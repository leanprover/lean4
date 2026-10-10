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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__27;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_isVoid(lean_object* v_e_85_){
_start:
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_87_ = l_Lean_Expr_isAppOf(v_e_85_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT void l_Lean_Expr_isVoid_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_85_ = stack[0].m_obj;
uint8_t v_res_88_;
v_res_88_ = l_Lean_Expr_isVoid(v_e_85_);
stack->m_num = v_res_88_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isVoid___boxed(lean_object* v_e_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_Lean_Expr_isVoid(v_e_89_);
lean_dec_ref(v_e_89_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
uint8_t l_Lean_Expr_isErased(lean_object* v_e_92_){
_start:
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2));
v___x_94_ = l_Lean_Expr_isAppOf(v_e_92_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT void l_Lean_Expr_isErased_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_92_ = stack[0].m_obj;
uint8_t v_res_95_;
v_res_95_ = l_Lean_Expr_isErased(v_e_92_);
stack->m_num = v_res_95_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isErased___boxed(lean_object* v_e_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Lean_Expr_isErased(v_e_96_);
lean_dec_ref(v_e_96_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
uint8_t l_Lean_Expr_isAny(lean_object* v_e_99_){
_start:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyExpr___closed__1));
v___x_101_ = l_Lean_Expr_isAppOf(v_e_99_, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT void l_Lean_Expr_isAny_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_99_ = stack[0].m_obj;
uint8_t v_res_102_;
v_res_102_ = l_Lean_Expr_isAny(v_e_99_);
stack->m_num = v_res_102_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAny___boxed(lean_object* v_e_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Lean_Expr_isAny(v_e_103_);
lean_dec_ref(v_e_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
uint8_t l_Lean_Compiler_LCNF_isPropFormerTypeQuick(lean_object* v_x_106_){
_start:
{
switch(lean_obj_tag(v_x_106_))
{
case 7:
{
lean_object* v_body_107_; 
v_body_107_ = lean_ctor_get(v_x_106_, 2);
v_x_106_ = v_body_107_;
goto _start;
}
case 3:
{
lean_object* v_u_109_; 
v_u_109_ = lean_ctor_get(v_x_106_, 0);
if (lean_obj_tag(v_u_109_) == 0)
{
uint8_t v___x_110_; 
v___x_110_ = 1;
return v___x_110_;
}
else
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
}
default: 
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isPropFormerTypeQuick_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_106_ = stack[0].m_obj;
uint8_t v_res_113_;
v_res_113_ = l_Lean_Compiler_LCNF_isPropFormerTypeQuick(v_x_106_);
stack->m_num = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerTypeQuick___boxed(lean_object* v_x_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Lean_Compiler_LCNF_isPropFormerTypeQuick(v_x_114_);
lean_dec_ref(v_x_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0(lean_object* v_k_117_, lean_object* v_b_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v___x_124_; 
lean_inc(v___y_122_);
lean_inc_ref(v___y_121_);
lean_inc(v___y_120_);
lean_inc_ref(v___y_119_);
v___x_124_ = lean_apply_6(v_k_117_, v_b_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, lean_box(0));
return v___x_124_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_117_ = stack[0].m_obj;
lean_object* v_b_118_ = stack[1].m_obj;
lean_object* v___y_119_ = stack[2].m_obj;
lean_object* v___y_120_ = stack[3].m_obj;
lean_object* v___y_121_ = stack[4].m_obj;
lean_object* v___y_122_ = stack[5].m_obj;
lean_object* v_res_125_;
v_res_125_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0(v_k_117_, v_b_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
stack->m_obj
 = v_res_125_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_126_, lean_object* v_b_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0(v_k_126_, v_b_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
return v_res_133_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(lean_object* v_name_134_, uint8_t v_bi_135_, lean_object* v_type_136_, lean_object* v_k_137_, uint8_t v_kind_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v___f_144_; lean_object* v___x_145_; 
v___f_144_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_144_, 0, v_k_137_);
v___x_145_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_134_, v_bi_135_, v_type_136_, v___f_144_, v_kind_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_a_154_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_145_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_145_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_134_ = stack[0].m_obj;
uint8_t v_bi_135_ = stack[1].m_num;
lean_object* v_type_136_ = stack[2].m_obj;
lean_object* v_k_137_ = stack[3].m_obj;
uint8_t v_kind_138_ = stack[4].m_num;
lean_object* v___y_139_ = stack[5].m_obj;
lean_object* v___y_140_ = stack[6].m_obj;
lean_object* v___y_141_ = stack[7].m_obj;
lean_object* v___y_142_ = stack[8].m_obj;
lean_object* v_res_162_;
v_res_162_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_name_134_, v_bi_135_, v_type_136_, v_k_137_, v_kind_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___boxed(lean_object* v_name_163_, lean_object* v_bi_164_, lean_object* v_type_165_, lean_object* v_k_166_, lean_object* v_kind_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
uint8_t v_bi_boxed_173_; uint8_t v_kind_boxed_174_; lean_object* v_res_175_; 
v_bi_boxed_173_ = lean_unbox(v_bi_164_);
v_kind_boxed_174_ = lean_unbox(v_kind_167_);
v_res_175_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_name_163_, v_bi_boxed_173_, v_type_165_, v_k_166_, v_kind_boxed_174_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v_res_175_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0(lean_object* v_00_u03b1_176_, lean_object* v_name_177_, uint8_t v_bi_178_, lean_object* v_type_179_, lean_object* v_k_180_, uint8_t v_kind_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_name_177_, v_bi_178_, v_type_179_, v_k_180_, v_kind_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
return v___x_187_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_177_ = stack[1].m_obj;
uint8_t v_bi_178_ = stack[2].m_num;
lean_object* v_type_179_ = stack[3].m_obj;
lean_object* v_k_180_ = stack[4].m_obj;
uint8_t v_kind_181_ = stack[5].m_num;
lean_object* v___y_182_ = stack[6].m_obj;
lean_object* v___y_183_ = stack[7].m_obj;
lean_object* v___y_184_ = stack[8].m_obj;
lean_object* v___y_185_ = stack[9].m_obj;
lean_object* v_res_188_;
v_res_188_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0(lean_box(0), v_name_177_, v_bi_178_, v_type_179_, v_k_180_, v_kind_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___boxed(lean_object* v_00_u03b1_189_, lean_object* v_name_190_, lean_object* v_bi_191_, lean_object* v_type_192_, lean_object* v_k_193_, lean_object* v_kind_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
uint8_t v_bi_boxed_200_; uint8_t v_kind_boxed_201_; lean_object* v_res_202_; 
v_bi_boxed_200_ = lean_unbox(v_bi_191_);
v_kind_boxed_201_ = lean_unbox(v_kind_194_);
v_res_202_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0(v_00_u03b1_189_, v_name_190_, v_bi_boxed_200_, v_type_192_, v_k_193_, v_kind_boxed_201_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed(lean_object* v_xs_205_, lean_object* v_body_206_, lean_object* v_x_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0(v_xs_205_, v_body_206_, v_x_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_213_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(lean_object* v_type_214_, lean_object* v_xs_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; 
switch(lean_obj_tag(v_type_214_))
{
case 3:
{
lean_object* v_u_248_; 
v_u_248_ = lean_ctor_get(v_type_214_, 0);
if (lean_obj_tag(v_u_248_) == 0)
{
lean_dec_ref_known(v_type_214_, 1);
lean_dec_ref(v_xs_215_);
goto v___jp_221_;
}
else
{
v___y_230_ = v_a_216_;
v___y_231_ = v_a_217_;
v___y_232_ = v_a_218_;
v___y_233_ = v_a_219_;
goto v___jp_229_;
}
}
case 7:
{
lean_object* v_binderName_249_; lean_object* v_binderType_250_; lean_object* v_body_251_; uint8_t v_binderInfo_252_; lean_object* v___f_253_; lean_object* v___x_254_; uint8_t v___x_255_; lean_object* v___x_256_; 
v_binderName_249_ = lean_ctor_get(v_type_214_, 0);
lean_inc(v_binderName_249_);
v_binderType_250_ = lean_ctor_get(v_type_214_, 1);
lean_inc_ref(v_binderType_250_);
v_body_251_ = lean_ctor_get(v_type_214_, 2);
lean_inc_ref(v_body_251_);
v_binderInfo_252_ = lean_ctor_get_uint8(v_type_214_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_214_, 3);
lean_inc_ref(v_xs_215_);
v___f_253_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_253_, 0, v_xs_215_);
lean_closure_set(v___f_253_, 1, v_body_251_);
v___x_254_ = lean_expr_instantiate_rev(v_binderType_250_, v_xs_215_);
lean_dec_ref(v_xs_215_);
lean_dec_ref(v_binderType_250_);
v___x_255_ = 0;
v___x_256_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_249_, v_binderInfo_252_, v___x_254_, v___f_253_, v___x_255_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
return v___x_256_;
}
default: 
{
v___y_230_ = v_a_216_;
v___y_231_ = v_a_217_;
v___y_232_ = v_a_218_;
v___y_233_ = v_a_219_;
goto v___jp_229_;
}
}
v___jp_221_:
{
uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = 1;
v___x_223_ = lean_box(v___x_222_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
v___jp_225_:
{
uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = 0;
v___x_227_ = lean_box(v___x_226_);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
v___jp_229_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_expr_instantiate_rev(v_type_214_, v_xs_215_);
lean_dec_ref(v_xs_215_);
lean_dec_ref(v_type_214_);
v___x_235_ = l_Lean_Meta_whnfD(v___x_234_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_235_, 1);
switch(lean_obj_tag(v_a_236_))
{
case 3:
{
lean_object* v_u_237_; 
v_u_237_ = lean_ctor_get(v_a_236_, 0);
lean_inc(v_u_237_);
lean_dec_ref_known(v_a_236_, 1);
if (lean_obj_tag(v_u_237_) == 0)
{
goto v___jp_221_;
}
else
{
lean_dec(v_u_237_);
goto v___jp_225_;
}
}
case 7:
{
lean_object* v___x_238_; 
v___x_238_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v_type_214_ = v_a_236_;
v_xs_215_ = v___x_238_;
v_a_216_ = v___y_230_;
v_a_217_ = v___y_231_;
v_a_218_ = v___y_232_;
v_a_219_ = v___y_233_;
goto _start;
}
default: 
{
lean_dec(v_a_236_);
goto v___jp_225_;
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
v_a_240_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_235_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_235_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_214_ = stack[0].m_obj;
lean_object* v_xs_215_ = stack[1].m_obj;
lean_object* v_a_216_ = stack[2].m_obj;
lean_object* v_a_217_ = stack[3].m_obj;
lean_object* v_a_218_ = stack[4].m_obj;
lean_object* v_a_219_ = stack[5].m_obj;
lean_object* v_res_257_;
v_res_257_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_type_214_, v_xs_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
stack->m_obj
 = v_res_257_;
}
lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0(lean_object* v_xs_258_, lean_object* v_body_259_, lean_object* v_x_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_array_push(v_xs_258_, v_x_260_);
v___x_267_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_body_259_, v___x_266_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
return v___x_267_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_258_ = stack[0].m_obj;
lean_object* v_body_259_ = stack[1].m_obj;
lean_object* v_x_260_ = stack[2].m_obj;
lean_object* v___y_261_ = stack[3].m_obj;
lean_object* v___y_262_ = stack[4].m_obj;
lean_object* v___y_263_ = stack[5].m_obj;
lean_object* v___y_264_ = stack[6].m_obj;
lean_object* v_res_268_;
v_res_268_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0(v_xs_258_, v_body_259_, v_x_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___boxed(lean_object* v_type_269_, lean_object* v_xs_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_type_269_, v_xs_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
return v_res_276_;
}
}
lean_object* l_Lean_Compiler_LCNF_isPropFormerType(lean_object* v_type_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = l_Lean_Compiler_LCNF_isPropFormerTypeQuick(v_type_277_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_285_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_type_277_, v___x_284_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
return v___x_285_;
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec_ref(v_type_277_);
v___x_286_ = lean_box(v___x_283_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isPropFormerType_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_277_ = stack[0].m_obj;
lean_object* v_a_278_ = stack[1].m_obj;
lean_object* v_a_279_ = stack[2].m_obj;
lean_object* v_a_280_ = stack[3].m_obj;
lean_object* v_a_281_ = stack[4].m_obj;
lean_object* v_res_288_;
v_res_288_ = l_Lean_Compiler_LCNF_isPropFormerType(v_type_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType___boxed(lean_object* v_type_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Compiler_LCNF_isPropFormerType(v_type_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
return v_res_295_;
}
}
lean_object* l_Lean_Compiler_LCNF_isPropFormer(lean_object* v_e_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_302_; 
lean_inc(v_a_300_);
lean_inc_ref(v_a_299_);
lean_inc(v_a_298_);
lean_inc_ref(v_a_297_);
v___x_302_ = lean_infer_type(v_e_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_304_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
lean_dec_ref_known(v___x_302_, 1);
v___x_304_ = l_Lean_Compiler_LCNF_isPropFormerType(v_a_303_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
return v___x_304_;
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
v_a_305_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_302_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_302_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isPropFormer_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_296_ = stack[0].m_obj;
lean_object* v_a_297_ = stack[1].m_obj;
lean_object* v_a_298_ = stack[2].m_obj;
lean_object* v_a_299_ = stack[3].m_obj;
lean_object* v_a_300_ = stack[4].m_obj;
lean_object* v_res_313_;
v_res_313_ = l_Lean_Compiler_LCNF_isPropFormer(v_e_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
stack->m_obj
 = v_res_313_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormer___boxed(lean_object* v_e_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Compiler_LCNF_isPropFormer(v_e_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
return v_res_320_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(lean_object* v_type_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___y_328_; lean_object* v___x_348_; uint8_t v_transparency_349_; uint8_t v___x_350_; uint8_t v___x_351_; 
v___x_348_ = l_Lean_Meta_Context_config(v_a_322_);
v_transparency_349_ = lean_ctor_get_uint8(v___x_348_, 9);
lean_dec_ref(v___x_348_);
v___x_350_ = 0;
v___x_351_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_349_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v_keyedConfig_352_; uint8_t v_trackZetaDelta_353_; lean_object* v_zetaDeltaSet_354_; lean_object* v_lctx_355_; lean_object* v_localInstances_356_; lean_object* v_defEqCtx_x3f_357_; lean_object* v_synthPendingDepth_358_; lean_object* v_customCanUnfoldPredicate_x3f_359_; uint8_t v_univApprox_360_; uint8_t v_inTypeClassResolution_361_; uint8_t v_cacheInferType_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_keyedConfig_352_ = lean_ctor_get(v_a_322_, 0);
v_trackZetaDelta_353_ = lean_ctor_get_uint8(v_a_322_, sizeof(void*)*7);
v_zetaDeltaSet_354_ = lean_ctor_get(v_a_322_, 1);
v_lctx_355_ = lean_ctor_get(v_a_322_, 2);
v_localInstances_356_ = lean_ctor_get(v_a_322_, 3);
v_defEqCtx_x3f_357_ = lean_ctor_get(v_a_322_, 4);
v_synthPendingDepth_358_ = lean_ctor_get(v_a_322_, 5);
v_customCanUnfoldPredicate_x3f_359_ = lean_ctor_get(v_a_322_, 6);
v_univApprox_360_ = lean_ctor_get_uint8(v_a_322_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_361_ = lean_ctor_get_uint8(v_a_322_, sizeof(void*)*7 + 2);
v_cacheInferType_362_ = lean_ctor_get_uint8(v_a_322_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_352_);
v___x_363_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_350_, v_keyedConfig_352_);
lean_inc(v_customCanUnfoldPredicate_x3f_359_);
lean_inc(v_synthPendingDepth_358_);
lean_inc(v_defEqCtx_x3f_357_);
lean_inc_ref(v_localInstances_356_);
lean_inc_ref(v_lctx_355_);
lean_inc(v_zetaDeltaSet_354_);
v___x_364_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_zetaDeltaSet_354_);
lean_ctor_set(v___x_364_, 2, v_lctx_355_);
lean_ctor_set(v___x_364_, 3, v_localInstances_356_);
lean_ctor_set(v___x_364_, 4, v_defEqCtx_x3f_357_);
lean_ctor_set(v___x_364_, 5, v_synthPendingDepth_358_);
lean_ctor_set(v___x_364_, 6, v_customCanUnfoldPredicate_x3f_359_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*7, v_trackZetaDelta_353_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*7 + 1, v_univApprox_360_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*7 + 2, v_inTypeClassResolution_361_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*7 + 3, v_cacheInferType_362_);
lean_inc(v_a_325_);
lean_inc_ref(v_a_324_);
lean_inc(v_a_323_);
v___x_365_ = lean_whnf(v_type_321_, v___x_364_, v_a_323_, v_a_324_, v_a_325_);
v___y_328_ = v___x_365_;
goto v___jp_327_;
}
else
{
lean_object* v___x_366_; 
lean_inc(v_a_325_);
lean_inc_ref(v_a_324_);
lean_inc(v_a_323_);
lean_inc_ref(v_a_322_);
v___x_366_ = lean_whnf(v_type_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
v___y_328_ = v___x_366_;
goto v___jp_327_;
}
v___jp_327_:
{
if (lean_obj_tag(v___y_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_339_; 
v_a_329_ = lean_ctor_get(v___y_328_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___y_328_);
if (v_isSharedCheck_339_ == 0)
{
v___x_331_ = v___y_328_;
v_isShared_332_ = v_isSharedCheck_339_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___y_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_339_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
lean_inc(v_a_329_);
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
lean_inc(v_a_329_);
v___x_335_ = l_Lean_Expr_eta(v_a_329_);
v___x_336_ = lean_expr_eqv(v___x_335_, v_a_329_);
lean_dec(v_a_329_);
if (v___x_336_ == 0)
{
lean_dec_ref(v___x_334_);
v_type_321_ = v___x_335_;
goto _start;
}
else
{
lean_dec_ref(v___x_335_);
return v___x_334_;
}
}
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_a_340_ = lean_ctor_get(v___y_328_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___y_328_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___y_328_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___y_328_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_321_ = stack[0].m_obj;
lean_object* v_a_322_ = stack[1].m_obj;
lean_object* v_a_323_ = stack[2].m_obj;
lean_object* v_a_324_ = stack[3].m_obj;
lean_object* v_a_325_ = stack[4].m_obj;
lean_object* v_res_367_;
v_res_367_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(v_type_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
stack->m_obj
 = v_res_367_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___boxed(lean_object* v_type_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(v_type_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
return v_res_374_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(lean_object* v_msgData_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; lean_object* v_env_382_; uint8_t v___x_383_; lean_object* v_env_384_; lean_object* v___x_385_; lean_object* v_toCold_386_; lean_object* v_mctx_387_; lean_object* v_lctx_388_; lean_object* v_options_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_381_ = lean_st_ref_get(v___y_379_);
v_env_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc_ref(v_env_382_);
lean_dec(v___x_381_);
v___x_383_ = 0;
v_env_384_ = l_Lean_Environment_setRecordingDeps(v_env_382_, v___x_383_);
v___x_385_ = lean_st_ref_get(v___y_377_);
v_toCold_386_ = lean_ctor_get(v___y_378_, 0);
v_mctx_387_ = lean_ctor_get(v___x_385_, 0);
lean_inc_ref(v_mctx_387_);
lean_dec(v___x_385_);
v_lctx_388_ = lean_ctor_get(v___y_376_, 2);
v_options_389_ = lean_ctor_get(v_toCold_386_, 2);
lean_inc_ref(v_options_389_);
lean_inc_ref(v_lctx_388_);
v___x_390_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_390_, 0, v_env_384_);
lean_ctor_set(v___x_390_, 1, v_mctx_387_);
lean_ctor_set(v___x_390_, 2, v_lctx_388_);
lean_ctor_set(v___x_390_, 3, v_options_389_);
v___x_391_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v_msgData_375_);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_375_ = stack[0].m_obj;
lean_object* v___y_376_ = stack[1].m_obj;
lean_object* v___y_377_ = stack[2].m_obj;
lean_object* v___y_378_ = stack[3].m_obj;
lean_object* v___y_379_ = stack[4].m_obj;
lean_object* v_res_393_;
v_res_393_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(v_msgData_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
stack->m_obj
 = v_res_393_;
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
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(lean_object* v_msg_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_ref_407_; lean_object* v___x_408_; lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_417_; 
v_ref_407_ = lean_ctor_get(v___y_404_, 2);
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
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_401_ = stack[0].m_obj;
lean_object* v___y_402_ = stack[1].m_obj;
lean_object* v___y_403_ = stack[2].m_obj;
lean_object* v___y_404_ = stack[3].m_obj;
lean_object* v___y_405_ = stack[4].m_obj;
lean_object* v_res_418_;
v_res_418_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
stack->m_obj
 = v_res_418_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg___boxed(lean_object* v_msg_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_425_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(lean_object* v_ref_426_, lean_object* v_msg_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_toCold_433_; lean_object* v_currRecDepth_434_; lean_object* v_ref_435_; uint16_t v_optionFlags_436_; uint8_t v_suppressElabErrors_437_; uint8_t v_isRecordingDeps_438_; lean_object* v_ref_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_toCold_433_ = lean_ctor_get(v___y_430_, 0);
v_currRecDepth_434_ = lean_ctor_get(v___y_430_, 1);
v_ref_435_ = lean_ctor_get(v___y_430_, 2);
v_optionFlags_436_ = lean_ctor_get_uint16(v___y_430_, sizeof(void*)*3);
v_suppressElabErrors_437_ = lean_ctor_get_uint8(v___y_430_, sizeof(void*)*3 + 2);
v_isRecordingDeps_438_ = lean_ctor_get_uint8(v___y_430_, sizeof(void*)*3 + 3);
v_ref_439_ = l_Lean_replaceRef(v_ref_426_, v_ref_435_);
lean_inc(v_currRecDepth_434_);
lean_inc_ref(v_toCold_433_);
v___x_440_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_440_, 0, v_toCold_433_);
lean_ctor_set(v___x_440_, 1, v_currRecDepth_434_);
lean_ctor_set(v___x_440_, 2, v_ref_439_);
lean_ctor_set_uint16(v___x_440_, sizeof(void*)*3, v_optionFlags_436_);
lean_ctor_set_uint8(v___x_440_, sizeof(void*)*3 + 2, v_suppressElabErrors_437_);
lean_ctor_set_uint8(v___x_440_, sizeof(void*)*3 + 3, v_isRecordingDeps_438_);
v___x_441_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_427_, v___y_428_, v___y_429_, v___x_440_, v___y_431_);
lean_dec_ref_known(v___x_440_, 3);
return v___x_441_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_426_ = stack[0].m_obj;
lean_object* v_msg_427_ = stack[1].m_obj;
lean_object* v___y_428_ = stack[2].m_obj;
lean_object* v___y_429_ = stack[3].m_obj;
lean_object* v___y_430_ = stack[4].m_obj;
lean_object* v___y_431_ = stack[5].m_obj;
lean_object* v_res_442_;
v_res_442_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_426_, v_msg_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg___boxed(lean_object* v_ref_443_, lean_object* v_msg_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_443_, v_msg_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v_ref_443_);
return v_res_450_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_451_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_455_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
lean_ctor_set(v___x_457_, 2, v___x_456_);
lean_ctor_set(v___x_457_, 3, v___x_456_);
lean_ctor_set(v___x_457_, 4, v___x_455_);
lean_ctor_set(v___x_457_, 5, v___x_455_);
lean_ctor_set(v___x_457_, 6, v___x_455_);
lean_ctor_set(v___x_457_, 7, v___x_455_);
lean_ctor_set(v___x_457_, 8, v___x_455_);
lean_ctor_set(v___x_457_, 9, v___x_455_);
lean_ctor_set(v___x_457_, 10, v___x_455_);
lean_ctor_set(v___x_457_, 11, v___x_454_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_unsigned_to_nat(32u);
v___x_459_ = lean_mk_empty_array_with_capacity(v___x_458_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_461_ = ((size_t)5ULL);
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_unsigned_to_nat(32u);
v___x_464_ = lean_mk_empty_array_with_capacity(v___x_463_);
v___x_465_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_466_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v___x_464_);
lean_ctor_set(v___x_466_, 2, v___x_462_);
lean_ctor_set(v___x_466_, 3, v___x_462_);
lean_ctor_set_usize(v___x_466_, 4, v___x_461_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_467_ = lean_box(1);
v___x_468_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_469_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
lean_ctor_set(v___x_470_, 2, v___x_467_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_473_ = l_Lean_stringToMessageData(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_476_ = l_Lean_stringToMessageData(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_479_ = l_Lean_stringToMessageData(v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_491_ = l_Lean_stringToMessageData(v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__21(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__20));
v___x_494_ = l_Lean_stringToMessageData(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__23(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__22));
v___x_497_ = l_Lean_stringToMessageData(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__25(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__24));
v___x_500_ = l_Lean_stringToMessageData(v___x_499_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__27(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__26));
v___x_503_ = l_Lean_stringToMessageData(v___x_502_);
return v___x_503_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_504_, lean_object* v_declHint_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v_env_510_; uint8_t v___x_511_; 
v___x_508_ = lean_box(0);
v___x_509_ = lean_st_ref_get(v___y_506_);
v_env_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc_ref(v_env_510_);
lean_dec(v___x_509_);
v___x_511_ = l_Lean_Name_isAnonymous(v_declHint_505_);
if (v___x_511_ == 0)
{
uint8_t v_isExporting_512_; 
v_isExporting_512_ = lean_ctor_get_uint8(v_env_510_, sizeof(void*)*13);
if (v_isExporting_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec_ref(v_env_510_);
lean_dec(v_declHint_505_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v_msg_504_);
return v___x_513_;
}
else
{
lean_object* v___x_514_; uint8_t v___x_515_; 
lean_inc_ref(v_env_510_);
v___x_514_ = l_Lean_Environment_setExporting(v_env_510_, v___x_511_);
lean_inc(v_declHint_505_);
lean_inc_ref(v___x_514_);
v___x_515_ = l_Lean_Environment_contains(v___x_514_, v_declHint_505_, v_isExporting_512_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
lean_dec_ref(v___x_514_);
lean_dec_ref(v_env_510_);
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
v___x_521_ = l_Lean_MessageData_ofConstName(v_declHint_505_, v___x_511_);
v_c_522_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_522_, 0, v___x_520_);
lean_ctor_set(v_c_522_, 1, v___x_521_);
v___x_523_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_510_, v_declHint_505_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec_ref(v_env_510_);
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
lean_object* v_val_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_587_; 
v_val_531_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_587_ == 0)
{
v___x_533_ = v___x_523_;
v_isShared_534_ = v_isSharedCheck_587_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_val_531_);
lean_dec(v___x_523_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_587_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v_modules_536_; lean_object* v_moduleNames_537_; lean_object* v_mod_538_; uint8_t v___y_540_; uint8_t v___x_570_; 
v___x_535_ = l_Lean_Environment_header(v_env_510_);
lean_dec_ref(v_env_510_);
v_modules_536_ = lean_ctor_get(v___x_535_, 3);
lean_inc_ref(v_modules_536_);
v_moduleNames_537_ = lean_ctor_get(v___x_535_, 4);
lean_inc_ref(v_moduleNames_537_);
lean_dec_ref(v___x_535_);
v_mod_538_ = lean_array_get(v___x_508_, v_moduleNames_537_, v_val_531_);
lean_dec_ref(v_moduleNames_537_);
v___x_570_ = l_Lean_isPrivateName(v_declHint_505_);
lean_dec(v_declHint_505_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_array_get_size(v_modules_536_);
v___x_572_ = lean_nat_dec_lt(v_val_531_, v___x_571_);
if (v___x_572_ == 0)
{
lean_dec_ref(v_modules_536_);
lean_dec(v_val_531_);
v___y_540_ = v___x_570_;
goto v___jp_539_;
}
else
{
lean_object* v___x_573_; lean_object* v_toImport_574_; uint8_t v_isExported_575_; 
v___x_573_ = lean_array_fget(v_modules_536_, v_val_531_);
lean_dec(v_val_531_);
lean_dec_ref(v_modules_536_);
v_toImport_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc_ref(v_toImport_574_);
lean_dec(v___x_573_);
v_isExported_575_ = lean_ctor_get_uint8(v_toImport_574_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_574_);
v___y_540_ = v_isExported_575_;
goto v___jp_539_;
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec_ref(v_modules_536_);
lean_del_object(v___x_533_);
lean_dec(v_val_531_);
v___x_576_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_c_522_);
v___x_578_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__25);
v___x_579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = l_Lean_MessageData_ofName(v_mod_538_);
v___x_581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__27);
v___x_583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = l_Lean_MessageData_note(v___x_583_);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v_msg_504_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
v___jp_539_:
{
if (v___y_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_541_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v_c_522_);
v___x_543_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = l_Lean_MessageData_ofName(v_mod_538_);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = l_Lean_MessageData_note(v___x_548_);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v_msg_504_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
if (v_isShared_534_ == 0)
{
lean_ctor_set_tag(v___x_533_, 0);
lean_ctor_set(v___x_533_, 0, v___x_550_);
v___x_552_ = v___x_533_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_554_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v_c_522_);
v___x_556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = l_Lean_MessageData_ofName(v_mod_538_);
lean_inc_ref(v___x_558_);
v___x_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__21);
v___x_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___x_558_);
v___x_563_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__23);
v___x_564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = l_Lean_MessageData_note(v___x_564_);
v___x_566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_566_, 0, v_msg_504_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
if (v_isShared_534_ == 0)
{
lean_ctor_set_tag(v___x_533_, 0);
lean_ctor_set(v___x_533_, 0, v___x_566_);
v___x_568_ = v___x_533_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
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
lean_object* v___x_588_; 
lean_dec_ref(v_env_510_);
lean_dec(v_declHint_505_);
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v_msg_504_);
return v___x_588_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_504_ = stack[0].m_obj;
lean_object* v_declHint_505_ = stack[1].m_obj;
lean_object* v___y_506_ = stack[2].m_obj;
lean_object* v_res_589_;
v_res_589_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_504_, v_declHint_505_, v___y_506_);
stack->m_obj
 = v_res_589_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_590_, lean_object* v_declHint_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_590_, v_declHint_591_, v___y_592_);
lean_dec(v___y_592_);
return v_res_594_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(lean_object* v_msg_595_, lean_object* v_declHint_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v___x_602_; lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_612_; 
v___x_602_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_595_, v_declHint_596_, v___y_600_);
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_612_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_612_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_612_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_607_ = l_Lean_unknownIdentifierMessageTag;
v___x_608_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v_a_603_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_608_);
v___x_610_ = v___x_605_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_595_ = stack[0].m_obj;
lean_object* v_declHint_596_ = stack[1].m_obj;
lean_object* v___y_597_ = stack[2].m_obj;
lean_object* v___y_598_ = stack[3].m_obj;
lean_object* v___y_599_ = stack[4].m_obj;
lean_object* v___y_600_ = stack[5].m_obj;
lean_object* v_res_613_;
v_res_613_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_595_, v_declHint_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9___boxed(lean_object* v_msg_614_, lean_object* v_declHint_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_614_, v_declHint_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(lean_object* v_ref_622_, lean_object* v_msg_623_, lean_object* v_declHint_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_630_; lean_object* v_a_631_; lean_object* v___x_632_; 
v___x_630_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_623_, v_declHint_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref(v___x_630_);
v___x_632_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_622_, v_a_631_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
return v___x_632_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_622_ = stack[0].m_obj;
lean_object* v_msg_623_ = stack[1].m_obj;
lean_object* v_declHint_624_ = stack[2].m_obj;
lean_object* v___y_625_ = stack[3].m_obj;
lean_object* v___y_626_ = stack[4].m_obj;
lean_object* v___y_627_ = stack[5].m_obj;
lean_object* v___y_628_ = stack[6].m_obj;
lean_object* v_res_633_;
v_res_633_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_622_, v_msg_623_, v_declHint_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_ref_634_, lean_object* v_msg_635_, lean_object* v_declHint_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_634_, v_msg_635_, v_declHint_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v_ref_634_);
return v_res_642_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__0));
v___x_645_ = l_Lean_stringToMessageData(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__2));
v___x_648_ = l_Lean_stringToMessageData(v___x_647_);
return v___x_648_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(lean_object* v_ref_649_, lean_object* v_constName_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; uint8_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_656_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1);
v___x_657_ = 0;
lean_inc(v_constName_650_);
v___x_658_ = l_Lean_MessageData_ofConstName(v_constName_650_, v___x_657_);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_656_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_649_, v___x_661_, v_constName_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
return v___x_662_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_649_ = stack[0].m_obj;
lean_object* v_constName_650_ = stack[1].m_obj;
lean_object* v___y_651_ = stack[2].m_obj;
lean_object* v___y_652_ = stack[3].m_obj;
lean_object* v___y_653_ = stack[4].m_obj;
lean_object* v___y_654_ = stack[5].m_obj;
lean_object* v_res_663_;
v_res_663_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_649_, v_constName_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
stack->m_obj
 = v_res_663_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___boxed(lean_object* v_ref_664_, lean_object* v_constName_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_664_, v_constName_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v_ref_664_);
return v_res_671_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(lean_object* v_constName_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_ref_678_; lean_object* v___x_679_; 
v_ref_678_ = lean_ctor_get(v___y_675_, 2);
v___x_679_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_678_, v_constName_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
return v___x_679_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_672_ = stack[0].m_obj;
lean_object* v___y_673_ = stack[1].m_obj;
lean_object* v___y_674_ = stack[2].m_obj;
lean_object* v___y_675_ = stack[3].m_obj;
lean_object* v___y_676_ = stack[4].m_obj;
lean_object* v_res_680_;
v_res_680_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
stack->m_obj
 = v_res_680_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg___boxed(lean_object* v_constName_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_687_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(lean_object* v_constName_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; lean_object* v_env_695_; uint8_t v___x_696_; lean_object* v___x_697_; 
v___x_694_ = lean_st_ref_get(v___y_692_);
v_env_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc_ref(v_env_695_);
lean_dec(v___x_694_);
v___x_696_ = 0;
lean_inc(v_constName_688_);
v___x_697_ = l_Lean_Environment_find_x3f(v_env_695_, v_constName_688_, v___x_696_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
return v___x_698_;
}
else
{
lean_object* v_val_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec(v_constName_688_);
v_val_699_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_697_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_val_699_);
lean_dec(v___x_697_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set_tag(v___x_701_, 0);
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_val_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_688_ = stack[0].m_obj;
lean_object* v___y_689_ = stack[1].m_obj;
lean_object* v___y_690_ = stack[2].m_obj;
lean_object* v___y_691_ = stack[3].m_obj;
lean_object* v___y_692_ = stack[4].m_obj;
lean_object* v_res_707_;
v_res_707_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_constName_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
stack->m_obj
 = v_res_707_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4___boxed(lean_object* v_constName_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_constName_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_714_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(lean_object* v_binderType_715_, lean_object* v_body_716_, lean_object* v_binderName_717_, uint8_t v_binderInfo_718_, lean_object* v_x_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_binderType_715_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = lean_expr_instantiate1(v_body_716_, v_x_719_);
v___x_728_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v___x_727_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; uint8_t v___x_730_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v___x_730_ = l_Lean_Expr_isErased(v_a_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_742_; 
lean_inc(v_a_729_);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v___x_728_, 0);
lean_dec(v_unused_743_);
v___x_732_ = v___x_728_;
v_isShared_733_ = v_isSharedCheck_742_;
goto v_resetjp_731_;
}
else
{
lean_dec(v___x_728_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_742_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_734_ = lean_unsigned_to_nat(1u);
v___x_735_ = lean_mk_empty_array_with_capacity(v___x_734_);
v___x_736_ = lean_array_push(v___x_735_, v_x_719_);
v___x_737_ = lean_expr_abstract(v_a_729_, v___x_736_);
lean_dec_ref(v___x_736_);
lean_dec(v_a_729_);
v___x_738_ = l_Lean_Expr_lam___override(v_binderName_717_, v_a_726_, v___x_737_, v_binderInfo_718_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_738_);
v___x_740_ = v___x_732_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
else
{
lean_dec(v_a_726_);
lean_dec_ref(v_x_719_);
lean_dec(v_binderName_717_);
return v___x_728_;
}
}
else
{
lean_dec(v_a_726_);
lean_dec_ref(v_x_719_);
lean_dec(v_binderName_717_);
return v___x_728_;
}
}
else
{
lean_dec_ref(v_x_719_);
lean_dec(v_binderName_717_);
return v___x_725_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_715_ = stack[0].m_obj;
lean_object* v_body_716_ = stack[1].m_obj;
lean_object* v_binderName_717_ = stack[2].m_obj;
uint8_t v_binderInfo_718_ = stack[3].m_num;
lean_object* v_x_719_ = stack[4].m_obj;
lean_object* v___y_720_ = stack[5].m_obj;
lean_object* v___y_721_ = stack[6].m_obj;
lean_object* v___y_722_ = stack[7].m_obj;
lean_object* v___y_723_ = stack[8].m_obj;
lean_object* v_res_744_;
v_res_744_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(v_binderType_715_, v_body_716_, v_binderName_717_, v_binderInfo_718_, v_x_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
stack->m_obj
 = v_res_744_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed(lean_object* v_binderType_745_, lean_object* v_body_746_, lean_object* v_binderName_747_, lean_object* v_binderInfo_748_, lean_object* v_x_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
uint8_t v_binderInfo_9260__boxed_755_; lean_object* v_res_756_; 
v_binderInfo_9260__boxed_755_ = lean_unbox(v_binderInfo_748_);
v_res_756_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(v_binderType_745_, v_body_746_, v_binderName_747_, v_binderInfo_9260__boxed_755_, v_x_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec_ref(v_body_746_);
return v_res_756_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(lean_object* v_xs_757_, lean_object* v_body_758_, lean_object* v_binderName_759_, uint8_t v_binderInfo_760_, lean_object* v_d_761_, lean_object* v_x_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_d_769_; uint8_t v_isBorrowed_781_; lean_object* v___x_782_; 
v_isBorrowed_781_ = l_Lean_isMarkedBorrowed(v_d_761_);
v___x_782_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_d_761_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_784_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_782_, 1);
v___x_784_ = lean_expr_abstract(v_a_783_, v_xs_757_);
lean_dec(v_a_783_);
if (v_isBorrowed_781_ == 0)
{
v_d_769_ = v___x_784_;
goto v___jp_768_;
}
else
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_markBorrowed(v___x_784_);
v_d_769_ = v___x_785_;
goto v___jp_768_;
}
}
else
{
lean_dec_ref(v_x_762_);
lean_dec(v_binderName_759_);
lean_dec_ref(v_body_758_);
lean_dec_ref(v_xs_757_);
return v___x_782_;
}
v___jp_768_:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_array_push(v_xs_757_, v_x_762_);
v___x_771_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_body_758_, v___x_770_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_780_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_780_ == 0)
{
v___x_774_ = v___x_771_;
v_isShared_775_ = v_isSharedCheck_780_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_780_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = l_Lean_Expr_forallE___override(v_binderName_759_, v_d_769_, v_a_772_, v_binderInfo_760_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_776_);
v___x_778_ = v___x_774_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
else
{
lean_dec_ref(v_d_769_);
lean_dec(v_binderName_759_);
return v___x_771_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_757_ = stack[0].m_obj;
lean_object* v_body_758_ = stack[1].m_obj;
lean_object* v_binderName_759_ = stack[2].m_obj;
uint8_t v_binderInfo_760_ = stack[3].m_num;
lean_object* v_d_761_ = stack[4].m_obj;
lean_object* v_x_762_ = stack[5].m_obj;
lean_object* v___y_763_ = stack[6].m_obj;
lean_object* v___y_764_ = stack[7].m_obj;
lean_object* v___y_765_ = stack[8].m_obj;
lean_object* v___y_766_ = stack[9].m_obj;
lean_object* v_res_786_;
v_res_786_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(v_xs_757_, v_body_758_, v_binderName_759_, v_binderInfo_760_, v_d_761_, v_x_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed(lean_object* v_xs_787_, lean_object* v_body_788_, lean_object* v_binderName_789_, lean_object* v_binderInfo_790_, lean_object* v_d_791_, lean_object* v_x_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
uint8_t v_binderInfo_9282__boxed_798_; lean_object* v_res_799_; 
v_binderInfo_9282__boxed_798_ = lean_unbox(v_binderInfo_790_);
v_res_799_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(v_xs_787_, v_body_788_, v_binderName_789_, v_binderInfo_9282__boxed_798_, v_d_791_, v_x_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
return v_res_799_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(lean_object* v_e_800_, lean_object* v_xs_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
if (lean_obj_tag(v_e_800_) == 7)
{
lean_object* v_binderName_807_; lean_object* v_binderType_808_; lean_object* v_body_809_; uint8_t v_binderInfo_810_; lean_object* v_d_811_; lean_object* v___x_812_; lean_object* v___f_813_; uint8_t v___x_814_; lean_object* v___x_815_; 
v_binderName_807_ = lean_ctor_get(v_e_800_, 0);
lean_inc_n(v_binderName_807_, 2);
v_binderType_808_ = lean_ctor_get(v_e_800_, 1);
lean_inc_ref(v_binderType_808_);
v_body_809_ = lean_ctor_get(v_e_800_, 2);
lean_inc_ref(v_body_809_);
v_binderInfo_810_ = lean_ctor_get_uint8(v_e_800_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_800_, 3);
v_d_811_ = lean_expr_instantiate_rev(v_binderType_808_, v_xs_801_);
lean_dec_ref(v_binderType_808_);
v___x_812_ = lean_box(v_binderInfo_810_);
lean_inc_ref(v_d_811_);
v___f_813_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed), 11, 5);
lean_closure_set(v___f_813_, 0, v_xs_801_);
lean_closure_set(v___f_813_, 1, v_body_809_);
lean_closure_set(v___f_813_, 2, v_binderName_807_);
lean_closure_set(v___f_813_, 3, v___x_812_);
lean_closure_set(v___f_813_, 4, v_d_811_);
v___x_814_ = 0;
v___x_815_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_807_, v_binderInfo_810_, v_d_811_, v___f_813_, v___x_814_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
return v___x_815_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_expr_instantiate_rev(v_e_800_, v_xs_801_);
lean_dec_ref(v_e_800_);
v___x_817_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v___x_816_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_826_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_826_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_expr_abstract(v_a_818_, v_xs_801_);
lean_dec_ref(v_xs_801_);
lean_dec(v_a_818_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_822_);
v___x_824_ = v___x_820_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
else
{
lean_dec_ref(v_xs_801_);
return v___x_817_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_800_ = stack[0].m_obj;
lean_object* v_xs_801_ = stack[1].m_obj;
lean_object* v_a_802_ = stack[2].m_obj;
lean_object* v_a_803_ = stack[3].m_obj;
lean_object* v_a_804_ = stack[4].m_obj;
lean_object* v_a_805_ = stack[5].m_obj;
lean_object* v_res_827_;
v_res_827_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_e_800_, v_xs_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
stack->m_obj
 = v_res_827_;
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0(void){
_start:
{
lean_object* v___x_828_; lean_object* v_dummy_829_; 
v___x_828_ = lean_box(0);
v_dummy_829_ = l_Lean_Expr_sort___override(v___x_828_);
return v_dummy_829_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(lean_object* v_type_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v___x_842_; 
lean_inc_ref(v_type_833_);
v___x_842_ = l_Lean_Meta_isProp(v_type_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_904_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_904_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_904_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_904_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
uint8_t v___x_847_; 
v___x_847_ = lean_unbox(v_a_843_);
lean_dec(v_a_843_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
lean_del_object(v___x_845_);
v___x_848_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(v_type_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
switch(lean_obj_tag(v_a_849_))
{
case 3:
{
return v___x_848_;
}
case 4:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
lean_inc_ref(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v___x_850_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_851_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_a_849_, v___x_850_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
return v___x_851_;
}
case 6:
{
lean_object* v_binderName_852_; lean_object* v_binderType_853_; lean_object* v_body_854_; uint8_t v_binderInfo_855_; lean_object* v___x_856_; lean_object* v___f_857_; uint8_t v___x_858_; lean_object* v___x_859_; 
lean_inc_ref(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v_binderName_852_ = lean_ctor_get(v_a_849_, 0);
lean_inc_n(v_binderName_852_, 2);
v_binderType_853_ = lean_ctor_get(v_a_849_, 1);
lean_inc_ref_n(v_binderType_853_, 2);
v_body_854_ = lean_ctor_get(v_a_849_, 2);
lean_inc_ref(v_body_854_);
v_binderInfo_855_ = lean_ctor_get_uint8(v_a_849_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_849_, 3);
v___x_856_ = lean_box(v_binderInfo_855_);
v___f_857_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_857_, 0, v_binderType_853_);
lean_closure_set(v___f_857_, 1, v_body_854_);
lean_closure_set(v___f_857_, 2, v_binderName_852_);
lean_closure_set(v___f_857_, 3, v___x_856_);
v___x_858_ = 0;
v___x_859_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_852_, v_binderInfo_855_, v_binderType_853_, v___f_857_, v___x_858_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
return v___x_859_;
}
case 7:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_inc_ref(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v___x_860_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_861_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_a_849_, v___x_860_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
return v___x_861_;
}
case 5:
{
lean_object* v_dummy_862_; lean_object* v_nargs_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
lean_inc_ref(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v_dummy_862_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0);
v_nargs_863_ = l_Lean_Expr_getAppNumArgs(v_a_849_);
lean_inc(v_nargs_863_);
v___x_864_ = lean_mk_array(v_nargs_863_, v_dummy_862_);
v___x_865_ = lean_unsigned_to_nat(1u);
v___x_866_ = lean_nat_sub(v_nargs_863_, v___x_865_);
lean_dec(v_nargs_863_);
v___x_867_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_a_849_, v___x_864_, v___x_866_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
return v___x_867_;
}
case 1:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_inc_ref(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v___x_868_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_869_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_a_849_, v___x_868_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
return v___x_869_;
}
case 11:
{
lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_898_; 
lean_inc_ref(v_a_849_);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v___x_848_, 0);
lean_dec(v_unused_899_);
v___x_871_ = v___x_848_;
v_isShared_872_ = v_isSharedCheck_898_;
goto v_resetjp_870_;
}
else
{
lean_dec(v___x_848_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_898_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_typeName_873_; 
v_typeName_873_ = lean_ctor_get(v_a_849_, 0);
lean_inc(v_typeName_873_);
if (lean_obj_tag(v_typeName_873_) == 1)
{
lean_object* v_pre_874_; 
v_pre_874_ = lean_ctor_get(v_typeName_873_, 0);
if (lean_obj_tag(v_pre_874_) == 0)
{
lean_object* v_idx_875_; lean_object* v_struct_876_; lean_object* v_str_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v_idx_875_ = lean_ctor_get(v_a_849_, 1);
lean_inc(v_idx_875_);
v_struct_876_ = lean_ctor_get(v_a_849_, 2);
lean_inc_ref(v_struct_876_);
lean_dec_ref_known(v_a_849_, 3);
v_str_877_ = lean_ctor_get(v_typeName_873_, 1);
lean_inc_ref(v_str_877_);
lean_dec_ref_known(v_typeName_873_, 2);
v___x_878_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__1));
v___x_879_ = lean_string_dec_eq(v_str_877_, v___x_878_);
lean_dec_ref(v_str_877_);
if (v___x_879_ == 0)
{
lean_dec_ref(v_struct_876_);
lean_dec(v_idx_875_);
lean_del_object(v___x_871_);
goto v___jp_839_;
}
else
{
lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = lean_nat_dec_eq(v_idx_875_, v___x_880_);
lean_dec(v_idx_875_);
if (v___x_881_ == 0)
{
lean_dec_ref(v_struct_876_);
lean_del_object(v___x_871_);
goto v___jp_839_;
}
else
{
if (lean_obj_tag(v_struct_876_) == 5)
{
lean_object* v_fn_882_; 
v_fn_882_ = lean_ctor_get(v_struct_876_, 0);
lean_inc_ref(v_fn_882_);
lean_dec_ref_known(v_struct_876_, 2);
if (lean_obj_tag(v_fn_882_) == 4)
{
lean_object* v_declName_883_; 
v_declName_883_ = lean_ctor_get(v_fn_882_, 0);
lean_inc(v_declName_883_);
if (lean_obj_tag(v_declName_883_) == 1)
{
lean_object* v_pre_884_; 
v_pre_884_ = lean_ctor_get(v_declName_883_, 0);
lean_inc(v_pre_884_);
if (lean_obj_tag(v_pre_884_) == 1)
{
lean_object* v_pre_885_; 
v_pre_885_ = lean_ctor_get(v_pre_884_, 0);
if (lean_obj_tag(v_pre_885_) == 0)
{
lean_object* v_us_886_; lean_object* v_str_887_; lean_object* v_str_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v_us_886_ = lean_ctor_get(v_fn_882_, 1);
lean_inc(v_us_886_);
lean_dec_ref_known(v_fn_882_, 2);
v_str_887_ = lean_ctor_get(v_declName_883_, 1);
lean_inc_ref(v_str_887_);
lean_dec_ref_known(v_declName_883_, 2);
v_str_888_ = lean_ctor_get(v_pre_884_, 1);
lean_inc_ref(v_str_888_);
lean_dec_ref_known(v_pre_884_, 2);
v___x_889_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__2));
v___x_890_ = lean_string_dec_eq(v_str_888_, v___x_889_);
lean_dec_ref(v_str_888_);
if (v___x_890_ == 0)
{
lean_dec_ref(v_str_887_);
lean_dec(v_us_886_);
lean_del_object(v___x_871_);
goto v___jp_839_;
}
else
{
lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_891_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__3));
v___x_892_ = lean_string_dec_eq(v_str_887_, v___x_891_);
lean_dec_ref(v_str_887_);
if (v___x_892_ == 0)
{
lean_dec(v_us_886_);
lean_del_object(v___x_871_);
goto v___jp_839_;
}
else
{
if (lean_obj_tag(v_us_886_) == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_893_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_894_ = l_Lean_mkConst(v___x_893_, v_us_886_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_894_);
v___x_896_ = v___x_871_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
else
{
lean_dec(v_us_886_);
lean_del_object(v___x_871_);
goto v___jp_839_;
}
}
}
}
else
{
lean_dec_ref_known(v_pre_884_, 2);
lean_dec_ref_known(v_declName_883_, 2);
lean_dec_ref_known(v_fn_882_, 2);
lean_del_object(v___x_871_);
goto v___jp_839_;
}
}
else
{
lean_dec(v_pre_884_);
lean_dec_ref_known(v_declName_883_, 2);
lean_dec_ref_known(v_fn_882_, 2);
lean_del_object(v___x_871_);
goto v___jp_839_;
}
}
else
{
lean_dec_ref_known(v_fn_882_, 2);
lean_dec(v_declName_883_);
lean_del_object(v___x_871_);
goto v___jp_839_;
}
}
else
{
lean_dec_ref(v_fn_882_);
lean_del_object(v___x_871_);
goto v___jp_839_;
}
}
else
{
lean_dec_ref(v_struct_876_);
lean_del_object(v___x_871_);
goto v___jp_839_;
}
}
}
}
else
{
lean_dec_ref_known(v_typeName_873_, 2);
lean_del_object(v___x_871_);
lean_dec_ref_known(v_a_849_, 3);
goto v___jp_839_;
}
}
else
{
lean_dec(v_typeName_873_);
lean_del_object(v___x_871_);
lean_dec_ref_known(v_a_849_, 3);
goto v___jp_839_;
}
}
}
default: 
{
lean_dec_ref_known(v___x_848_, 1);
goto v___jp_839_;
}
}
}
else
{
return v___x_848_;
}
}
else
{
lean_object* v___x_900_; lean_object* v___x_902_; 
lean_dec_ref(v_type_833_);
v___x_900_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_900_);
v___x_902_ = v___x_845_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec_ref(v_type_833_);
v_a_905_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_842_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_842_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
v___jp_839_:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_833_ = stack[0].m_obj;
lean_object* v_a_834_ = stack[1].m_obj;
lean_object* v_a_835_ = stack[2].m_obj;
lean_object* v_a_836_ = stack[3].m_obj;
lean_object* v_a_837_ = stack[4].m_obj;
lean_object* v_res_913_;
v_res_913_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_type_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
stack->m_obj
 = v_res_913_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(lean_object* v_as_914_, size_t v_sz_915_, size_t v_i_916_, lean_object* v_b_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_a_924_; uint8_t v___x_928_; 
v___x_928_ = lean_usize_dec_lt(v_i_916_, v_sz_915_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v_b_917_);
return v___x_929_;
}
else
{
lean_object* v_a_930_; lean_object* v___y_932_; lean_object* v___x_961_; 
v_a_930_ = lean_array_uget_borrowed(v_as_914_, v_i_916_);
lean_inc(v_a_930_);
v___x_961_ = l_Lean_Meta_isProp(v_a_930_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; uint8_t v___x_963_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v___x_963_ = lean_unbox(v_a_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
lean_dec_ref_known(v___x_961_, 1);
lean_inc(v_a_930_);
v___x_964_ = l_Lean_Compiler_LCNF_isPropFormer(v_a_930_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
v___y_932_ = v___x_964_;
goto v___jp_931_;
}
else
{
v___y_932_ = v___x_961_;
goto v___jp_931_;
}
}
else
{
v___y_932_ = v___x_961_;
goto v___jp_931_;
}
v___jp_931_:
{
if (lean_obj_tag(v___y_932_) == 0)
{
lean_object* v_a_933_; uint8_t v___x_934_; 
v_a_933_ = lean_ctor_get(v___y_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___y_932_, 1);
v___x_934_ = lean_unbox(v_a_933_);
lean_dec(v_a_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
lean_inc(v_a_930_);
v___x_935_ = l_Lean_Meta_isTypeFormer(v_a_930_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; uint8_t v___x_937_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
v___x_937_ = lean_unbox(v_a_936_);
lean_dec(v_a_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
v___x_939_ = l_Lean_Expr_app___override(v_b_917_, v___x_938_);
v_a_924_ = v___x_939_;
goto v___jp_923_;
}
else
{
lean_object* v___x_940_; 
lean_inc(v_a_930_);
v___x_940_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_a_930_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_942_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
v___x_942_ = l_Lean_Expr_app___override(v_b_917_, v_a_941_);
v_a_924_ = v___x_942_;
goto v___jp_923_;
}
else
{
lean_dec_ref(v_b_917_);
return v___x_940_;
}
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec_ref(v_b_917_);
v_a_943_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_935_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_935_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_952_ = l_Lean_Expr_app___override(v_b_917_, v___x_951_);
v_a_924_ = v___x_952_;
goto v___jp_923_;
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref(v_b_917_);
v_a_953_ = lean_ctor_get(v___y_932_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___y_932_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___y_932_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___y_932_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
v___jp_923_:
{
size_t v___x_925_; size_t v___x_926_; 
v___x_925_ = ((size_t)1ULL);
v___x_926_ = lean_usize_add(v_i_916_, v___x_925_);
v_i_916_ = v___x_926_;
v_b_917_ = v_a_924_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_914_ = stack[0].m_obj;
size_t v_sz_915_ = stack[1].m_num;
size_t v_i_916_ = stack[2].m_num;
lean_object* v_b_917_ = stack[3].m_obj;
lean_object* v___y_918_ = stack[4].m_obj;
lean_object* v___y_919_ = stack[5].m_obj;
lean_object* v___y_920_ = stack[6].m_obj;
lean_object* v___y_921_ = stack[7].m_obj;
lean_object* v_res_965_;
v_res_965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_as_914_, v_sz_915_, v_i_916_, v_b_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
stack->m_obj
 = v_res_965_;
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__0));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(lean_object* v_f_969_, lean_object* v_args_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_fNew_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; 
switch(lean_obj_tag(v_f_969_))
{
case 4:
{
lean_object* v_declName_985_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___x_1009_; lean_object* v_env_1010_; uint8_t v_isExporting_1011_; 
v_declName_985_ = lean_ctor_get(v_f_969_, 0);
v___x_1009_ = lean_st_ref_get(v_a_974_);
v_env_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc_ref(v_env_1010_);
lean_dec(v___x_1009_);
v_isExporting_1011_ = lean_ctor_get_uint8(v_env_1010_, sizeof(void*)*13);
lean_dec_ref(v_env_1010_);
if (v_isExporting_1011_ == 0)
{
v___y_987_ = v_a_971_;
v___y_988_ = v_a_972_;
v___y_989_ = v_a_973_;
v___y_990_ = v_a_974_;
goto v___jp_986_;
}
else
{
uint8_t v___x_1012_; 
v___x_1012_ = l_Lean_isPrivateName(v_declName_985_);
if (v___x_1012_ == 0)
{
v___y_987_ = v_a_971_;
v___y_988_ = v_a_972_;
v___y_989_ = v_a_973_;
v___y_990_ = v_a_974_;
goto v___jp_986_;
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1);
v___x_1014_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v___x_1013_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_dec_ref_known(v___x_1014_, 1);
v___y_987_ = v_a_971_;
v___y_988_ = v_a_972_;
v___y_989_ = v_a_973_;
v___y_990_ = v_a_974_;
goto v___jp_986_;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref_known(v_f_969_, 2);
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
v___jp_986_:
{
lean_object* v___x_991_; 
lean_inc(v_declName_985_);
v___x_991_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_declName_985_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1000_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1000_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1000_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
if (lean_obj_tag(v_a_992_) == 5)
{
lean_dec_ref_known(v_a_992_, 1);
lean_del_object(v___x_994_);
v_fNew_977_ = v_f_969_;
v___y_978_ = v___y_987_;
v___y_979_ = v___y_988_;
v___y_980_ = v___y_989_;
v___y_981_ = v___y_990_;
goto v___jp_976_;
}
else
{
lean_object* v___x_996_; lean_object* v___x_998_; 
lean_dec(v_a_992_);
lean_dec_ref_known(v_f_969_, 2);
v___x_996_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_996_);
v___x_998_ = v___x_994_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref_known(v_f_969_, 2);
v_a_1001_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_991_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_991_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
case 1:
{
v_fNew_977_ = v_f_969_;
v___y_978_ = v_a_971_;
v___y_979_ = v_a_972_;
v___y_980_ = v_a_973_;
v___y_981_ = v_a_974_;
goto v___jp_976_;
}
default: 
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_dec_ref(v_f_969_);
v___x_1023_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
}
v___jp_976_:
{
size_t v_sz_982_; size_t v___x_983_; lean_object* v___x_984_; 
v_sz_982_ = lean_array_size(v_args_970_);
v___x_983_ = ((size_t)0ULL);
v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_args_970_, v_sz_982_, v___x_983_, v_fNew_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
return v___x_984_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_969_ = stack[0].m_obj;
lean_object* v_args_970_ = stack[1].m_obj;
lean_object* v_a_971_ = stack[2].m_obj;
lean_object* v_a_972_ = stack[3].m_obj;
lean_object* v_a_973_ = stack[4].m_obj;
lean_object* v_a_974_ = stack[5].m_obj;
lean_object* v_res_1025_;
v_res_1025_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_f_969_, v_args_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
stack->m_obj
 = v_res_1025_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(lean_object* v_x_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
if (lean_obj_tag(v_x_1026_) == 5)
{
lean_object* v_fn_1034_; lean_object* v_arg_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v_fn_1034_ = lean_ctor_get(v_x_1026_, 0);
lean_inc_ref(v_fn_1034_);
v_arg_1035_ = lean_ctor_get(v_x_1026_, 1);
lean_inc_ref(v_arg_1035_);
lean_dec_ref_known(v_x_1026_, 2);
v___x_1036_ = lean_array_set(v_x_1027_, v_x_1028_, v_arg_1035_);
v___x_1037_ = lean_unsigned_to_nat(1u);
v___x_1038_ = lean_nat_sub(v_x_1028_, v___x_1037_);
lean_dec(v_x_1028_);
v_x_1026_ = v_fn_1034_;
v_x_1027_ = v___x_1036_;
v_x_1028_ = v___x_1038_;
goto _start;
}
else
{
lean_object* v___x_1040_; 
lean_dec(v_x_1028_);
v___x_1040_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_x_1026_, v_x_1027_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec_ref(v_x_1027_);
return v___x_1040_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1026_ = stack[0].m_obj;
lean_object* v_x_1027_ = stack[1].m_obj;
lean_object* v_x_1028_ = stack[2].m_obj;
lean_object* v___y_1029_ = stack[3].m_obj;
lean_object* v___y_1030_ = stack[4].m_obj;
lean_object* v___y_1031_ = stack[5].m_obj;
lean_object* v___y_1032_ = stack[6].m_obj;
lean_object* v_res_1041_;
v_res_1041_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_x_1026_, v_x_1027_, v_x_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
stack->m_obj
 = v_res_1041_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0___boxed(lean_object* v_x_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_x_1042_, v_x_1043_, v_x_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___boxed(lean_object* v_e_1051_, lean_object* v_xs_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_e_1051_, v_xs_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___boxed(lean_object* v_f_1059_, lean_object* v_args_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_f_1059_, v_args_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec_ref(v_args_1060_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3___boxed(lean_object* v_as_1067_, lean_object* v_sz_1068_, lean_object* v_i_1069_, lean_object* v_b_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
size_t v_sz_boxed_1076_; size_t v_i_boxed_1077_; lean_object* v_res_1078_; 
v_sz_boxed_1076_ = lean_unbox_usize(v_sz_1068_);
lean_dec(v_sz_1068_);
v_i_boxed_1077_ = lean_unbox_usize(v_i_1069_);
lean_dec(v_i_1069_);
v_res_1078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_as_1067_, v_sz_boxed_1076_, v_i_boxed_1077_, v_b_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec_ref(v_as_1067_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed(lean_object* v_type_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_type_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
return v_res_1085_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(lean_object* v_00_u03b1_1086_, lean_object* v_msg_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1087_ = stack[1].m_obj;
lean_object* v___y_1088_ = stack[2].m_obj;
lean_object* v___y_1089_ = stack[3].m_obj;
lean_object* v___y_1090_ = stack[4].m_obj;
lean_object* v___y_1091_ = stack[5].m_obj;
lean_object* v_res_1094_;
v_res_1094_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(lean_box(0), v_msg_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
stack->m_obj
 = v_res_1094_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___boxed(lean_object* v_00_u03b1_1095_, lean_object* v_msg_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(v_00_u03b1_1095_, v_msg_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
return v_res_1102_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(lean_object* v_00_u03b1_1103_, lean_object* v_constName_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
return v___x_1110_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1104_ = stack[1].m_obj;
lean_object* v___y_1105_ = stack[2].m_obj;
lean_object* v___y_1106_ = stack[3].m_obj;
lean_object* v___y_1107_ = stack[4].m_obj;
lean_object* v___y_1108_ = stack[5].m_obj;
lean_object* v_res_1111_;
v_res_1111_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(lean_box(0), v_constName_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
stack->m_obj
 = v_res_1111_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___boxed(lean_object* v_00_u03b1_1112_, lean_object* v_constName_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(v_00_u03b1_1112_, v_constName_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1119_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(lean_object* v_00_u03b1_1120_, lean_object* v_ref_1121_, lean_object* v_constName_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_1121_, v_constName_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1121_ = stack[1].m_obj;
lean_object* v_constName_1122_ = stack[2].m_obj;
lean_object* v___y_1123_ = stack[3].m_obj;
lean_object* v___y_1124_ = stack[4].m_obj;
lean_object* v___y_1125_ = stack[5].m_obj;
lean_object* v___y_1126_ = stack[6].m_obj;
lean_object* v_res_1129_;
v_res_1129_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(lean_box(0), v_ref_1121_, v_constName_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
stack->m_obj
 = v_res_1129_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1130_, lean_object* v_ref_1131_, lean_object* v_constName_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(v_00_u03b1_1130_, v_ref_1131_, v_constName_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v_ref_1131_);
return v_res_1138_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(lean_object* v_00_u03b1_1139_, lean_object* v_ref_1140_, lean_object* v_msg_1141_, lean_object* v_declHint_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_1140_, v_msg_1141_, v_declHint_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
return v___x_1148_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1140_ = stack[1].m_obj;
lean_object* v_msg_1141_ = stack[2].m_obj;
lean_object* v_declHint_1142_ = stack[3].m_obj;
lean_object* v___y_1143_ = stack[4].m_obj;
lean_object* v___y_1144_ = stack[5].m_obj;
lean_object* v___y_1145_ = stack[6].m_obj;
lean_object* v___y_1146_ = stack[7].m_obj;
lean_object* v_res_1149_;
v_res_1149_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(lean_box(0), v_ref_1140_, v_msg_1141_, v_declHint_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
stack->m_obj
 = v_res_1149_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1150_, lean_object* v_ref_1151_, lean_object* v_msg_1152_, lean_object* v_declHint_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(v_00_u03b1_1150_, v_ref_1151_, v_msg_1152_, v_declHint_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v_ref_1151_);
return v_res_1159_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(lean_object* v_msg_1160_, lean_object* v_declHint_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_1160_, v_declHint_1161_, v___y_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1160_ = stack[0].m_obj;
lean_object* v_declHint_1161_ = stack[1].m_obj;
lean_object* v___y_1162_ = stack[2].m_obj;
lean_object* v___y_1163_ = stack[3].m_obj;
lean_object* v___y_1164_ = stack[4].m_obj;
lean_object* v___y_1165_ = stack[5].m_obj;
lean_object* v_res_1168_;
v_res_1168_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(v_msg_1160_, v_declHint_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
stack->m_obj
 = v_res_1168_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_1169_, lean_object* v_declHint_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(v_msg_1169_, v_declHint_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
return v_res_1176_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(lean_object* v_00_u03b1_1177_, lean_object* v_ref_1178_, lean_object* v_msg_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_1178_, v_msg_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
return v___x_1185_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1178_ = stack[1].m_obj;
lean_object* v_msg_1179_ = stack[2].m_obj;
lean_object* v___y_1180_ = stack[3].m_obj;
lean_object* v___y_1181_ = stack[4].m_obj;
lean_object* v___y_1182_ = stack[5].m_obj;
lean_object* v___y_1183_ = stack[6].m_obj;
lean_object* v_res_1186_;
v_res_1186_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(lean_box(0), v_ref_1178_, v_msg_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
stack->m_obj
 = v_res_1186_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1187_, lean_object* v_ref_1188_, lean_object* v_msg_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(v_00_u03b1_1187_, v_ref_1188_, v_msg_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v_ref_1188_);
return v_res_1195_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(lean_object* v___y_1196_, uint8_t v_isExporting_1197_, lean_object* v___x_1198_, lean_object* v___y_1199_, lean_object* v___x_1200_, lean_object* v_a_x3f_1201_){
_start:
{
lean_object* v___x_1203_; lean_object* v_env_1204_; lean_object* v_nextMacroScope_1205_; lean_object* v_ngen_1206_; lean_object* v_auxDeclNGen_1207_; lean_object* v_traceState_1208_; lean_object* v_recordedDeps_1209_; lean_object* v_messages_1210_; lean_object* v_infoState_1211_; lean_object* v_snapshotTasks_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1237_; 
v___x_1203_ = lean_st_ref_take(v___y_1196_);
v_env_1204_ = lean_ctor_get(v___x_1203_, 0);
v_nextMacroScope_1205_ = lean_ctor_get(v___x_1203_, 1);
v_ngen_1206_ = lean_ctor_get(v___x_1203_, 2);
v_auxDeclNGen_1207_ = lean_ctor_get(v___x_1203_, 3);
v_traceState_1208_ = lean_ctor_get(v___x_1203_, 4);
v_recordedDeps_1209_ = lean_ctor_get(v___x_1203_, 6);
v_messages_1210_ = lean_ctor_get(v___x_1203_, 7);
v_infoState_1211_ = lean_ctor_get(v___x_1203_, 8);
v_snapshotTasks_1212_ = lean_ctor_get(v___x_1203_, 9);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v___x_1203_, 5);
lean_dec(v_unused_1238_);
v___x_1214_ = v___x_1203_;
v_isShared_1215_ = v_isSharedCheck_1237_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_snapshotTasks_1212_);
lean_inc(v_infoState_1211_);
lean_inc(v_messages_1210_);
lean_inc(v_recordedDeps_1209_);
lean_inc(v_traceState_1208_);
lean_inc(v_auxDeclNGen_1207_);
lean_inc(v_ngen_1206_);
lean_inc(v_nextMacroScope_1205_);
lean_inc(v_env_1204_);
lean_dec(v___x_1203_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1237_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = l_Lean_Environment_setExporting(v_env_1204_, v_isExporting_1197_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 5, v___x_1198_);
lean_ctor_set(v___x_1214_, 0, v___x_1216_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_nextMacroScope_1205_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_ngen_1206_);
lean_ctor_set(v_reuseFailAlloc_1236_, 3, v_auxDeclNGen_1207_);
lean_ctor_set(v_reuseFailAlloc_1236_, 4, v_traceState_1208_);
lean_ctor_set(v_reuseFailAlloc_1236_, 5, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1236_, 6, v_recordedDeps_1209_);
lean_ctor_set(v_reuseFailAlloc_1236_, 7, v_messages_1210_);
lean_ctor_set(v_reuseFailAlloc_1236_, 8, v_infoState_1211_);
lean_ctor_set(v_reuseFailAlloc_1236_, 9, v_snapshotTasks_1212_);
v___x_1218_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v_mctx_1221_; lean_object* v_zetaDeltaFVarIds_1222_; lean_object* v_postponed_1223_; lean_object* v_diag_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1234_; 
v___x_1219_ = lean_st_ref_put(v___y_1196_, v___x_1218_);
v___x_1220_ = lean_st_ref_take(v___y_1199_);
v_mctx_1221_ = lean_ctor_get(v___x_1220_, 0);
v_zetaDeltaFVarIds_1222_ = lean_ctor_get(v___x_1220_, 2);
v_postponed_1223_ = lean_ctor_get(v___x_1220_, 3);
v_diag_1224_ = lean_ctor_get(v___x_1220_, 4);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v___x_1220_, 1);
lean_dec(v_unused_1235_);
v___x_1226_ = v___x_1220_;
v_isShared_1227_ = v_isSharedCheck_1234_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_diag_1224_);
lean_inc(v_postponed_1223_);
lean_inc(v_zetaDeltaFVarIds_1222_);
lean_inc(v_mctx_1221_);
lean_dec(v___x_1220_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1234_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1228_ = lean_box(0);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___x_1200_);
v___x_1230_ = v___x_1226_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_mctx_1221_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_zetaDeltaFVarIds_1222_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v_postponed_1223_);
lean_ctor_set(v_reuseFailAlloc_1233_, 4, v_diag_1224_);
v___x_1230_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_st_ref_put(v___y_1199_, v___x_1230_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1228_);
return v___x_1232_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1196_ = stack[0].m_obj;
uint8_t v_isExporting_1197_ = stack[1].m_num;
lean_object* v___x_1198_ = stack[2].m_obj;
lean_object* v___y_1199_ = stack[3].m_obj;
lean_object* v___x_1200_ = stack[4].m_obj;
lean_object* v_a_x3f_1201_ = stack[5].m_obj;
lean_object* v_res_1239_;
v_res_1239_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1196_, v_isExporting_1197_, v___x_1198_, v___y_1199_, v___x_1200_, v_a_x3f_1201_);
stack->m_obj
 = v_res_1239_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0___boxed(lean_object* v___y_1240_, lean_object* v_isExporting_1241_, lean_object* v___x_1242_, lean_object* v___y_1243_, lean_object* v___x_1244_, lean_object* v_a_x3f_1245_, lean_object* v___y_1246_){
_start:
{
uint8_t v_isExporting_boxed_1247_; lean_object* v_res_1248_; 
v_isExporting_boxed_1247_ = lean_unbox(v_isExporting_1241_);
v_res_1248_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1240_, v_isExporting_boxed_1247_, v___x_1242_, v___y_1243_, v___x_1244_, v_a_x3f_1245_);
lean_dec(v_a_x3f_1245_);
lean_dec(v___y_1243_);
lean_dec(v___y_1240_);
return v_res_1248_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
return v___x_1252_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0);
v___x_1254_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
lean_ctor_set(v___x_1254_, 2, v___x_1253_);
lean_ctor_set(v___x_1254_, 3, v___x_1253_);
lean_ctor_set(v___x_1254_, 4, v___x_1253_);
lean_ctor_set(v___x_1254_, 5, v___x_1253_);
return v___x_1254_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(lean_object* v_x_1255_, uint8_t v_isExporting_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; lean_object* v_env_1263_; lean_object* v___x_1264_; uint8_t v_isModule_1265_; 
v___x_1262_ = lean_st_ref_get(v___y_1260_);
v_env_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc_ref(v_env_1263_);
lean_dec(v___x_1262_);
v___x_1264_ = l_Lean_Environment_header(v_env_1263_);
v_isModule_1265_ = lean_ctor_get_uint8(v___x_1264_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1264_);
if (v_isModule_1265_ == 0)
{
lean_object* v___x_1266_; 
lean_dec_ref(v_env_1263_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
lean_inc(v___y_1258_);
lean_inc_ref(v___y_1257_);
v___x_1266_ = lean_apply_5(v_x_1255_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, lean_box(0));
return v___x_1266_;
}
else
{
uint8_t v_isExporting_1267_; 
v_isExporting_1267_ = lean_ctor_get_uint8(v_env_1263_, sizeof(void*)*13);
lean_dec_ref(v_env_1263_);
if (v_isExporting_1256_ == 0)
{
if (v_isExporting_1267_ == 0)
{
lean_object* v___x_1334_; 
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
lean_inc(v___y_1258_);
lean_inc_ref(v___y_1257_);
v___x_1334_ = lean_apply_5(v_x_1255_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, lean_box(0));
return v___x_1334_;
}
else
{
goto v___jp_1268_;
}
}
else
{
if (v_isExporting_1267_ == 0)
{
goto v___jp_1268_;
}
else
{
lean_object* v___x_1335_; 
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
lean_inc(v___y_1258_);
lean_inc_ref(v___y_1257_);
v___x_1335_ = lean_apply_5(v_x_1255_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, lean_box(0));
return v___x_1335_;
}
}
v___jp_1268_:
{
lean_object* v___x_1269_; lean_object* v_env_1270_; lean_object* v_nextMacroScope_1271_; lean_object* v_ngen_1272_; lean_object* v_auxDeclNGen_1273_; lean_object* v_traceState_1274_; lean_object* v_recordedDeps_1275_; lean_object* v_messages_1276_; lean_object* v_infoState_1277_; lean_object* v_snapshotTasks_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1332_; 
v___x_1269_ = lean_st_ref_take(v___y_1260_);
v_env_1270_ = lean_ctor_get(v___x_1269_, 0);
v_nextMacroScope_1271_ = lean_ctor_get(v___x_1269_, 1);
v_ngen_1272_ = lean_ctor_get(v___x_1269_, 2);
v_auxDeclNGen_1273_ = lean_ctor_get(v___x_1269_, 3);
v_traceState_1274_ = lean_ctor_get(v___x_1269_, 4);
v_recordedDeps_1275_ = lean_ctor_get(v___x_1269_, 6);
v_messages_1276_ = lean_ctor_get(v___x_1269_, 7);
v_infoState_1277_ = lean_ctor_get(v___x_1269_, 8);
v_snapshotTasks_1278_ = lean_ctor_get(v___x_1269_, 9);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; 
v_unused_1333_ = lean_ctor_get(v___x_1269_, 5);
lean_dec(v_unused_1333_);
v___x_1280_ = v___x_1269_;
v_isShared_1281_ = v_isSharedCheck_1332_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_snapshotTasks_1278_);
lean_inc(v_infoState_1277_);
lean_inc(v_messages_1276_);
lean_inc(v_recordedDeps_1275_);
lean_inc(v_traceState_1274_);
lean_inc(v_auxDeclNGen_1273_);
lean_inc(v_ngen_1272_);
lean_inc(v_nextMacroScope_1271_);
lean_inc(v_env_1270_);
lean_dec(v___x_1269_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1332_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1282_ = l_Lean_Environment_setExporting(v_env_1270_, v_isExporting_1256_);
v___x_1283_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 5, v___x_1283_);
lean_ctor_set(v___x_1280_, 0, v___x_1282_);
v___x_1285_ = v___x_1280_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_nextMacroScope_1271_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_ngen_1272_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v_auxDeclNGen_1273_);
lean_ctor_set(v_reuseFailAlloc_1331_, 4, v_traceState_1274_);
lean_ctor_set(v_reuseFailAlloc_1331_, 5, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1331_, 6, v_recordedDeps_1275_);
lean_ctor_set(v_reuseFailAlloc_1331_, 7, v_messages_1276_);
lean_ctor_set(v_reuseFailAlloc_1331_, 8, v_infoState_1277_);
lean_ctor_set(v_reuseFailAlloc_1331_, 9, v_snapshotTasks_1278_);
v___x_1285_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v_mctx_1288_; lean_object* v_zetaDeltaFVarIds_1289_; lean_object* v_postponed_1290_; lean_object* v_diag_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1329_; 
v___x_1286_ = lean_st_ref_put(v___y_1260_, v___x_1285_);
v___x_1287_ = lean_st_ref_take(v___y_1258_);
v_mctx_1288_ = lean_ctor_get(v___x_1287_, 0);
v_zetaDeltaFVarIds_1289_ = lean_ctor_get(v___x_1287_, 2);
v_postponed_1290_ = lean_ctor_get(v___x_1287_, 3);
v_diag_1291_ = lean_ctor_get(v___x_1287_, 4);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v___x_1287_, 1);
lean_dec(v_unused_1330_);
v___x_1293_ = v___x_1287_;
v_isShared_1294_ = v_isSharedCheck_1329_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_diag_1291_);
lean_inc(v_postponed_1290_);
lean_inc(v_zetaDeltaFVarIds_1289_);
lean_inc(v_mctx_1288_);
lean_dec(v___x_1287_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1329_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1295_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v___x_1295_);
v___x_1297_ = v___x_1293_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_mctx_1288_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_zetaDeltaFVarIds_1289_);
lean_ctor_set(v_reuseFailAlloc_1328_, 3, v_postponed_1290_);
lean_ctor_set(v_reuseFailAlloc_1328_, 4, v_diag_1291_);
v___x_1297_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1298_; lean_object* v_r_1299_; 
v___x_1298_ = lean_st_ref_put(v___y_1258_, v___x_1297_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
lean_inc(v___y_1258_);
lean_inc_ref(v___y_1257_);
v_r_1299_ = lean_apply_5(v_x_1255_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, lean_box(0));
if (lean_obj_tag(v_r_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1316_; 
v_a_1300_ = lean_ctor_get(v_r_1299_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_r_1299_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1302_ = v_r_1299_;
v_isShared_1303_ = v_isSharedCheck_1316_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v_r_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1316_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
lean_inc(v_a_1300_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set_tag(v___x_1302_, 1);
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
v___x_1306_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1260_, v_isExporting_1267_, v___x_1283_, v___y_1258_, v___x_1295_, v___x_1305_);
lean_dec_ref(v___x_1305_);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; 
v_unused_1314_ = lean_ctor_get(v___x_1306_, 0);
lean_dec(v_unused_1314_);
v___x_1308_ = v___x_1306_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_dec(v___x_1306_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v_a_1300_);
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1300_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
v_a_1317_ = lean_ctor_get(v_r_1299_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v_r_1299_, 1);
v___x_1318_ = lean_box(0);
v___x_1319_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1260_, v_isExporting_1267_, v___x_1283_, v___y_1258_, v___x_1295_, v___x_1318_);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v___x_1319_, 0);
lean_dec(v_unused_1327_);
v___x_1321_ = v___x_1319_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_dec(v___x_1319_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 1);
lean_ctor_set(v___x_1321_, 0, v_a_1317_);
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1317_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1255_ = stack[0].m_obj;
uint8_t v_isExporting_1256_ = stack[1].m_num;
lean_object* v___y_1257_ = stack[2].m_obj;
lean_object* v___y_1258_ = stack[3].m_obj;
lean_object* v___y_1259_ = stack[4].m_obj;
lean_object* v___y_1260_ = stack[5].m_obj;
lean_object* v_res_1336_;
v_res_1336_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v_x_1255_, v_isExporting_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
stack->m_obj
 = v_res_1336_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___boxed(lean_object* v_x_1337_, lean_object* v_isExporting_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
uint8_t v_isExporting_boxed_1344_; lean_object* v_res_1345_; 
v_isExporting_boxed_1344_ = lean_unbox(v_isExporting_1338_);
v_res_1345_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v_x_1337_, v_isExporting_boxed_1344_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
return v_res_1345_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(lean_object* v_00_u03b1_1346_, lean_object* v_x_1347_, uint8_t v_isExporting_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v_x_1347_, v_isExporting_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1347_ = stack[1].m_obj;
uint8_t v_isExporting_1348_ = stack[2].m_num;
lean_object* v___y_1349_ = stack[3].m_obj;
lean_object* v___y_1350_ = stack[4].m_obj;
lean_object* v___y_1351_ = stack[5].m_obj;
lean_object* v___y_1352_ = stack[6].m_obj;
lean_object* v_res_1355_;
v_res_1355_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(lean_box(0), v_x_1347_, v_isExporting_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
stack->m_obj
 = v_res_1355_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___boxed(lean_object* v_00_u03b1_1356_, lean_object* v_x_1357_, lean_object* v_isExporting_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
uint8_t v_isExporting_boxed_1364_; lean_object* v_res_1365_; 
v_isExporting_boxed_1364_ = lean_unbox(v_isExporting_1358_);
v_res_1365_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(v_00_u03b1_1356_, v_x_1357_, v_isExporting_boxed_1364_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(lean_object* v_opts_1366_, lean_object* v_opt_1367_){
_start:
{
lean_object* v_name_1368_; lean_object* v_defValue_1369_; lean_object* v_map_1370_; lean_object* v___x_1371_; 
v_name_1368_ = lean_ctor_get(v_opt_1367_, 0);
v_defValue_1369_ = lean_ctor_get(v_opt_1367_, 1);
v_map_1370_ = lean_ctor_get(v_opts_1366_, 0);
v___x_1371_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1370_, v_name_1368_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_inc(v_defValue_1369_);
return v_defValue_1369_;
}
else
{
lean_object* v_val_1372_; 
v_val_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_val_1372_);
lean_dec_ref_known(v___x_1371_, 1);
if (lean_obj_tag(v_val_1372_) == 3)
{
lean_object* v_v_1373_; 
v_v_1373_ = lean_ctor_get(v_val_1372_, 0);
lean_inc(v_v_1373_);
lean_dec_ref_known(v_val_1372_, 1);
return v_v_1373_;
}
else
{
lean_dec(v_val_1372_);
lean_inc(v_defValue_1369_);
return v_defValue_1369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__4___boxed(lean_object* v_opts_1374_, lean_object* v_opt_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(v_opts_1374_, v_opt_1375_);
lean_dec_ref(v_opt_1375_);
lean_dec_ref(v_opts_1374_);
return v_res_1376_;
}
}
lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0(lean_object* v_a_1377_, lean_object* v_diag_1378_, lean_object* v_a_x3f_1379_){
_start:
{
lean_object* v___x_1381_; lean_object* v_mctx_1382_; lean_object* v_cache_1383_; lean_object* v_zetaDeltaFVarIds_1384_; lean_object* v_postponed_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1395_; 
v___x_1381_ = lean_st_ref_take(v_a_1377_);
v_mctx_1382_ = lean_ctor_get(v___x_1381_, 0);
v_cache_1383_ = lean_ctor_get(v___x_1381_, 1);
v_zetaDeltaFVarIds_1384_ = lean_ctor_get(v___x_1381_, 2);
v_postponed_1385_ = lean_ctor_get(v___x_1381_, 3);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; 
v_unused_1396_ = lean_ctor_get(v___x_1381_, 4);
lean_dec(v_unused_1396_);
v___x_1387_ = v___x_1381_;
v_isShared_1388_ = v_isSharedCheck_1395_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_postponed_1385_);
lean_inc(v_zetaDeltaFVarIds_1384_);
lean_inc(v_cache_1383_);
lean_inc(v_mctx_1382_);
lean_dec(v___x_1381_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1395_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1389_ = lean_box(0);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 4, v_diag_1378_);
v___x_1391_ = v___x_1387_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_mctx_1382_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_cache_1383_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_zetaDeltaFVarIds_1384_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v_postponed_1385_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v_diag_1378_);
v___x_1391_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_st_ref_put(v_a_1377_, v___x_1391_);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1389_);
return v___x_1393_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_toLCNFType___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1377_ = stack[0].m_obj;
lean_object* v_diag_1378_ = stack[1].m_obj;
lean_object* v_a_x3f_1379_ = stack[2].m_obj;
lean_object* v_res_1397_;
v_res_1397_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1377_, v_diag_1378_, v_a_x3f_1379_);
stack->m_obj
 = v_res_1397_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0___boxed(lean_object* v_a_1398_, lean_object* v_diag_1399_, lean_object* v_a_x3f_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1398_, v_diag_1399_, v_a_x3f_1400_);
lean_dec(v_a_x3f_1400_);
lean_dec(v_a_1398_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___lam__0(lean_object* v_ps_1403_, lean_object* v_k_1404_, lean_object* v_v_1405_){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v_k_1404_);
lean_ctor_set(v___x_1406_, 1, v_v_1405_);
v___x_1407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v_ps_1403_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___lam__0(lean_object* v_f_1408_, lean_object* v_x1_1409_, lean_object* v_x2_1410_, lean_object* v_x3_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_apply_3(v_f_1408_, v_x1_1409_, v_x2_1410_, v_x3_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__12___redArg(lean_object* v_f_1413_, lean_object* v_keys_1414_, lean_object* v_vals_1415_, lean_object* v_i_1416_, lean_object* v_acc_1417_){
_start:
{
lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1418_ = lean_array_get_size(v_keys_1414_);
v___x_1419_ = lean_nat_dec_lt(v_i_1416_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_dec(v_i_1416_);
lean_dec(v_f_1413_);
return v_acc_1417_;
}
else
{
lean_object* v_k_1420_; lean_object* v_v_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_k_1420_ = lean_array_fget_borrowed(v_keys_1414_, v_i_1416_);
v_v_1421_ = lean_array_fget_borrowed(v_vals_1415_, v_i_1416_);
lean_inc(v_f_1413_);
lean_inc(v_v_1421_);
lean_inc(v_k_1420_);
v___x_1422_ = lean_apply_3(v_f_1413_, v_acc_1417_, v_k_1420_, v_v_1421_);
v___x_1423_ = lean_unsigned_to_nat(1u);
v___x_1424_ = lean_nat_add(v_i_1416_, v___x_1423_);
lean_dec(v_i_1416_);
v_i_1416_ = v___x_1424_;
v_acc_1417_ = v___x_1422_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__12___redArg___boxed(lean_object* v_f_1426_, lean_object* v_keys_1427_, lean_object* v_vals_1428_, lean_object* v_i_1429_, lean_object* v_acc_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__12___redArg(v_f_1426_, v_keys_1427_, v_vals_1428_, v_i_1429_, v_acc_1430_);
lean_dec_ref(v_vals_1428_);
lean_dec_ref(v_keys_1427_);
return v_res_1431_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11___redArg(lean_object* v_f_1432_, lean_object* v_as_1433_, size_t v_i_1434_, size_t v_stop_1435_, lean_object* v_b_1436_){
_start:
{
lean_object* v___y_1438_; uint8_t v___x_1442_; 
v___x_1442_ = lean_usize_dec_eq(v_i_1434_, v_stop_1435_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_array_uget_borrowed(v_as_1433_, v_i_1434_);
switch(lean_obj_tag(v___x_1443_))
{
case 0:
{
lean_object* v_key_1444_; lean_object* v_val_1445_; lean_object* v___x_1446_; 
v_key_1444_ = lean_ctor_get(v___x_1443_, 0);
v_val_1445_ = lean_ctor_get(v___x_1443_, 1);
lean_inc(v_f_1432_);
lean_inc(v_val_1445_);
lean_inc(v_key_1444_);
v___x_1446_ = lean_apply_3(v_f_1432_, v_b_1436_, v_key_1444_, v_val_1445_);
v___y_1438_ = v___x_1446_;
goto v___jp_1437_;
}
case 1:
{
lean_object* v_node_1447_; lean_object* v___x_1448_; 
v_node_1447_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_f_1432_);
v___x_1448_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10___redArg(v_f_1432_, v_node_1447_, v_b_1436_);
v___y_1438_ = v___x_1448_;
goto v___jp_1437_;
}
default: 
{
v___y_1438_ = v_b_1436_;
goto v___jp_1437_;
}
}
}
else
{
lean_dec(v_f_1432_);
return v_b_1436_;
}
v___jp_1437_:
{
size_t v___x_1439_; size_t v___x_1440_; 
v___x_1439_ = ((size_t)1ULL);
v___x_1440_ = lean_usize_add(v_i_1434_, v___x_1439_);
v_i_1434_ = v___x_1440_;
v_b_1436_ = v___y_1438_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1432_ = stack[0].m_obj;
lean_object* v_as_1433_ = stack[1].m_obj;
size_t v_i_1434_ = stack[2].m_num;
size_t v_stop_1435_ = stack[3].m_num;
lean_object* v_b_1436_ = stack[4].m_obj;
lean_object* v_res_1449_;
v_res_1449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11___redArg(v_f_1432_, v_as_1433_, v_i_1434_, v_stop_1435_, v_b_1436_);
stack->m_obj
 = v_res_1449_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10___redArg(lean_object* v_f_1450_, lean_object* v_x_1451_, lean_object* v_x_1452_){
_start:
{
if (lean_obj_tag(v_x_1451_) == 0)
{
lean_object* v_es_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v_es_1453_ = lean_ctor_get(v_x_1451_, 0);
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_array_get_size(v_es_1453_);
v___x_1456_ = lean_nat_dec_lt(v___x_1454_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_dec(v_f_1450_);
return v_x_1452_;
}
else
{
size_t v___x_1457_; size_t v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = ((size_t)0ULL);
v___x_1458_ = lean_usize_of_nat(v___x_1455_);
v___x_1459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11___redArg(v_f_1450_, v_es_1453_, v___x_1457_, v___x_1458_, v_x_1452_);
return v___x_1459_;
}
}
else
{
lean_object* v_ks_1460_; lean_object* v_vs_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_ks_1460_ = lean_ctor_get(v_x_1451_, 0);
v_vs_1461_ = lean_ctor_get(v_x_1451_, 1);
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__12___redArg(v_f_1450_, v_ks_1460_, v_vs_1461_, v___x_1462_, v_x_1452_);
return v___x_1463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_f_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10___redArg(v_f_1464_, v_x_1465_, v_x_1466_);
lean_dec_ref(v_x_1465_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11___redArg___boxed(lean_object* v_f_1468_, lean_object* v_as_1469_, lean_object* v_i_1470_, lean_object* v_stop_1471_, lean_object* v_b_1472_){
_start:
{
size_t v_i_boxed_1473_; size_t v_stop_boxed_1474_; lean_object* v_res_1475_; 
v_i_boxed_1473_ = lean_unbox_usize(v_i_1470_);
lean_dec(v_i_1470_);
v_stop_boxed_1474_ = lean_unbox_usize(v_stop_1471_);
lean_dec(v_stop_1471_);
v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11___redArg(v_f_1468_, v_as_1469_, v_i_boxed_1473_, v_stop_boxed_1474_, v_b_1472_);
lean_dec_ref(v_as_1469_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(lean_object* v_map_1476_, lean_object* v_f_1477_, lean_object* v_init_1478_){
_start:
{
lean_object* v___f_1479_; lean_object* v___x_1480_; 
v___f_1479_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1479_, 0, v_f_1477_);
v___x_1480_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10___redArg(v___f_1479_, v_map_1476_, v_init_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___boxed(lean_object* v_map_1481_, lean_object* v_f_1482_, lean_object* v_init_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_map_1481_, v_f_1482_, v_init_1483_);
lean_dec_ref(v_map_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(lean_object* v_m_1486_){
_start:
{
lean_object* v___f_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___f_1487_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0));
v___x_1488_ = lean_box(0);
v___x_1489_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_m_1486_, v___f_1487_, v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___boxed(lean_object* v_m_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_m_1490_);
lean_dec_ref(v_m_1490_);
return v_res_1491_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7(lean_object* v_o_1495_, lean_object* v_k_1496_, uint8_t v_v_1497_){
_start:
{
lean_object* v_map_1498_; uint8_t v_hasTrace_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1513_; 
v_map_1498_ = lean_ctor_get(v_o_1495_, 0);
v_hasTrace_1499_ = lean_ctor_get_uint8(v_o_1495_, sizeof(void*)*1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_o_1495_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1501_ = v_o_1495_;
v_isShared_1502_ = v_isSharedCheck_1513_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_map_1498_);
lean_dec(v_o_1495_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1513_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1503_, 0, v_v_1497_);
lean_inc(v_k_1496_);
v___x_1504_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1496_, v___x_1503_, v_map_1498_);
if (v_hasTrace_1499_ == 0)
{
lean_object* v___x_1505_; uint8_t v___x_1506_; lean_object* v___x_1508_; 
v___x_1505_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7___closed__1));
v___x_1506_ = l_Lean_Name_isPrefixOf(v___x_1505_, v_k_1496_);
lean_dec(v_k_1496_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1504_);
v___x_1508_ = v___x_1501_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1504_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*1, v___x_1506_);
return v___x_1508_;
}
}
else
{
lean_object* v___x_1511_; 
lean_dec(v_k_1496_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1504_);
v___x_1511_ = v___x_1501_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1504_);
lean_ctor_set_uint8(v_reuseFailAlloc_1512_, sizeof(void*)*1, v_hasTrace_1499_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_1495_ = stack[0].m_obj;
lean_object* v_k_1496_ = stack[1].m_obj;
uint8_t v_v_1497_ = stack[2].m_num;
lean_object* v_res_1514_;
v_res_1514_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7(v_o_1495_, v_k_1496_, v_v_1497_);
stack->m_obj
 = v_res_1514_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7___boxed(lean_object* v_o_1515_, lean_object* v_k_1516_, lean_object* v_v_1517_){
_start:
{
uint8_t v_v_boxed_1518_; lean_object* v_res_1519_; 
v_v_boxed_1518_ = lean_unbox(v_v_1517_);
v_res_1519_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7(v_o_1515_, v_k_1516_, v_v_boxed_1518_);
return v_res_1519_;
}
}
lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(lean_object* v_opts_1520_, lean_object* v_opt_1521_, uint8_t v_val_1522_){
_start:
{
lean_object* v_name_1523_; lean_object* v___x_1524_; 
v_name_1523_ = lean_ctor_get(v_opt_1521_, 0);
lean_inc(v_name_1523_);
lean_dec_ref(v_opt_1521_);
v___x_1524_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__7(v_opts_1520_, v_name_1523_, v_val_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1520_ = stack[0].m_obj;
lean_object* v_opt_1521_ = stack[1].m_obj;
uint8_t v_val_1522_ = stack[2].m_num;
lean_object* v_res_1525_;
v_res_1525_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(v_opts_1520_, v_opt_1521_, v_val_1522_);
stack->m_obj
 = v_res_1525_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5___boxed(lean_object* v_opts_1526_, lean_object* v_opt_1527_, lean_object* v_val_1528_){
_start:
{
uint8_t v_val_boxed_1529_; lean_object* v_res_1530_; 
v_val_boxed_1529_ = lean_unbox(v_val_1528_);
v_res_1530_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(v_opts_1526_, v_opt_1527_, v_val_boxed_1529_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__3___redArg(lean_object* v_keys_1531_, lean_object* v_vals_1532_, lean_object* v_i_1533_, lean_object* v_k_1534_){
_start:
{
lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = lean_array_get_size(v_keys_1531_);
v___x_1536_ = lean_nat_dec_lt(v_i_1533_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
lean_dec(v_i_1533_);
v___x_1537_ = lean_box(0);
return v___x_1537_;
}
else
{
lean_object* v_k_x27_1538_; uint8_t v___x_1539_; 
v_k_x27_1538_ = lean_array_fget_borrowed(v_keys_1531_, v_i_1533_);
v___x_1539_ = lean_name_eq(v_k_1534_, v_k_x27_1538_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_unsigned_to_nat(1u);
v___x_1541_ = lean_nat_add(v_i_1533_, v___x_1540_);
lean_dec(v_i_1533_);
v_i_1533_ = v___x_1541_;
goto _start;
}
else
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = lean_array_fget_borrowed(v_vals_1532_, v_i_1533_);
lean_dec(v_i_1533_);
lean_inc(v___x_1543_);
v___x_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_keys_1545_, lean_object* v_vals_1546_, lean_object* v_i_1547_, lean_object* v_k_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__3___redArg(v_keys_1545_, v_vals_1546_, v_i_1547_, v_k_1548_);
lean_dec(v_k_1548_);
lean_dec_ref(v_vals_1546_);
lean_dec_ref(v_keys_1545_);
return v_res_1549_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(lean_object* v_x_1550_, size_t v_x_1551_, lean_object* v_x_1552_){
_start:
{
if (lean_obj_tag(v_x_1550_) == 0)
{
lean_object* v_es_1553_; lean_object* v___x_1554_; size_t v___x_1555_; size_t v___x_1556_; lean_object* v_j_1557_; lean_object* v___x_1558_; 
v_es_1553_ = lean_ctor_get(v_x_1550_, 0);
v___x_1554_ = lean_box(2);
v___x_1555_ = ((size_t)31ULL);
v___x_1556_ = lean_usize_land(v_x_1551_, v___x_1555_);
v_j_1557_ = lean_usize_to_nat(v___x_1556_);
v___x_1558_ = lean_array_get_borrowed(v___x_1554_, v_es_1553_, v_j_1557_);
lean_dec(v_j_1557_);
switch(lean_obj_tag(v___x_1558_))
{
case 0:
{
lean_object* v_key_1559_; lean_object* v_val_1560_; uint8_t v___x_1561_; 
v_key_1559_ = lean_ctor_get(v___x_1558_, 0);
v_val_1560_ = lean_ctor_get(v___x_1558_, 1);
v___x_1561_ = lean_name_eq(v_x_1552_, v_key_1559_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_box(0);
return v___x_1562_;
}
else
{
lean_object* v___x_1563_; 
lean_inc(v_val_1560_);
v___x_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1563_, 0, v_val_1560_);
return v___x_1563_;
}
}
case 1:
{
lean_object* v_node_1564_; size_t v___x_1565_; size_t v___x_1566_; 
v_node_1564_ = lean_ctor_get(v___x_1558_, 0);
v___x_1565_ = ((size_t)5ULL);
v___x_1566_ = lean_usize_shift_right(v_x_1551_, v___x_1565_);
v_x_1550_ = v_node_1564_;
v_x_1551_ = v___x_1566_;
goto _start;
}
default: 
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_box(0);
return v___x_1568_;
}
}
}
else
{
lean_object* v_ks_1569_; lean_object* v_vs_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_ks_1569_ = lean_ctor_get(v_x_1550_, 0);
v_vs_1570_ = lean_ctor_get(v_x_1550_, 1);
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1572_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__3___redArg(v_ks_1569_, v_vs_1570_, v___x_1571_, v_x_1552_);
return v___x_1572_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1550_ = stack[0].m_obj;
size_t v_x_1551_ = stack[1].m_num;
lean_object* v_x_1552_ = stack[2].m_obj;
lean_object* v_res_1573_;
v_res_1573_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1550_, v_x_1551_, v_x_1552_);
stack->m_obj
 = v_res_1573_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___boxed(lean_object* v_x_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_){
_start:
{
size_t v_x_17713__boxed_1577_; lean_object* v_res_1578_; 
v_x_17713__boxed_1577_ = lean_unbox_usize(v_x_1575_);
lean_dec(v_x_1575_);
v_res_1578_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1574_, v_x_17713__boxed_1577_, v_x_1576_);
lean_dec(v_x_1576_);
lean_dec_ref(v_x_1574_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(lean_object* v_x_1579_, lean_object* v_x_1580_){
_start:
{
uint64_t v___y_1582_; 
if (lean_obj_tag(v_x_1580_) == 0)
{
uint64_t v___x_1585_; 
v___x_1585_ = 1723ULL;
v___y_1582_ = v___x_1585_;
goto v___jp_1581_;
}
else
{
uint64_t v_hash_1586_; 
v_hash_1586_ = lean_ctor_get_uint64(v_x_1580_, sizeof(void*)*2);
v___y_1582_ = v_hash_1586_;
goto v___jp_1581_;
}
v___jp_1581_:
{
size_t v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_uint64_to_usize(v___y_1582_);
v___x_1584_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1579_, v___x_1583_, v_x_1580_);
return v___x_1584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___boxed(lean_object* v_x_1587_, lean_object* v_x_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_x_1587_, v_x_1588_);
lean_dec(v_x_1588_);
lean_dec_ref(v_x_1587_);
return v_res_1589_;
}
}
static lean_object* _init_l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0));
v___x_1592_ = l_Lean_stringToMessageData(v___x_1591_);
return v___x_1592_;
}
}
lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(lean_object* v___x_1593_, uint8_t v___x_1594_, lean_object* v___x_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
if (lean_obj_tag(v_a_1596_) == 0)
{
lean_object* v___x_1598_; 
lean_dec_ref(v___x_1595_);
v___x_1598_ = lean_array_to_list(v_a_1597_);
return v___x_1598_;
}
else
{
lean_object* v_head_1599_; lean_object* v_tail_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1641_; 
v_head_1599_ = lean_ctor_get(v_a_1596_, 0);
v_tail_1600_ = lean_ctor_get(v_a_1596_, 1);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_a_1596_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1602_ = v_a_1596_;
v_isShared_1603_ = v_isSharedCheck_1641_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_tail_1600_);
lean_inc(v_head_1599_);
lean_dec(v_a_1596_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1641_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v_fst_1604_; lean_object* v_snd_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1640_; 
v_fst_1604_ = lean_ctor_get(v_head_1599_, 0);
v_snd_1605_ = lean_ctor_get(v_head_1599_, 1);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_head_1599_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1607_ = v_head_1599_;
v_isShared_1608_ = v_isSharedCheck_1640_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_snd_1605_);
lean_inc(v_fst_1604_);
lean_dec(v_head_1599_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1640_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___y_1610_; lean_object* v___y_1625_; uint8_t v___y_1626_; lean_object* v_unfoldAxiomCounter_1628_; lean_object* v___x_1629_; lean_object* v___y_1631_; lean_object* v___x_1638_; 
v_unfoldAxiomCounter_1628_ = lean_ctor_get(v___x_1593_, 1);
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1638_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_unfoldAxiomCounter_1628_, v_fst_1604_);
if (lean_obj_tag(v___x_1638_) == 0)
{
v___y_1631_ = v___x_1629_;
goto v___jp_1630_;
}
else
{
lean_object* v_val_1639_; 
v_val_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_val_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___y_1631_ = v_val_1639_;
goto v___jp_1630_;
}
v___jp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1611_ = l_Lean_MessageData_ofConstName(v_fst_1604_, v___x_1594_);
v___x_1612_ = lean_obj_once(&l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1, &l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1_once, _init_l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1);
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 7);
lean_ctor_set(v___x_1607_, 1, v___x_1612_);
lean_ctor_set(v___x_1607_, 0, v___x_1611_);
v___x_1614_ = v___x_1607_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1615_ = l_Nat_reprFast(v___y_1610_);
v___x_1616_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
v___x_1617_ = l_Lean_MessageData_ofFormat(v___x_1616_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 7);
lean_ctor_set(v___x_1602_, 1, v___x_1617_);
lean_ctor_set(v___x_1602_, 0, v___x_1614_);
v___x_1619_ = v___x_1602_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_array_push(v_a_1597_, v___x_1619_);
v_a_1596_ = v_tail_1600_;
v_a_1597_ = v___x_1620_;
goto _start;
}
}
}
v___jp_1624_:
{
if (v___y_1626_ == 0)
{
lean_dec(v___y_1625_);
lean_del_object(v___x_1607_);
lean_dec(v_fst_1604_);
lean_del_object(v___x_1602_);
v_a_1596_ = v_tail_1600_;
goto _start;
}
else
{
v___y_1610_ = v___y_1625_;
goto v___jp_1609_;
}
}
v___jp_1630_:
{
lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = lean_nat_sub(v_snd_1605_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec(v_snd_1605_);
v___x_1633_ = lean_nat_dec_lt(v___x_1629_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_dec(v___x_1632_);
lean_del_object(v___x_1607_);
lean_dec(v_fst_1604_);
lean_del_object(v___x_1602_);
v_a_1596_ = v_tail_1600_;
goto _start;
}
else
{
lean_object* v___x_1635_; 
lean_inc(v_fst_1604_);
lean_inc_ref(v___x_1595_);
v___x_1635_ = l_Lean_getOriginalConstKind_x3f(v___x_1595_, v_fst_1604_);
if (lean_obj_tag(v___x_1635_) == 1)
{
lean_object* v_val_1636_; uint8_t v___x_1637_; 
v_val_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_val_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = lean_unbox(v_val_1636_);
lean_dec(v_val_1636_);
if (v___x_1637_ == 0)
{
v___y_1610_ = v___x_1632_;
goto v___jp_1609_;
}
else
{
v___y_1625_ = v___x_1632_;
v___y_1626_ = v___x_1594_;
goto v___jp_1624_;
}
}
else
{
lean_dec(v___x_1635_);
v___y_1625_ = v___x_1632_;
v___y_1626_ = v___x_1594_;
goto v___jp_1624_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1593_ = stack[0].m_obj;
uint8_t v___x_1594_ = stack[1].m_num;
lean_object* v___x_1595_ = stack[2].m_obj;
lean_object* v_a_1596_ = stack[3].m_obj;
lean_object* v_a_1597_ = stack[4].m_obj;
lean_object* v_res_1642_;
v_res_1642_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(v___x_1593_, v___x_1594_, v___x_1595_, v_a_1596_, v_a_1597_);
stack->m_obj
 = v_res_1642_;
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___boxed(lean_object* v___x_1643_, lean_object* v___x_1644_, lean_object* v___x_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
uint8_t v___x_17816__boxed_1648_; lean_object* v_res_1649_; 
v___x_17816__boxed_1648_ = lean_unbox(v___x_1644_);
v_res_1649_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(v___x_1643_, v___x_17816__boxed_1648_, v___x_1645_, v_a_1646_, v_a_1647_);
lean_dec_ref(v___x_1643_);
return v_res_1649_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__1(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__0));
v___x_1652_ = l_Lean_stringToMessageData(v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__3(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__2));
v___x_1655_ = l_Lean_stringToMessageData(v___x_1654_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__5(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__4));
v___x_1658_ = l_Lean_stringToMessageData(v___x_1657_);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__7(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__6));
v___x_1661_ = l_Lean_stringToMessageData(v___x_1660_);
return v___x_1661_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__9(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__8));
v___x_1664_ = l_Lean_stringToMessageData(v___x_1663_);
return v___x_1664_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__12(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__11));
v___x_1669_ = l_Lean_stringToMessageData(v___x_1668_);
return v___x_1669_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__13(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_box(1);
v___x_1671_ = l_Lean_MessageData_ofFormat(v___x_1670_);
return v___x_1671_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__15(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__14));
v___x_1674_ = l_Lean_stringToMessageData(v___x_1673_);
return v___x_1674_;
}
}
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object* v_type_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_inc_ref(v_type_1675_);
v___x_1681_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed), 6, 1);
lean_closure_set(v___x_1681_, 0, v_type_1675_);
v___x_1682_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_type_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1874_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1685_ = v___x_1682_;
v_isShared_1686_ = v_isSharedCheck_1874_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1874_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; lean_object* v_env_1688_; lean_object* v___x_1689_; uint8_t v_isModule_1690_; 
v___x_1687_ = lean_st_ref_get(v_a_1679_);
v_env_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc_ref(v_env_1688_);
lean_dec(v___x_1687_);
v___x_1689_ = l_Lean_Environment_header(v_env_1688_);
lean_dec_ref(v_env_1688_);
v_isModule_1690_ = lean_ctor_get_uint8(v___x_1689_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1689_);
if (v_isModule_1690_ == 0)
{
lean_object* v___x_1692_; 
lean_dec_ref(v___x_1681_);
if (v_isShared_1686_ == 0)
{
v___x_1692_ = v___x_1685_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1683_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
else
{
lean_object* v___x_1694_; 
lean_del_object(v___x_1685_);
lean_inc_ref(v___x_1681_);
v___x_1694_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v___x_1681_, v_isModule_1690_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1860_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1860_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1860_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_expr_eqv(v_a_1683_, v_a_1695_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v_toCold_1712_; lean_object* v_diag_1713_; lean_object* v_currRecDepth_1714_; lean_object* v_ref_1715_; uint8_t v_suppressElabErrors_1716_; uint8_t v_isRecordingDeps_1717_; lean_object* v_fileName_1718_; lean_object* v_fileMap_1719_; lean_object* v_options_1720_; lean_object* v_currNamespace_1721_; lean_object* v_openDecls_1722_; lean_object* v_initHeartbeats_1723_; lean_object* v_maxHeartbeats_1724_; lean_object* v_quotContext_1725_; lean_object* v_currMacroScope_1726_; lean_object* v_cancelTk_x3f_1727_; lean_object* v_inheritedTraceOptions_1728_; lean_object* v_a_1730_; lean_object* v___y_1776_; uint8_t v___y_1777_; lean_object* v___y_1789_; uint16_t v___y_1790_; lean_object* v_fileName_1791_; lean_object* v_fileMap_1792_; lean_object* v_currNamespace_1793_; lean_object* v_openDecls_1794_; lean_object* v_initHeartbeats_1795_; lean_object* v_maxHeartbeats_1796_; lean_object* v_quotContext_1797_; lean_object* v_currMacroScope_1798_; lean_object* v_cancelTk_x3f_1799_; lean_object* v_inheritedTraceOptions_1800_; lean_object* v_currRecDepth_1801_; lean_object* v_ref_1802_; uint8_t v_suppressElabErrors_1803_; uint8_t v_isRecordingDeps_1804_; lean_object* v___y_1805_; lean_object* v___y_1815_; uint8_t v___y_1816_; uint16_t v___y_1817_; lean_object* v___y_1840_; uint8_t v___y_1841_; uint16_t v___y_1842_; uint8_t v___y_1843_; lean_object* v___y_1845_; 
lean_del_object(v___x_1697_);
v___x_1700_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__1, &l_Lean_Compiler_LCNF_toLCNFType___closed__1_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__1);
v___x_1701_ = l_Lean_MessageData_ofExpr(v_a_1683_);
v___x_1702_ = l_Lean_indentD(v___x_1701_);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1700_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__3, &l_Lean_Compiler_LCNF_toLCNFType___closed__3_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__3);
v___x_1705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = l_Lean_MessageData_ofExpr(v_a_1695_);
v___x_1707_ = l_Lean_indentD(v___x_1706_);
v___x_1708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1705_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__5, &l_Lean_Compiler_LCNF_toLCNFType___closed__5_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__5);
v___x_1710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = lean_st_ref_get(v_a_1677_);
v_toCold_1712_ = lean_ctor_get(v_a_1678_, 0);
v_diag_1713_ = lean_ctor_get(v___x_1711_, 4);
lean_inc_ref(v_diag_1713_);
lean_dec(v___x_1711_);
v_currRecDepth_1714_ = lean_ctor_get(v_a_1678_, 1);
v_ref_1715_ = lean_ctor_get(v_a_1678_, 2);
v_suppressElabErrors_1716_ = lean_ctor_get_uint8(v_a_1678_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1717_ = lean_ctor_get_uint8(v_a_1678_, sizeof(void*)*3 + 3);
v_fileName_1718_ = lean_ctor_get(v_toCold_1712_, 0);
v_fileMap_1719_ = lean_ctor_get(v_toCold_1712_, 1);
v_options_1720_ = lean_ctor_get(v_toCold_1712_, 2);
v_currNamespace_1721_ = lean_ctor_get(v_toCold_1712_, 4);
v_openDecls_1722_ = lean_ctor_get(v_toCold_1712_, 5);
v_initHeartbeats_1723_ = lean_ctor_get(v_toCold_1712_, 6);
v_maxHeartbeats_1724_ = lean_ctor_get(v_toCold_1712_, 7);
v_quotContext_1725_ = lean_ctor_get(v_toCold_1712_, 8);
v_currMacroScope_1726_ = lean_ctor_get(v_toCold_1712_, 9);
v_cancelTk_x3f_1727_ = lean_ctor_get(v_toCold_1712_, 10);
v_inheritedTraceOptions_1728_ = lean_ctor_get(v_toCold_1712_, 11);
if (v_isRecordingDeps_1717_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1720_);
v___x_1855_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(v_options_1720_, v___x_1854_, v_isModule_1690_);
v___y_1845_ = v___x_1855_;
goto v___jp_1844_;
}
else
{
lean_object* v___x_1856_; 
lean_inc_ref(v_options_1720_);
v___x_1856_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_1720_);
v___y_1845_ = v___x_1856_;
goto v___jp_1844_;
}
v___jp_1729_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v_snd_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1752_; 
lean_inc_ref(v_a_1730_);
v___x_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_a_1730_);
v___x_1732_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1677_, v_diag_1713_, v___x_1731_);
lean_dec_ref_known(v___x_1731_, 1);
lean_dec_ref(v___x_1732_);
v_snd_1733_ = lean_ctor_get(v_a_1730_, 1);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_a_1730_);
if (v_isSharedCheck_1752_ == 0)
{
lean_object* v_unused_1753_; 
v_unused_1753_ = lean_ctor_get(v_a_1730_, 0);
lean_dec(v_unused_1753_);
v___x_1735_ = v_a_1730_;
v_isShared_1736_ = v_isSharedCheck_1752_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_snd_1733_);
lean_dec(v_a_1730_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1752_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1737_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__7, &l_Lean_Compiler_LCNF_toLCNFType___closed__7_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__7);
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 7);
lean_ctor_set(v___x_1735_, 0, v___x_1737_);
v___x_1739_ = v___x_1735_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_snd_1733_);
v___x_1739_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
v___x_1740_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__9, &l_Lean_Compiler_LCNF_toLCNFType___closed__9_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__9);
v___x_1741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1739_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v___x_1741_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
v___jp_1754_:
{
lean_object* v___x_1755_; lean_object* v_env_1756_; lean_object* v___x_1757_; lean_object* v_diag_1758_; lean_object* v_unfoldAxiomCounter_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1755_ = lean_st_ref_get(v_a_1679_);
v_env_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc_ref(v_env_1756_);
lean_dec(v___x_1755_);
v___x_1757_ = lean_st_ref_get(v_a_1677_);
v_diag_1758_ = lean_ctor_get(v___x_1757_, 4);
lean_inc_ref(v_diag_1758_);
lean_dec(v___x_1757_);
v_unfoldAxiomCounter_1759_ = lean_ctor_get(v_diag_1758_, 1);
lean_inc_ref(v_unfoldAxiomCounter_1759_);
lean_dec_ref(v_diag_1758_);
v___x_1760_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_unfoldAxiomCounter_1759_);
lean_dec_ref(v_unfoldAxiomCounter_1759_);
v___x_1761_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__10));
v___x_1762_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(v_diag_1713_, v___x_1699_, v_env_1756_, v___x_1760_, v___x_1761_);
v___x_1763_ = l_List_isEmpty___redArg(v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec_ref_known(v___x_1710_, 2);
v___x_1764_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__12, &l_Lean_Compiler_LCNF_toLCNFType___closed__12_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__12);
v___x_1765_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__13, &l_Lean_Compiler_LCNF_toLCNFType___closed__13_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__13);
v___x_1766_ = l_Lean_MessageData_joinSep(v___x_1762_, v___x_1765_);
v___x_1767_ = l_Lean_indentD(v___x_1766_);
v___x_1768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1764_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__15, &l_Lean_Compiler_LCNF_toLCNFType___closed__15_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__15);
v___x_1770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = lean_box(0);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v___x_1770_);
v_a_1730_ = v___x_1772_;
goto v___jp_1729_;
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
lean_dec(v___x_1762_);
v___x_1773_ = lean_box(0);
v___x_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
lean_ctor_set(v___x_1774_, 1, v___x_1710_);
v_a_1730_ = v___x_1774_;
goto v___jp_1729_;
}
}
v___jp_1775_:
{
if (v___y_1777_ == 0)
{
lean_dec_ref(v___y_1776_);
goto v___jp_1754_;
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref_known(v___x_1710_, 2);
v___x_1778_ = lean_box(0);
v___x_1779_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1677_, v_diag_1713_, v___x_1778_);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1786_ == 0)
{
lean_object* v_unused_1787_; 
v_unused_1787_ = lean_ctor_get(v___x_1779_, 0);
lean_dec(v_unused_1787_);
v___x_1781_ = v___x_1779_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_dec(v___x_1779_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set_tag(v___x_1781_, 1);
lean_ctor_set(v___x_1781_, 0, v___y_1776_);
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___y_1776_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
v___jp_1788_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1806_ = l_Lean_maxRecDepth;
v___x_1807_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(v___y_1789_, v___x_1806_);
v___x_1808_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1808_, 0, v_fileName_1791_);
lean_ctor_set(v___x_1808_, 1, v_fileMap_1792_);
lean_ctor_set(v___x_1808_, 2, v___y_1789_);
lean_ctor_set(v___x_1808_, 3, v___x_1807_);
lean_ctor_set(v___x_1808_, 4, v_currNamespace_1793_);
lean_ctor_set(v___x_1808_, 5, v_openDecls_1794_);
lean_ctor_set(v___x_1808_, 6, v_initHeartbeats_1795_);
lean_ctor_set(v___x_1808_, 7, v_maxHeartbeats_1796_);
lean_ctor_set(v___x_1808_, 8, v_quotContext_1797_);
lean_ctor_set(v___x_1808_, 9, v_currMacroScope_1798_);
lean_ctor_set(v___x_1808_, 10, v_cancelTk_x3f_1799_);
lean_ctor_set(v___x_1808_, 11, v_inheritedTraceOptions_1800_);
lean_inc(v_ref_1802_);
lean_inc(v_currRecDepth_1801_);
v___x_1809_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v_currRecDepth_1801_);
lean_ctor_set(v___x_1809_, 2, v_ref_1802_);
lean_ctor_set_uint16(v___x_1809_, sizeof(void*)*3, v___y_1790_);
lean_ctor_set_uint8(v___x_1809_, sizeof(void*)*3 + 2, v_suppressElabErrors_1803_);
lean_ctor_set_uint8(v___x_1809_, sizeof(void*)*3 + 3, v_isRecordingDeps_1804_);
v___x_1810_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v___x_1681_, v_isModule_1690_, v_a_1676_, v_a_1677_, v___x_1809_, v___y_1805_);
lean_dec_ref_known(v___x_1809_, 3);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_dec_ref_known(v___x_1810_, 1);
goto v___jp_1754_;
}
else
{
lean_object* v_a_1811_; uint8_t v___x_1812_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v___x_1812_ = l_Lean_Exception_isInterrupt(v_a_1811_);
if (v___x_1812_ == 0)
{
uint8_t v___x_1813_; 
lean_inc(v_a_1811_);
v___x_1813_ = l_Lean_Exception_isRuntime(v_a_1811_);
v___y_1776_ = v_a_1811_;
v___y_1777_ = v___x_1813_;
goto v___jp_1775_;
}
else
{
v___y_1776_ = v_a_1811_;
v___y_1777_ = v___x_1812_;
goto v___jp_1775_;
}
}
}
v___jp_1814_:
{
lean_object* v___x_1818_; lean_object* v_env_1819_; lean_object* v_nextMacroScope_1820_; lean_object* v_ngen_1821_; lean_object* v_auxDeclNGen_1822_; lean_object* v_traceState_1823_; lean_object* v_recordedDeps_1824_; lean_object* v_messages_1825_; lean_object* v_infoState_1826_; lean_object* v_snapshotTasks_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1837_; 
v___x_1818_ = lean_st_ref_take(v_a_1679_);
v_env_1819_ = lean_ctor_get(v___x_1818_, 0);
v_nextMacroScope_1820_ = lean_ctor_get(v___x_1818_, 1);
v_ngen_1821_ = lean_ctor_get(v___x_1818_, 2);
v_auxDeclNGen_1822_ = lean_ctor_get(v___x_1818_, 3);
v_traceState_1823_ = lean_ctor_get(v___x_1818_, 4);
v_recordedDeps_1824_ = lean_ctor_get(v___x_1818_, 6);
v_messages_1825_ = lean_ctor_get(v___x_1818_, 7);
v_infoState_1826_ = lean_ctor_get(v___x_1818_, 8);
v_snapshotTasks_1827_ = lean_ctor_get(v___x_1818_, 9);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; 
v_unused_1838_ = lean_ctor_get(v___x_1818_, 5);
lean_dec(v_unused_1838_);
v___x_1829_ = v___x_1818_;
v_isShared_1830_ = v_isSharedCheck_1837_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_snapshotTasks_1827_);
lean_inc(v_infoState_1826_);
lean_inc(v_messages_1825_);
lean_inc(v_recordedDeps_1824_);
lean_inc(v_traceState_1823_);
lean_inc(v_auxDeclNGen_1822_);
lean_inc(v_ngen_1821_);
lean_inc(v_nextMacroScope_1820_);
lean_inc(v_env_1819_);
lean_dec(v___x_1818_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1837_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1831_ = l_Lean_Kernel_enableDiag(v_env_1819_, v___y_1816_);
v___x_1832_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 5, v___x_1832_);
lean_ctor_set(v___x_1829_, 0, v___x_1831_);
v___x_1834_ = v___x_1829_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1831_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_nextMacroScope_1820_);
lean_ctor_set(v_reuseFailAlloc_1836_, 2, v_ngen_1821_);
lean_ctor_set(v_reuseFailAlloc_1836_, 3, v_auxDeclNGen_1822_);
lean_ctor_set(v_reuseFailAlloc_1836_, 4, v_traceState_1823_);
lean_ctor_set(v_reuseFailAlloc_1836_, 5, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1836_, 6, v_recordedDeps_1824_);
lean_ctor_set(v_reuseFailAlloc_1836_, 7, v_messages_1825_);
lean_ctor_set(v_reuseFailAlloc_1836_, 8, v_infoState_1826_);
lean_ctor_set(v_reuseFailAlloc_1836_, 9, v_snapshotTasks_1827_);
v___x_1834_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_st_ref_put(v_a_1679_, v___x_1834_);
lean_inc_ref(v_inheritedTraceOptions_1728_);
lean_inc(v_cancelTk_x3f_1727_);
lean_inc(v_currMacroScope_1726_);
lean_inc(v_quotContext_1725_);
lean_inc(v_maxHeartbeats_1724_);
lean_inc(v_initHeartbeats_1723_);
lean_inc(v_openDecls_1722_);
lean_inc(v_currNamespace_1721_);
lean_inc_ref(v_fileMap_1719_);
lean_inc_ref(v_fileName_1718_);
v___y_1789_ = v___y_1815_;
v___y_1790_ = v___y_1817_;
v_fileName_1791_ = v_fileName_1718_;
v_fileMap_1792_ = v_fileMap_1719_;
v_currNamespace_1793_ = v_currNamespace_1721_;
v_openDecls_1794_ = v_openDecls_1722_;
v_initHeartbeats_1795_ = v_initHeartbeats_1723_;
v_maxHeartbeats_1796_ = v_maxHeartbeats_1724_;
v_quotContext_1797_ = v_quotContext_1725_;
v_currMacroScope_1798_ = v_currMacroScope_1726_;
v_cancelTk_x3f_1799_ = v_cancelTk_x3f_1727_;
v_inheritedTraceOptions_1800_ = v_inheritedTraceOptions_1728_;
v_currRecDepth_1801_ = v_currRecDepth_1714_;
v_ref_1802_ = v_ref_1715_;
v_suppressElabErrors_1803_ = v_suppressElabErrors_1716_;
v_isRecordingDeps_1804_ = v_isRecordingDeps_1717_;
v___y_1805_ = v_a_1679_;
goto v___jp_1788_;
}
}
}
v___jp_1839_:
{
if (v___y_1841_ == 0)
{
v___y_1815_ = v___y_1840_;
v___y_1816_ = v___y_1843_;
v___y_1817_ = v___y_1842_;
goto v___jp_1814_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1728_);
lean_inc(v_cancelTk_x3f_1727_);
lean_inc(v_currMacroScope_1726_);
lean_inc(v_quotContext_1725_);
lean_inc(v_maxHeartbeats_1724_);
lean_inc(v_initHeartbeats_1723_);
lean_inc(v_openDecls_1722_);
lean_inc(v_currNamespace_1721_);
lean_inc_ref(v_fileMap_1719_);
lean_inc_ref(v_fileName_1718_);
v___y_1789_ = v___y_1840_;
v___y_1790_ = v___y_1842_;
v_fileName_1791_ = v_fileName_1718_;
v_fileMap_1792_ = v_fileMap_1719_;
v_currNamespace_1793_ = v_currNamespace_1721_;
v_openDecls_1794_ = v_openDecls_1722_;
v_initHeartbeats_1795_ = v_initHeartbeats_1723_;
v_maxHeartbeats_1796_ = v_maxHeartbeats_1724_;
v_quotContext_1797_ = v_quotContext_1725_;
v_currMacroScope_1798_ = v_currMacroScope_1726_;
v_cancelTk_x3f_1799_ = v_cancelTk_x3f_1727_;
v_inheritedTraceOptions_1800_ = v_inheritedTraceOptions_1728_;
v_currRecDepth_1801_ = v_currRecDepth_1714_;
v_ref_1802_ = v_ref_1715_;
v_suppressElabErrors_1803_ = v_suppressElabErrors_1716_;
v_isRecordingDeps_1804_ = v_isRecordingDeps_1717_;
v___y_1805_ = v_a_1679_;
goto v___jp_1788_;
}
}
v___jp_1844_:
{
uint16_t v___x_1846_; lean_object* v___x_1847_; lean_object* v_env_1848_; uint8_t v___x_1849_; uint16_t v___x_1850_; uint16_t v___x_1851_; uint16_t v___x_1852_; uint8_t v___x_1853_; 
v___x_1846_ = l_Lean_OptionFlags_ofOptions(v___y_1845_);
v___x_1847_ = lean_st_ref_get(v_a_1679_);
v_env_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc_ref(v_env_1848_);
lean_dec(v___x_1847_);
v___x_1849_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1848_);
lean_dec_ref(v_env_1848_);
v___x_1850_ = 512;
v___x_1851_ = lean_uint16_land(v___x_1846_, v___x_1850_);
v___x_1852_ = 0;
v___x_1853_ = lean_uint16_dec_eq(v___x_1851_, v___x_1852_);
if (v___x_1853_ == 0)
{
v___y_1840_ = v___y_1845_;
v___y_1841_ = v___x_1849_;
v___y_1842_ = v___x_1846_;
v___y_1843_ = v_isModule_1690_;
goto v___jp_1839_;
}
else
{
if (v___x_1699_ == 0)
{
if (v___x_1849_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_1728_);
lean_inc(v_cancelTk_x3f_1727_);
lean_inc(v_currMacroScope_1726_);
lean_inc(v_quotContext_1725_);
lean_inc(v_maxHeartbeats_1724_);
lean_inc(v_initHeartbeats_1723_);
lean_inc(v_openDecls_1722_);
lean_inc(v_currNamespace_1721_);
lean_inc_ref(v_fileMap_1719_);
lean_inc_ref(v_fileName_1718_);
v___y_1789_ = v___y_1845_;
v___y_1790_ = v___x_1846_;
v_fileName_1791_ = v_fileName_1718_;
v_fileMap_1792_ = v_fileMap_1719_;
v_currNamespace_1793_ = v_currNamespace_1721_;
v_openDecls_1794_ = v_openDecls_1722_;
v_initHeartbeats_1795_ = v_initHeartbeats_1723_;
v_maxHeartbeats_1796_ = v_maxHeartbeats_1724_;
v_quotContext_1797_ = v_quotContext_1725_;
v_currMacroScope_1798_ = v_currMacroScope_1726_;
v_cancelTk_x3f_1799_ = v_cancelTk_x3f_1727_;
v_inheritedTraceOptions_1800_ = v_inheritedTraceOptions_1728_;
v_currRecDepth_1801_ = v_currRecDepth_1714_;
v_ref_1802_ = v_ref_1715_;
v_suppressElabErrors_1803_ = v_suppressElabErrors_1716_;
v_isRecordingDeps_1804_ = v_isRecordingDeps_1717_;
v___y_1805_ = v_a_1679_;
goto v___jp_1788_;
}
else
{
v___y_1815_ = v___y_1845_;
v___y_1816_ = v___x_1699_;
v___y_1817_ = v___x_1846_;
goto v___jp_1814_;
}
}
else
{
v___y_1840_ = v___y_1845_;
v___y_1841_ = v___x_1849_;
v___y_1842_ = v___x_1846_;
v___y_1843_ = v___x_1699_;
goto v___jp_1839_;
}
}
}
}
else
{
lean_object* v___x_1858_; 
lean_dec(v_a_1695_);
lean_dec_ref(v___x_1681_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v_a_1683_);
v___x_1858_ = v___x_1697_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1683_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
else
{
lean_object* v_a_1861_; uint8_t v___y_1863_; uint8_t v___x_1872_; 
lean_dec_ref(v___x_1681_);
v_a_1861_ = lean_ctor_get(v___x_1694_, 0);
v___x_1872_ = l_Lean_Exception_isInterrupt(v_a_1861_);
if (v___x_1872_ == 0)
{
uint8_t v___x_1873_; 
lean_inc(v_a_1861_);
v___x_1873_ = l_Lean_Exception_isRuntime(v_a_1861_);
v___y_1863_ = v___x_1873_;
goto v___jp_1862_;
}
else
{
v___y_1863_ = v___x_1872_;
goto v___jp_1862_;
}
v___jp_1862_:
{
if (v___y_1863_ == 0)
{
lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1870_ == 0)
{
lean_object* v_unused_1871_; 
v_unused_1871_ = lean_ctor_get(v___x_1694_, 0);
lean_dec(v_unused_1871_);
v___x_1865_ = v___x_1694_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_dec(v___x_1694_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set_tag(v___x_1865_, 0);
lean_ctor_set(v___x_1865_, 0, v_a_1683_);
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1683_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
else
{
lean_dec(v_a_1683_);
return v___x_1694_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1681_);
return v___x_1682_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_toLCNFType_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1675_ = stack[0].m_obj;
lean_object* v_a_1676_ = stack[1].m_obj;
lean_object* v_a_1677_ = stack[2].m_obj;
lean_object* v_a_1678_ = stack[3].m_obj;
lean_object* v_a_1679_ = stack[4].m_obj;
lean_object* v_res_1875_;
v_res_1875_ = l_Lean_Compiler_LCNF_toLCNFType(v_type_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
stack->m_obj
 = v_res_1875_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___boxed(lean_object* v_type_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Compiler_LCNF_toLCNFType(v_type_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(lean_object* v_00_u03b2_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_x_1884_, v_x_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___boxed(lean_object* v_00_u03b2_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(v_00_u03b2_1887_, v_x_1888_, v_x_1889_);
lean_dec(v_x_1889_);
lean_dec_ref(v_x_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(lean_object* v_00_u03b2_1891_, lean_object* v_m_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_m_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___boxed(lean_object* v_00_u03b2_1894_, lean_object* v_m_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(v_00_u03b2_1894_, v_m_1895_);
lean_dec_ref(v_m_1895_);
return v_res_1896_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1(lean_object* v_00_u03b2_1897_, lean_object* v_x_1898_, size_t v_x_1899_, lean_object* v_x_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1898_, v_x_1899_, v_x_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1898_ = stack[1].m_obj;
size_t v_x_1899_ = stack[2].m_num;
lean_object* v_x_1900_ = stack[3].m_obj;
lean_object* v_res_1902_;
v_res_1902_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1(lean_box(0), v_x_1898_, v_x_1899_, v_x_1900_);
stack->m_obj
 = v_res_1902_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1903_, lean_object* v_x_1904_, lean_object* v_x_1905_, lean_object* v_x_1906_){
_start:
{
size_t v_x_18550__boxed_1907_; lean_object* v_res_1908_; 
v_x_18550__boxed_1907_ = lean_unbox_usize(v_x_1905_);
lean_dec(v_x_1905_);
v_res_1908_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1(v_00_u03b2_1903_, v_x_1904_, v_x_18550__boxed_1907_, v_x_1906_);
lean_dec(v_x_1906_);
lean_dec_ref(v_x_1904_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3(lean_object* v_00_u03c3_1909_, lean_object* v_00_u03b2_1910_, lean_object* v_map_1911_, lean_object* v_f_1912_, lean_object* v_init_1913_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_map_1911_, v_f_1912_, v_init_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1915_, lean_object* v_00_u03b2_1916_, lean_object* v_map_1917_, lean_object* v_f_1918_, lean_object* v_init_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3(v_00_u03c3_1915_, v_00_u03b2_1916_, v_map_1917_, v_f_1918_, v_init_1919_);
lean_dec_ref(v_map_1917_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1921_, lean_object* v_keys_1922_, lean_object* v_vals_1923_, lean_object* v_heq_1924_, lean_object* v_i_1925_, lean_object* v_k_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__3___redArg(v_keys_1922_, v_vals_1923_, v_i_1925_, v_k_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1928_, lean_object* v_keys_1929_, lean_object* v_vals_1930_, lean_object* v_heq_1931_, lean_object* v_i_1932_, lean_object* v_k_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__3(v_00_u03b2_1928_, v_keys_1929_, v_vals_1930_, v_heq_1931_, v_i_1932_, v_k_1933_);
lean_dec(v_k_1933_);
lean_dec_ref(v_vals_1930_);
lean_dec_ref(v_keys_1929_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6___redArg(lean_object* v_map_1935_, lean_object* v_f_1936_, lean_object* v_init_1937_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10___redArg(v_f_1936_, v_map_1935_, v_init_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_map_1939_, lean_object* v_f_1940_, lean_object* v_init_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6___redArg(v_map_1939_, v_f_1940_, v_init_1941_);
lean_dec_ref(v_map_1939_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1943_, lean_object* v_00_u03b2_1944_, lean_object* v_map_1945_, lean_object* v_f_1946_, lean_object* v_init_1947_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10___redArg(v_f_1946_, v_map_1945_, v_init_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1949_, lean_object* v_00_u03b2_1950_, lean_object* v_map_1951_, lean_object* v_f_1952_, lean_object* v_init_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6(v_00_u03c3_1949_, v_00_u03b2_1950_, v_map_1951_, v_f_1952_, v_init_1953_);
lean_dec_ref(v_map_1951_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10(lean_object* v_00_u03c3_1955_, lean_object* v_00_u03b1_1956_, lean_object* v_00_u03b2_1957_, lean_object* v_f_1958_, lean_object* v_x_1959_, lean_object* v_x_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10___redArg(v_f_1958_, v_x_1959_, v_x_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03c3_1962_, lean_object* v_00_u03b1_1963_, lean_object* v_00_u03b2_1964_, lean_object* v_f_1965_, lean_object* v_x_1966_, lean_object* v_x_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10(v_00_u03c3_1962_, v_00_u03b1_1963_, v_00_u03b2_1964_, v_f_1965_, v_x_1966_, v_x_1967_);
lean_dec_ref(v_x_1966_);
return v_res_1968_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11(lean_object* v_00_u03b1_1969_, lean_object* v_00_u03b2_1970_, lean_object* v_00_u03c3_1971_, lean_object* v_f_1972_, lean_object* v_as_1973_, size_t v_i_1974_, size_t v_stop_1975_, lean_object* v_b_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11___redArg(v_f_1972_, v_as_1973_, v_i_1974_, v_stop_1975_, v_b_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1972_ = stack[3].m_obj;
lean_object* v_as_1973_ = stack[4].m_obj;
size_t v_i_1974_ = stack[5].m_num;
size_t v_stop_1975_ = stack[6].m_num;
lean_object* v_b_1976_ = stack[7].m_obj;
lean_object* v_res_1978_;
v_res_1978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11(lean_box(0), lean_box(0), lean_box(0), v_f_1972_, v_as_1973_, v_i_1974_, v_stop_1975_, v_b_1976_);
stack->m_obj
 = v_res_1978_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11___boxed(lean_object* v_00_u03b1_1979_, lean_object* v_00_u03b2_1980_, lean_object* v_00_u03c3_1981_, lean_object* v_f_1982_, lean_object* v_as_1983_, lean_object* v_i_1984_, lean_object* v_stop_1985_, lean_object* v_b_1986_){
_start:
{
size_t v_i_boxed_1987_; size_t v_stop_boxed_1988_; lean_object* v_res_1989_; 
v_i_boxed_1987_ = lean_unbox_usize(v_i_1984_);
lean_dec(v_i_1984_);
v_stop_boxed_1988_ = lean_unbox_usize(v_stop_1985_);
lean_dec(v_stop_1985_);
v_res_1989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__11(v_00_u03b1_1979_, v_00_u03b2_1980_, v_00_u03c3_1981_, v_f_1982_, v_as_1983_, v_i_boxed_1987_, v_stop_boxed_1988_, v_b_1986_);
lean_dec_ref(v_as_1983_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__12(lean_object* v_00_u03c3_1990_, lean_object* v_00_u03b1_1991_, lean_object* v_00_u03b2_1992_, lean_object* v_f_1993_, lean_object* v_keys_1994_, lean_object* v_vals_1995_, lean_object* v_heq_1996_, lean_object* v_i_1997_, lean_object* v_acc_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__12___redArg(v_f_1993_, v_keys_1994_, v_vals_1995_, v_i_1997_, v_acc_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__12___boxed(lean_object* v_00_u03c3_2000_, lean_object* v_00_u03b1_2001_, lean_object* v_00_u03b2_2002_, lean_object* v_f_2003_, lean_object* v_keys_2004_, lean_object* v_vals_2005_, lean_object* v_heq_2006_, lean_object* v_i_2007_, lean_object* v_acc_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__6_spec__10_spec__12(v_00_u03c3_2000_, v_00_u03b1_2001_, v_00_u03b2_2002_, v_f_2003_, v_keys_2004_, v_vals_2005_, v_heq_2006_, v_i_2007_, v_acc_2008_);
lean_dec_ref(v_vals_2005_);
lean_dec_ref(v_keys_2004_);
return v_res_2009_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
v___x_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
return v___x_2011_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f(lean_object* v_a_2014_, lean_object* v_b_2015_){
_start:
{
lean_object* v___y_2019_; uint8_t v___y_2022_; uint8_t v___x_2096_; 
v___x_2096_ = l_Lean_Expr_isErased(v_a_2014_);
if (v___x_2096_ == 0)
{
uint8_t v___x_2097_; 
v___x_2097_ = l_Lean_Expr_isErased(v_b_2015_);
v___y_2022_ = v___x_2097_;
goto v___jp_2021_;
}
else
{
v___y_2022_ = v___x_2096_;
goto v___jp_2021_;
}
v___jp_2016_:
{
lean_object* v___x_2017_; 
v___x_2017_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_2017_;
}
v___jp_2018_:
{
if (lean_obj_tag(v___y_2019_) == 0)
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_2020_;
}
else
{
return v___y_2019_;
}
}
v___jp_2021_:
{
if (v___y_2022_ == 0)
{
uint8_t v___x_2023_; 
v___x_2023_ = lean_expr_eqv(v_a_2014_, v_b_2015_);
if (v___x_2023_ == 0)
{
lean_object* v_a_x27_2024_; lean_object* v_b_x27_2025_; uint8_t v___x_2026_; 
lean_inc_ref(v_a_2014_);
v_a_x27_2024_ = l_Lean_Expr_headBeta(v_a_2014_);
lean_inc_ref(v_b_2015_);
v_b_x27_2025_ = l_Lean_Expr_headBeta(v_b_2015_);
v___x_2026_ = lean_expr_eqv(v_a_2014_, v_a_x27_2024_);
if (v___x_2026_ == 0)
{
lean_dec_ref(v_b_2015_);
lean_dec_ref(v_a_2014_);
v_a_2014_ = v_a_x27_2024_;
v_b_2015_ = v_b_x27_2025_;
goto _start;
}
else
{
if (v___x_2023_ == 0)
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_expr_eqv(v_b_2015_, v_b_x27_2025_);
if (v___x_2028_ == 0)
{
lean_dec_ref(v_b_2015_);
lean_dec_ref(v_a_2014_);
v_a_2014_ = v_a_x27_2024_;
v_b_2015_ = v_b_x27_2025_;
goto _start;
}
else
{
if (v___x_2023_ == 0)
{
lean_dec_ref(v_b_x27_2025_);
lean_dec_ref(v_a_x27_2024_);
switch(lean_obj_tag(v_a_2014_))
{
case 10:
{
lean_object* v_expr_2030_; 
v_expr_2030_ = lean_ctor_get(v_a_2014_, 1);
lean_inc_ref(v_expr_2030_);
lean_dec_ref_known(v_a_2014_, 2);
v_a_2014_ = v_expr_2030_;
goto _start;
}
case 5:
{
switch(lean_obj_tag(v_b_2015_))
{
case 10:
{
lean_object* v_expr_2032_; 
v_expr_2032_ = lean_ctor_get(v_b_2015_, 1);
lean_inc_ref(v_expr_2032_);
lean_dec_ref_known(v_b_2015_, 2);
v_b_2015_ = v_expr_2032_;
goto _start;
}
case 5:
{
lean_object* v_fn_2034_; lean_object* v_arg_2035_; lean_object* v_fn_2036_; lean_object* v_arg_2037_; lean_object* v___x_2038_; 
v_fn_2034_ = lean_ctor_get(v_a_2014_, 0);
lean_inc_ref(v_fn_2034_);
v_arg_2035_ = lean_ctor_get(v_a_2014_, 1);
lean_inc_ref(v_arg_2035_);
lean_dec_ref_known(v_a_2014_, 2);
v_fn_2036_ = lean_ctor_get(v_b_2015_, 0);
lean_inc_ref(v_fn_2036_);
v_arg_2037_ = lean_ctor_get(v_b_2015_, 1);
lean_inc_ref(v_arg_2037_);
lean_dec_ref_known(v_b_2015_, 2);
v___x_2038_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_fn_2034_, v_fn_2036_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_dec_ref(v_arg_2037_);
lean_dec_ref(v_arg_2035_);
v___y_2019_ = v___x_2038_;
goto v___jp_2018_;
}
else
{
lean_object* v_val_2039_; lean_object* v___x_2040_; 
v_val_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_val_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___x_2040_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_arg_2035_, v_arg_2037_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_dec(v_val_2039_);
v___y_2019_ = v___x_2040_;
goto v___jp_2018_;
}
else
{
lean_object* v_val_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2049_; 
v_val_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2049_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_val_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2049_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2045_ = l_Lean_Expr_app___override(v_val_2039_, v_val_2041_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2045_);
v___x_2047_ = v___x_2043_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_a_2014_, 2);
lean_dec_ref(v_b_2015_);
goto v___jp_2016_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_2015_))
{
case 10:
{
lean_object* v_expr_2050_; 
v_expr_2050_ = lean_ctor_get(v_b_2015_, 1);
lean_inc_ref(v_expr_2050_);
lean_dec_ref_known(v_b_2015_, 2);
v_b_2015_ = v_expr_2050_;
goto _start;
}
case 7:
{
lean_object* v_binderName_2052_; lean_object* v_binderType_2053_; lean_object* v_body_2054_; lean_object* v_binderType_2055_; lean_object* v_body_2056_; lean_object* v___x_2057_; 
v_binderName_2052_ = lean_ctor_get(v_a_2014_, 0);
lean_inc(v_binderName_2052_);
v_binderType_2053_ = lean_ctor_get(v_a_2014_, 1);
lean_inc_ref(v_binderType_2053_);
v_body_2054_ = lean_ctor_get(v_a_2014_, 2);
lean_inc_ref(v_body_2054_);
lean_dec_ref_known(v_a_2014_, 3);
v_binderType_2055_ = lean_ctor_get(v_b_2015_, 1);
lean_inc_ref(v_binderType_2055_);
v_body_2056_ = lean_ctor_get(v_b_2015_, 2);
lean_inc_ref(v_body_2056_);
lean_dec_ref_known(v_b_2015_, 3);
v___x_2057_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_binderType_2053_, v_binderType_2055_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_dec_ref(v_body_2056_);
lean_dec_ref(v_body_2054_);
lean_dec(v_binderName_2052_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_2058_;
}
else
{
return v___x_2057_;
}
}
else
{
lean_object* v_val_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2069_; 
v_val_2059_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2061_ = v___x_2057_;
v_isShared_2062_ = v_isSharedCheck_2069_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_val_2059_);
lean_dec(v___x_2057_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2069_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2063_ = l_Lean_Compiler_LCNF_joinTypes(v_body_2054_, v_body_2056_);
v___x_2064_ = 0;
v___x_2065_ = l_Lean_Expr_forallE___override(v_binderName_2052_, v_val_2059_, v___x_2063_, v___x_2064_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2065_);
v___x_2067_ = v___x_2061_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
default: 
{
lean_dec_ref_known(v_a_2014_, 3);
lean_dec_ref(v_b_2015_);
goto v___jp_2016_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_2015_))
{
case 10:
{
lean_object* v_expr_2070_; 
v_expr_2070_ = lean_ctor_get(v_b_2015_, 1);
lean_inc_ref(v_expr_2070_);
lean_dec_ref_known(v_b_2015_, 2);
v_b_2015_ = v_expr_2070_;
goto _start;
}
case 6:
{
lean_object* v_binderName_2072_; lean_object* v_binderType_2073_; lean_object* v_body_2074_; lean_object* v_binderType_2075_; lean_object* v_body_2076_; lean_object* v___x_2077_; 
v_binderName_2072_ = lean_ctor_get(v_a_2014_, 0);
lean_inc(v_binderName_2072_);
v_binderType_2073_ = lean_ctor_get(v_a_2014_, 1);
lean_inc_ref(v_binderType_2073_);
v_body_2074_ = lean_ctor_get(v_a_2014_, 2);
lean_inc_ref(v_body_2074_);
lean_dec_ref_known(v_a_2014_, 3);
v_binderType_2075_ = lean_ctor_get(v_b_2015_, 1);
lean_inc_ref(v_binderType_2075_);
v_body_2076_ = lean_ctor_get(v_b_2015_, 2);
lean_inc_ref(v_body_2076_);
lean_dec_ref_known(v_b_2015_, 3);
v___x_2077_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_binderType_2073_, v_binderType_2075_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_dec_ref(v_body_2076_);
lean_dec_ref(v_body_2074_);
lean_dec(v_binderName_2072_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_2078_;
}
else
{
return v___x_2077_;
}
}
else
{
lean_object* v_val_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2089_; 
v_val_2079_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2081_ = v___x_2077_;
v_isShared_2082_ = v_isSharedCheck_2089_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_val_2079_);
lean_dec(v___x_2077_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2089_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; uint8_t v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2083_ = l_Lean_Compiler_LCNF_joinTypes(v_body_2074_, v_body_2076_);
v___x_2084_ = 0;
v___x_2085_ = l_Lean_Expr_lam___override(v_binderName_2072_, v_val_2079_, v___x_2083_, v___x_2084_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2085_);
v___x_2087_ = v___x_2081_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
default: 
{
lean_dec_ref_known(v_a_2014_, 3);
lean_dec_ref(v_b_2015_);
goto v___jp_2016_;
}
}
}
default: 
{
if (lean_obj_tag(v_b_2015_) == 10)
{
lean_object* v_expr_2090_; 
v_expr_2090_ = lean_ctor_get(v_b_2015_, 1);
lean_inc_ref(v_expr_2090_);
lean_dec_ref_known(v_b_2015_, 2);
v_b_2015_ = v_expr_2090_;
goto _start;
}
else
{
lean_dec_ref(v_b_2015_);
lean_dec_ref(v_a_2014_);
goto v___jp_2016_;
}
}
}
}
else
{
lean_dec_ref(v_b_2015_);
lean_dec_ref(v_a_2014_);
v_a_2014_ = v_a_x27_2024_;
v_b_2015_ = v_b_x27_2025_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_b_2015_);
lean_dec_ref(v_a_2014_);
v_a_2014_ = v_a_x27_2024_;
v_b_2015_ = v_b_x27_2025_;
goto _start;
}
}
}
else
{
lean_object* v___x_2094_; 
lean_dec_ref(v_b_2015_);
v___x_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2094_, 0, v_a_2014_);
return v___x_2094_;
}
}
else
{
lean_object* v___x_2095_; 
lean_dec_ref(v_b_2015_);
lean_dec_ref(v_a_2014_);
v___x_2095_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1);
return v___x_2095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object* v_a_2098_, lean_object* v_b_2099_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_a_2098_, v_b_2099_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
return v___x_2101_;
}
else
{
lean_object* v_val_2102_; 
v_val_2102_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_val_2102_);
lean_dec_ref_known(v___x_2100_, 1);
return v_val_2102_;
}
}
}
uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object* v_type_2103_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lean_Expr_headBeta(v_type_2103_);
switch(lean_obj_tag(v___x_2104_))
{
case 3:
{
uint8_t v___x_2105_; 
lean_dec_ref_known(v___x_2104_, 1);
v___x_2105_ = 1;
return v___x_2105_;
}
case 7:
{
lean_object* v_body_2106_; 
v_body_2106_ = lean_ctor_get(v___x_2104_, 2);
lean_inc_ref(v_body_2106_);
lean_dec_ref_known(v___x_2104_, 3);
v_type_2103_ = v_body_2106_;
goto _start;
}
default: 
{
uint8_t v___x_2108_; 
lean_dec_ref(v___x_2104_);
v___x_2108_ = 0;
return v___x_2108_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isTypeFormerType_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2103_ = stack[0].m_obj;
uint8_t v_res_2109_;
v_res_2109_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_2103_);
stack->m_num = v_res_2109_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTypeFormerType___boxed(lean_object* v_type_2110_){
_start:
{
uint8_t v_res_2111_; lean_object* v_r_2112_; 
v_res_2111_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_2110_);
v_r_2112_ = lean_box(v_res_2111_);
return v_r_2112_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(lean_object* v_msgData_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2117_; lean_object* v_toCold_2118_; lean_object* v_env_2119_; lean_object* v_options_2120_; uint8_t v___x_2121_; lean_object* v_env_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2117_ = lean_st_ref_get(v___y_2115_);
v_toCold_2118_ = lean_ctor_get(v___y_2114_, 0);
v_env_2119_ = lean_ctor_get(v___x_2117_, 0);
lean_inc_ref(v_env_2119_);
lean_dec(v___x_2117_);
v_options_2120_ = lean_ctor_get(v_toCold_2118_, 2);
v___x_2121_ = 0;
v_env_2122_ = l_Lean_Environment_setRecordingDeps(v_env_2119_, v___x_2121_);
v___x_2123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_2124_ = lean_unsigned_to_nat(32u);
v___x_2125_ = lean_mk_empty_array_with_capacity(v___x_2124_);
lean_dec_ref(v___x_2125_);
v___x_2126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_2120_);
v___x_2127_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2127_, 0, v_env_2122_);
lean_ctor_set(v___x_2127_, 1, v___x_2123_);
lean_ctor_set(v___x_2127_, 2, v___x_2126_);
lean_ctor_set(v___x_2127_, 3, v_options_2120_);
v___x_2128_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v_msgData_2113_);
v___x_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2113_ = stack[0].m_obj;
lean_object* v___y_2114_ = stack[1].m_obj;
lean_object* v___y_2115_ = stack[2].m_obj;
lean_object* v_res_2130_;
v_res_2130_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msgData_2113_, v___y_2114_, v___y_2115_);
stack->m_obj
 = v_res_2130_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0___boxed(lean_object* v_msgData_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msgData_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
return v_res_2135_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(lean_object* v_msg_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_ref_2140_; lean_object* v___x_2141_; lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2150_; 
v_ref_2140_ = lean_ctor_get(v___y_2137_, 2);
v___x_2141_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msg_2136_, v___y_2137_, v___y_2138_);
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2144_ = v___x_2141_;
v_isShared_2145_ = v_isSharedCheck_2150_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2150_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
lean_inc(v_ref_2140_);
v___x_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2146_, 0, v_ref_2140_);
lean_ctor_set(v___x_2146_, 1, v_a_2142_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set_tag(v___x_2144_, 1);
lean_ctor_set(v___x_2144_, 0, v___x_2146_);
v___x_2148_ = v___x_2144_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2136_ = stack[0].m_obj;
lean_object* v___y_2137_ = stack[1].m_obj;
lean_object* v___y_2138_ = stack[2].m_obj;
lean_object* v_res_2151_;
v_res_2151_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_2136_, v___y_2137_, v___y_2138_);
stack->m_obj
 = v_res_2151_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg___boxed(lean_object* v_msg_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
return v_res_2156_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__0));
v___x_2159_ = l_Lean_stringToMessageData(v___x_2158_);
return v___x_2159_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(lean_object* v_ps_2160_, lean_object* v_i_2161_, lean_object* v_type_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = lean_array_get_size(v_ps_2160_);
v___x_2167_ = lean_nat_dec_lt(v_i_2161_, v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; 
lean_dec(v_i_2161_);
v___x_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2168_, 0, v_type_2162_);
return v___x_2168_;
}
else
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_Expr_headBeta(v_type_2162_);
if (lean_obj_tag(v___x_2169_) == 7)
{
lean_object* v_body_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_body_2170_ = lean_ctor_get(v___x_2169_, 2);
lean_inc_ref(v_body_2170_);
lean_dec_ref_known(v___x_2169_, 3);
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_add(v_i_2161_, v___x_2171_);
v___x_2173_ = lean_array_fget_borrowed(v_ps_2160_, v_i_2161_);
lean_dec(v_i_2161_);
v___x_2174_ = lean_expr_instantiate1(v_body_2170_, v___x_2173_);
lean_dec_ref(v_body_2170_);
v_i_2161_ = v___x_2172_;
v_type_2162_ = v___x_2174_;
goto _start;
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_dec_ref(v___x_2169_);
lean_dec(v_i_2161_);
v___x_2176_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1);
v___x_2177_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v___x_2176_, v_a_2163_, v_a_2164_);
return v___x_2177_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_ps_2160_ = stack[0].m_obj;
lean_object* v_i_2161_ = stack[1].m_obj;
lean_object* v_type_2162_ = stack[2].m_obj;
lean_object* v_a_2163_ = stack[3].m_obj;
lean_object* v_a_2164_ = stack[4].m_obj;
lean_object* v_res_2178_;
v_res_2178_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(v_ps_2160_, v_i_2161_, v_type_2162_, v_a_2163_, v_a_2164_);
stack->m_obj
 = v_res_2178_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___boxed(lean_object* v_ps_2179_, lean_object* v_i_2180_, lean_object* v_type_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(v_ps_2179_, v_i_2180_, v_type_2181_, v_a_2182_, v_a_2183_);
lean_dec(v_a_2183_);
lean_dec_ref(v_a_2182_);
lean_dec_ref(v_ps_2179_);
return v_res_2185_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(lean_object* v_00_u03b1_2186_, lean_object* v_msg_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_2187_, v___y_2188_, v___y_2189_);
return v___x_2191_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2187_ = stack[1].m_obj;
lean_object* v___y_2188_ = stack[2].m_obj;
lean_object* v___y_2189_ = stack[3].m_obj;
lean_object* v_res_2192_;
v_res_2192_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(lean_box(0), v_msg_2187_, v___y_2188_, v___y_2189_);
stack->m_obj
 = v_res_2192_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___boxed(lean_object* v_00_u03b1_2193_, lean_object* v_msg_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(v_00_u03b1_2193_, v_msg_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter___redArg(lean_object* v_e_2199_, lean_object* v_h__1_2200_, lean_object* v_h__2_2201_){
_start:
{
if (lean_obj_tag(v_e_2199_) == 7)
{
lean_object* v_binderName_2202_; lean_object* v_binderType_2203_; lean_object* v_body_2204_; uint8_t v_binderInfo_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec(v_h__2_2201_);
v_binderName_2202_ = lean_ctor_get(v_e_2199_, 0);
lean_inc(v_binderName_2202_);
v_binderType_2203_ = lean_ctor_get(v_e_2199_, 1);
lean_inc_ref(v_binderType_2203_);
v_body_2204_ = lean_ctor_get(v_e_2199_, 2);
lean_inc_ref(v_body_2204_);
v_binderInfo_2205_ = lean_ctor_get_uint8(v_e_2199_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2199_, 3);
v___x_2206_ = lean_box(v_binderInfo_2205_);
v___x_2207_ = lean_apply_4(v_h__1_2200_, v_binderName_2202_, v_binderType_2203_, v_body_2204_, v___x_2206_);
return v___x_2207_;
}
else
{
lean_object* v___x_2208_; 
lean_dec(v_h__1_2200_);
v___x_2208_ = lean_apply_2(v_h__2_2201_, v_e_2199_, lean_box(0));
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter(lean_object* v_motive_2209_, lean_object* v_e_2210_, lean_object* v_h__1_2211_, lean_object* v_h__2_2212_){
_start:
{
if (lean_obj_tag(v_e_2210_) == 7)
{
lean_object* v_binderName_2213_; lean_object* v_binderType_2214_; lean_object* v_body_2215_; uint8_t v_binderInfo_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec(v_h__2_2212_);
v_binderName_2213_ = lean_ctor_get(v_e_2210_, 0);
lean_inc(v_binderName_2213_);
v_binderType_2214_ = lean_ctor_get(v_e_2210_, 1);
lean_inc_ref(v_binderType_2214_);
v_body_2215_ = lean_ctor_get(v_e_2210_, 2);
lean_inc_ref(v_body_2215_);
v_binderInfo_2216_ = lean_ctor_get_uint8(v_e_2210_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2210_, 3);
v___x_2217_ = lean_box(v_binderInfo_2216_);
v___x_2218_ = lean_apply_4(v_h__1_2211_, v_binderName_2213_, v_binderType_2214_, v_body_2215_, v___x_2217_);
return v___x_2218_;
}
else
{
lean_object* v___x_2219_; 
lean_dec(v_h__1_2211_);
v___x_2219_ = lean_apply_2(v_h__2_2212_, v_e_2210_, lean_box(0));
return v___x_2219_;
}
}
}
lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object* v_type_2220_, lean_object* v_ps_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(v_ps_2221_, v___x_2225_, v_type_2220_, v_a_2222_, v_a_2223_);
return v___x_2226_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instantiateForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2220_ = stack[0].m_obj;
lean_object* v_ps_2221_ = stack[1].m_obj;
lean_object* v_a_2222_ = stack[2].m_obj;
lean_object* v_a_2223_ = stack[3].m_obj;
lean_object* v_res_2227_;
v_res_2227_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_2220_, v_ps_2221_, v_a_2222_, v_a_2223_);
stack->m_obj
 = v_res_2227_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall___boxed(lean_object* v_type_2228_, lean_object* v_ps_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_2228_, v_ps_2229_, v_a_2230_, v_a_2231_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec_ref(v_ps_2229_);
return v_res_2233_;
}
}
uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object* v_type_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_Expr_headBeta(v_type_2234_);
switch(lean_obj_tag(v___x_2235_))
{
case 3:
{
lean_object* v_u_2236_; 
v_u_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_u_2236_);
lean_dec_ref_known(v___x_2235_, 1);
if (lean_obj_tag(v_u_2236_) == 0)
{
uint8_t v___x_2237_; 
v___x_2237_ = 1;
return v___x_2237_;
}
else
{
uint8_t v___x_2238_; 
lean_dec(v_u_2236_);
v___x_2238_ = 0;
return v___x_2238_;
}
}
case 7:
{
lean_object* v_body_2239_; 
v_body_2239_ = lean_ctor_get(v___x_2235_, 2);
lean_inc_ref(v_body_2239_);
lean_dec_ref_known(v___x_2235_, 3);
v_type_2234_ = v_body_2239_;
goto _start;
}
default: 
{
uint8_t v___x_2241_; 
lean_dec_ref(v___x_2235_);
v___x_2241_ = 0;
return v___x_2241_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isPredicateType_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2234_ = stack[0].m_obj;
uint8_t v_res_2242_;
v_res_2242_ = l_Lean_Compiler_LCNF_isPredicateType(v_type_2234_);
stack->m_num = v_res_2242_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPredicateType___boxed(lean_object* v_type_2243_){
_start:
{
uint8_t v_res_2244_; lean_object* v_r_2245_; 
v_res_2244_ = l_Lean_Compiler_LCNF_isPredicateType(v_type_2243_);
v_r_2245_ = lean_box(v_res_2244_);
return v_r_2245_;
}
}
uint8_t l_Lean_Compiler_LCNF_maybeTypeFormerType(lean_object* v_type_2246_){
_start:
{
lean_object* v___x_2247_; 
lean_inc_ref(v_type_2246_);
v___x_2247_ = l_Lean_Expr_headBeta(v_type_2246_);
switch(lean_obj_tag(v___x_2247_))
{
case 3:
{
uint8_t v___x_2248_; 
lean_dec_ref_known(v___x_2247_, 1);
lean_dec_ref(v_type_2246_);
v___x_2248_ = 1;
return v___x_2248_;
}
case 7:
{
lean_object* v_body_2249_; 
lean_dec_ref(v_type_2246_);
v_body_2249_ = lean_ctor_get(v___x_2247_, 2);
lean_inc_ref(v_body_2249_);
lean_dec_ref_known(v___x_2247_, 3);
v_type_2246_ = v_body_2249_;
goto _start;
}
default: 
{
uint8_t v___x_2251_; 
lean_dec_ref(v___x_2247_);
v___x_2251_ = l_Lean_Expr_isErased(v_type_2246_);
lean_dec_ref(v_type_2246_);
return v___x_2251_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_maybeTypeFormerType_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2246_ = stack[0].m_obj;
uint8_t v_res_2252_;
v_res_2252_ = l_Lean_Compiler_LCNF_maybeTypeFormerType(v_type_2246_);
stack->m_num = v_res_2252_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_maybeTypeFormerType___boxed(lean_object* v_type_2253_){
_start:
{
uint8_t v_res_2254_; lean_object* v_r_2255_; 
v_res_2254_ = l_Lean_Compiler_LCNF_maybeTypeFormerType(v_type_2253_);
v_r_2255_ = lean_box(v_res_2254_);
return v_r_2255_;
}
}
lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg(lean_object* v_type_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_Expr_getAppFn(v_type_2256_);
if (lean_obj_tag(v___x_2259_) == 4)
{
lean_object* v_declName_2260_; lean_object* v___x_2261_; lean_object* v_env_2262_; uint8_t v___x_2263_; 
v_declName_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_declName_2260_);
lean_dec_ref_known(v___x_2259_, 2);
v___x_2261_ = lean_st_ref_get(v_a_2257_);
v_env_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc_ref(v_env_2262_);
lean_dec(v___x_2261_);
v___x_2263_ = l_Lean_isClass(v_env_2262_, v_declName_2260_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
lean_dec(v_declName_2260_);
v___x_2264_ = lean_box(0);
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2266_, 0, v_declName_2260_);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
return v___x_2267_;
}
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
lean_dec_ref(v___x_2259_);
v___x_2268_ = lean_box(0);
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
return v___x_2269_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isClass_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2256_ = stack[0].m_obj;
lean_object* v_a_2257_ = stack[1].m_obj;
lean_object* v_res_2270_;
v_res_2270_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2256_, v_a_2257_);
stack->m_obj
 = v_res_2270_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg___boxed(lean_object* v_type_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2271_, v_a_2272_);
lean_dec(v_a_2272_);
lean_dec_ref(v_type_2271_);
return v_res_2274_;
}
}
lean_object* l_Lean_Compiler_LCNF_isClass_x3f(lean_object* v_type_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2275_, v_a_2277_);
return v___x_2279_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isClass_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2275_ = stack[0].m_obj;
lean_object* v_a_2276_ = stack[1].m_obj;
lean_object* v_a_2277_ = stack[2].m_obj;
lean_object* v_res_2280_;
v_res_2280_ = l_Lean_Compiler_LCNF_isClass_x3f(v_type_2275_, v_a_2276_, v_a_2277_);
stack->m_obj
 = v_res_2280_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___boxed(lean_object* v_type_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_Compiler_LCNF_isClass_x3f(v_type_2281_, v_a_2282_, v_a_2283_);
lean_dec(v_a_2283_);
lean_dec_ref(v_a_2282_);
lean_dec_ref(v_type_2281_);
return v_res_2285_;
}
}
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object* v_type_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v___x_2289_; 
lean_inc_ref(v_type_2286_);
v___x_2289_ = l_Lean_Expr_headBeta(v_type_2286_);
if (lean_obj_tag(v___x_2289_) == 7)
{
lean_object* v_body_2290_; 
lean_dec_ref(v_type_2286_);
v_body_2290_ = lean_ctor_get(v___x_2289_, 2);
lean_inc_ref(v_body_2290_);
lean_dec_ref_known(v___x_2289_, 3);
v_type_2286_ = v_body_2290_;
goto _start;
}
else
{
lean_object* v___x_2292_; 
lean_dec_ref(v___x_2289_);
v___x_2292_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2286_, v_a_2287_);
lean_dec_ref(v_type_2286_);
return v___x_2292_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2286_ = stack[0].m_obj;
lean_object* v_a_2287_ = stack[1].m_obj;
lean_object* v_res_2293_;
v_res_2293_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_2286_, v_a_2287_);
stack->m_obj
 = v_res_2293_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg___boxed(lean_object* v_type_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_2294_, v_a_2295_);
lean_dec(v_a_2295_);
return v_res_2297_;
}
}
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f(lean_object* v_type_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_2298_, v_a_2300_);
return v___x_2302_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isArrowClass_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2298_ = stack[0].m_obj;
lean_object* v_a_2299_ = stack[1].m_obj;
lean_object* v_a_2300_ = stack[2].m_obj;
lean_object* v_res_2303_;
v_res_2303_ = l_Lean_Compiler_LCNF_isArrowClass_x3f(v_type_2298_, v_a_2299_, v_a_2300_);
stack->m_obj
 = v_res_2303_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___boxed(lean_object* v_type_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_Compiler_LCNF_isArrowClass_x3f(v_type_2304_, v_a_2305_, v_a_2306_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getArrowArity(lean_object* v_e_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_Expr_headBeta(v_e_2309_);
if (lean_obj_tag(v___x_2310_) == 7)
{
lean_object* v_body_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_body_2311_ = lean_ctor_get(v___x_2310_, 2);
lean_inc_ref(v_body_2311_);
lean_dec_ref_known(v___x_2310_, 3);
v___x_2312_ = l_Lean_Compiler_LCNF_getArrowArity(v_body_2311_);
v___x_2313_ = lean_unsigned_to_nat(1u);
v___x_2314_ = lean_nat_add(v___x_2312_, v___x_2313_);
lean_dec(v___x_2312_);
return v___x_2314_;
}
else
{
lean_object* v___x_2315_; 
lean_dec_ref(v___x_2310_);
v___x_2315_ = lean_unsigned_to_nat(0u);
return v___x_2315_;
}
}
}
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object* v_type_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_Expr_getAppFn(v_type_2316_);
if (lean_obj_tag(v___x_2323_) == 4)
{
lean_object* v_declName_2324_; lean_object* v___x_2325_; lean_object* v_env_2326_; uint8_t v___x_2327_; lean_object* v___x_2328_; 
v_declName_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_declName_2324_);
lean_dec_ref_known(v___x_2323_, 2);
v___x_2325_ = lean_st_ref_get(v_a_2317_);
v_env_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc_ref(v_env_2326_);
lean_dec(v___x_2325_);
v___x_2327_ = 0;
v___x_2328_ = l_Lean_Environment_find_x3f(v_env_2326_, v_declName_2324_, v___x_2327_);
if (lean_obj_tag(v___x_2328_) == 1)
{
lean_object* v_val_2329_; 
v_val_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_val_2329_);
lean_dec_ref_known(v___x_2328_, 1);
if (lean_obj_tag(v_val_2329_) == 5)
{
lean_object* v_val_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2341_; 
v_val_2330_ = lean_ctor_get(v_val_2329_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_val_2329_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2332_ = v_val_2329_;
v_isShared_2333_ = v_isSharedCheck_2341_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_val_2330_);
lean_dec(v_val_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2341_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2334_ = l_Lean_InductiveVal_numCtors(v_val_2330_);
lean_dec_ref(v_val_2330_);
v___x_2335_ = lean_unsigned_to_nat(0u);
v___x_2336_ = lean_nat_dec_eq(v___x_2334_, v___x_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(v___x_2336_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set_tag(v___x_2332_, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2337_);
v___x_2339_ = v___x_2332_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
else
{
lean_dec(v_val_2329_);
goto v___jp_2319_;
}
}
else
{
lean_dec(v___x_2328_);
goto v___jp_2319_;
}
}
else
{
uint8_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
lean_dec_ref(v___x_2323_);
v___x_2342_ = 0;
v___x_2343_ = lean_box(v___x_2342_);
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
return v___x_2344_;
}
v___jp_2319_:
{
uint8_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = 0;
v___x_2321_ = lean_box(v___x_2320_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2316_ = stack[0].m_obj;
lean_object* v_a_2317_ = stack[1].m_obj;
lean_object* v_res_2345_;
v_res_2345_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_2316_, v_a_2317_);
stack->m_obj
 = v_res_2345_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg___boxed(lean_object* v_type_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_type_2346_);
return v_res_2349_;
}
}
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors(lean_object* v_type_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_2350_, v_a_2352_);
return v___x_2354_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isInductiveWithNoCtors_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2350_ = stack[0].m_obj;
lean_object* v_a_2351_ = stack[1].m_obj;
lean_object* v_a_2352_ = stack[2].m_obj;
lean_object* v_res_2355_;
v_res_2355_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors(v_type_2350_, v_a_2351_, v_a_2352_);
stack->m_obj
 = v_res_2355_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___boxed(lean_object* v_type_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors(v_type_2356_, v_a_2357_, v_a_2358_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec_ref(v_type_2356_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkBoxedName(lean_object* v_n_2362_){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkBoxedName___closed__0));
v___x_2364_ = l_Lean_Name_str___override(v_n_2362_, v___x_2363_);
return v___x_2364_;
}
}
uint8_t l_Lean_Compiler_LCNF_isBoxedName(lean_object* v_name_2365_){
_start:
{
if (lean_obj_tag(v_name_2365_) == 1)
{
lean_object* v_str_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; 
v_str_2366_ = lean_ctor_get(v_name_2365_, 1);
v___x_2367_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkBoxedName___closed__0));
v___x_2368_ = lean_string_dec_eq(v_str_2366_, v___x_2367_);
return v___x_2368_;
}
else
{
uint8_t v___x_2369_; 
v___x_2369_ = 0;
return v___x_2369_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isBoxedName_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2365_ = stack[0].m_obj;
uint8_t v_res_2370_;
v_res_2370_ = l_Lean_Compiler_LCNF_isBoxedName(v_name_2365_);
stack->m_num = v_res_2370_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isBoxedName___boxed(lean_object* v_name_2371_){
_start:
{
uint8_t v_res_2372_; lean_object* v_r_2373_; 
v_res_2372_ = l_Lean_Compiler_LCNF_isBoxedName(v_name_2371_);
lean_dec(v_name_2371_);
v_r_2373_ = lean_box(v_res_2372_);
return v_r_2373_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float___closed__2(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = lean_box(0);
v___x_2378_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__1));
v___x_2379_ = l_Lean_Expr_const___override(v___x_2378_, v___x_2377_);
return v___x_2379_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float(void){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_float___closed__2, &l_Lean_Compiler_LCNF_ImpureType_float___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_float___closed__2);
return v___x_2380_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float32___closed__2(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = lean_box(0);
v___x_2385_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__1));
v___x_2386_ = l_Lean_Expr_const___override(v___x_2385_, v___x_2384_);
return v___x_2386_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float32(void){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_float32___closed__2, &l_Lean_Compiler_LCNF_ImpureType_float32___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_float32___closed__2);
return v___x_2387_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = lean_box(0);
v___x_2392_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__1));
v___x_2393_ = l_Lean_Expr_const___override(v___x_2392_, v___x_2391_);
return v___x_2393_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint8(void){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2);
return v___x_2394_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2(void){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2398_ = lean_box(0);
v___x_2399_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__1));
v___x_2400_ = l_Lean_Expr_const___override(v___x_2399_, v___x_2398_);
return v___x_2400_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint16(void){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2);
return v___x_2401_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = lean_box(0);
v___x_2406_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__1));
v___x_2407_ = l_Lean_Expr_const___override(v___x_2406_, v___x_2405_);
return v___x_2407_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint32(void){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2);
return v___x_2408_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2(void){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = lean_box(0);
v___x_2413_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__1));
v___x_2414_ = l_Lean_Expr_const___override(v___x_2413_, v___x_2412_);
return v___x_2414_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint64(void){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2);
return v___x_2415_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_usize___closed__2(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2419_ = lean_box(0);
v___x_2420_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_usize___closed__1));
v___x_2421_ = l_Lean_Expr_const___override(v___x_2420_, v___x_2419_);
return v___x_2421_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_usize(void){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_usize___closed__2, &l_Lean_Compiler_LCNF_ImpureType_usize___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_usize___closed__2);
return v___x_2422_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_erased___closed__0(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2423_ = lean_box(0);
v___x_2424_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2));
v___x_2425_ = l_Lean_Expr_const___override(v___x_2424_, v___x_2423_);
return v___x_2425_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_erased(void){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_erased___closed__0, &l_Lean_Compiler_LCNF_ImpureType_erased___closed__0_once, _init_l_Lean_Compiler_LCNF_ImpureType_erased___closed__0);
return v___x_2426_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2430_ = lean_box(0);
v___x_2431_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__1));
v___x_2432_ = l_Lean_Expr_const___override(v___x_2431_, v___x_2430_);
return v___x_2432_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_object(void){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_object___closed__2, &l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2);
return v___x_2433_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = lean_box(0);
v___x_2438_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__1));
v___x_2439_ = l_Lean_Expr_const___override(v___x_2438_, v___x_2437_);
return v___x_2439_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tobject(void){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2);
return v___x_2440_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2444_ = lean_box(0);
v___x_2445_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__1));
v___x_2446_ = l_Lean_Expr_const___override(v___x_2445_, v___x_2444_);
return v___x_2446_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tagged(void){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2);
return v___x_2447_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_void___closed__0(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2448_ = lean_box(0);
v___x_2449_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_2450_ = l_Lean_Expr_const___override(v___x_2449_, v___x_2448_);
return v___x_2450_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_void(void){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_void___closed__0, &l_Lean_Compiler_LCNF_ImpureType_void___closed__0_once, _init_l_Lean_Compiler_LCNF_ImpureType_void___closed__0);
return v___x_2451_;
}
}
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object* v_x_2452_){
_start:
{
if (lean_obj_tag(v_x_2452_) == 4)
{
lean_object* v_declName_2453_; 
v_declName_2453_ = lean_ctor_get(v_x_2452_, 0);
if (lean_obj_tag(v_declName_2453_) == 1)
{
lean_object* v_pre_2454_; 
v_pre_2454_ = lean_ctor_get(v_declName_2453_, 0);
if (lean_obj_tag(v_pre_2454_) == 0)
{
lean_object* v_us_2455_; lean_object* v_str_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v_us_2455_ = lean_ctor_get(v_x_2452_, 1);
v_str_2456_ = lean_ctor_get(v_declName_2453_, 1);
v___x_2457_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__0));
v___x_2458_ = lean_string_dec_eq(v_str_2456_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2459_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__0));
v___x_2460_ = lean_string_dec_eq(v_str_2456_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___x_2461_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0));
v___x_2462_ = lean_string_dec_eq(v_str_2456_, v___x_2461_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2463_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0));
v___x_2464_ = lean_string_dec_eq(v_str_2456_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2465_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0));
v___x_2466_ = lean_string_dec_eq(v_str_2456_, v___x_2465_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; uint8_t v___x_2468_; 
v___x_2467_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0));
v___x_2468_ = lean_string_dec_eq(v_str_2456_, v___x_2467_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2469_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_usize___closed__0));
v___x_2470_ = lean_string_dec_eq(v_str_2456_, v___x_2469_);
if (v___x_2470_ == 0)
{
return v___x_2470_;
}
else
{
if (lean_obj_tag(v_us_2455_) == 0)
{
return v___x_2470_;
}
else
{
return v___x_2468_;
}
}
}
else
{
if (lean_obj_tag(v_us_2455_) == 0)
{
return v___x_2468_;
}
else
{
return v___x_2466_;
}
}
}
else
{
if (lean_obj_tag(v_us_2455_) == 0)
{
return v___x_2466_;
}
else
{
return v___x_2464_;
}
}
}
else
{
if (lean_obj_tag(v_us_2455_) == 0)
{
return v___x_2464_;
}
else
{
return v___x_2462_;
}
}
}
else
{
if (lean_obj_tag(v_us_2455_) == 0)
{
return v___x_2462_;
}
else
{
return v___x_2460_;
}
}
}
else
{
if (lean_obj_tag(v_us_2455_) == 0)
{
return v___x_2460_;
}
else
{
return v___x_2458_;
}
}
}
else
{
if (lean_obj_tag(v_us_2455_) == 0)
{
return v___x_2458_;
}
else
{
uint8_t v___x_2471_; 
v___x_2471_ = 0;
return v___x_2471_;
}
}
}
else
{
uint8_t v___x_2472_; 
v___x_2472_ = 0;
return v___x_2472_;
}
}
else
{
uint8_t v___x_2473_; 
v___x_2473_ = 0;
return v___x_2473_;
}
}
else
{
uint8_t v___x_2474_; 
v___x_2474_ = 0;
return v___x_2474_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2452_ = stack[0].m_obj;
uint8_t v_res_2475_;
v_res_2475_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_x_2452_);
stack->m_num = v_res_2475_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar___boxed(lean_object* v_x_2476_){
_start:
{
uint8_t v_res_2477_; lean_object* v_r_2478_; 
v_res_2477_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_x_2476_);
lean_dec_ref(v_x_2476_);
v_r_2478_ = lean_box(v_res_2477_);
return v_r_2478_;
}
}
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(lean_object* v_x_2479_){
_start:
{
if (lean_obj_tag(v_x_2479_) == 4)
{
lean_object* v_declName_2480_; 
v_declName_2480_ = lean_ctor_get(v_x_2479_, 0);
if (lean_obj_tag(v_declName_2480_) == 1)
{
lean_object* v_pre_2481_; 
v_pre_2481_ = lean_ctor_get(v_declName_2480_, 0);
if (lean_obj_tag(v_pre_2481_) == 0)
{
lean_object* v_us_2482_; lean_object* v_str_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; 
v_us_2482_ = lean_ctor_get(v_x_2479_, 1);
v_str_2483_ = lean_ctor_get(v_declName_2480_, 1);
v___x_2484_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2485_ = lean_string_dec_eq(v_str_2483_, v___x_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; uint8_t v___x_2487_; 
v___x_2486_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0));
v___x_2487_ = lean_string_dec_eq(v_str_2483_, v___x_2486_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2488_; uint8_t v___x_2489_; 
v___x_2488_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0));
v___x_2489_ = lean_string_dec_eq(v_str_2483_, v___x_2488_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; uint8_t v___x_2491_; 
v___x_2490_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__0));
v___x_2491_ = lean_string_dec_eq(v_str_2483_, v___x_2490_);
if (v___x_2491_ == 0)
{
return v___x_2491_;
}
else
{
if (lean_obj_tag(v_us_2482_) == 0)
{
return v___x_2491_;
}
else
{
return v___x_2489_;
}
}
}
else
{
if (lean_obj_tag(v_us_2482_) == 0)
{
return v___x_2489_;
}
else
{
return v___x_2487_;
}
}
}
else
{
if (lean_obj_tag(v_us_2482_) == 0)
{
return v___x_2487_;
}
else
{
return v___x_2485_;
}
}
}
else
{
if (lean_obj_tag(v_us_2482_) == 0)
{
return v___x_2485_;
}
else
{
uint8_t v___x_2492_; 
v___x_2492_ = 0;
return v___x_2492_;
}
}
}
else
{
uint8_t v___x_2493_; 
v___x_2493_ = 0;
return v___x_2493_;
}
}
else
{
uint8_t v___x_2494_; 
v___x_2494_ = 0;
return v___x_2494_;
}
}
else
{
uint8_t v___x_2495_; 
v___x_2495_ = 0;
return v___x_2495_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2479_ = stack[0].m_obj;
uint8_t v_res_2496_;
v_res_2496_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(v_x_2479_);
stack->m_num = v_res_2496_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj___boxed(lean_object* v_x_2497_){
_start:
{
uint8_t v_res_2498_; lean_object* v_r_2499_; 
v_res_2498_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(v_x_2497_);
lean_dec_ref(v_x_2497_);
v_r_2499_ = lean_box(v_res_2498_);
return v_r_2499_;
}
}
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(lean_object* v_x_2500_){
_start:
{
if (lean_obj_tag(v_x_2500_) == 4)
{
lean_object* v_declName_2501_; 
v_declName_2501_ = lean_ctor_get(v_x_2500_, 0);
if (lean_obj_tag(v_declName_2501_) == 1)
{
lean_object* v_pre_2502_; 
v_pre_2502_ = lean_ctor_get(v_declName_2501_, 0);
if (lean_obj_tag(v_pre_2502_) == 0)
{
lean_object* v_us_2503_; lean_object* v_str_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v_us_2503_ = lean_ctor_get(v_x_2500_, 1);
v_str_2504_ = lean_ctor_get(v_declName_2501_, 1);
v___x_2505_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2506_ = lean_string_dec_eq(v_str_2504_, v___x_2505_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2507_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0));
v___x_2508_ = lean_string_dec_eq(v_str_2504_, v___x_2507_);
if (v___x_2508_ == 0)
{
return v___x_2508_;
}
else
{
if (lean_obj_tag(v_us_2503_) == 0)
{
return v___x_2508_;
}
else
{
return v___x_2506_;
}
}
}
else
{
if (lean_obj_tag(v_us_2503_) == 0)
{
return v___x_2506_;
}
else
{
uint8_t v___x_2509_; 
v___x_2509_ = 0;
return v___x_2509_;
}
}
}
else
{
uint8_t v___x_2510_; 
v___x_2510_ = 0;
return v___x_2510_;
}
}
else
{
uint8_t v___x_2511_; 
v___x_2511_ = 0;
return v___x_2511_;
}
}
else
{
uint8_t v___x_2512_; 
v___x_2512_ = 0;
return v___x_2512_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2500_ = stack[0].m_obj;
uint8_t v_res_2513_;
v_res_2513_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_x_2500_);
stack->m_num = v_res_2513_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef___boxed(lean_object* v_x_2514_){
_start:
{
uint8_t v_res_2515_; lean_object* v_r_2516_; 
v_res_2515_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_x_2514_);
lean_dec_ref(v_x_2514_);
v_r_2516_ = lean_box(v_res_2515_);
return v_r_2516_;
}
}
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(lean_object* v_x_2517_){
_start:
{
if (lean_obj_tag(v_x_2517_) == 4)
{
lean_object* v_declName_2518_; 
v_declName_2518_ = lean_ctor_get(v_x_2517_, 0);
if (lean_obj_tag(v_declName_2518_) == 1)
{
lean_object* v_pre_2519_; 
v_pre_2519_ = lean_ctor_get(v_declName_2518_, 0);
if (lean_obj_tag(v_pre_2519_) == 0)
{
lean_object* v_us_2520_; lean_object* v_str_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v_us_2520_ = lean_ctor_get(v_x_2517_, 1);
v_str_2521_ = lean_ctor_get(v_declName_2518_, 1);
v___x_2522_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2523_ = lean_string_dec_eq(v_str_2521_, v___x_2522_);
if (v___x_2523_ == 0)
{
return v___x_2523_;
}
else
{
if (lean_obj_tag(v_us_2520_) == 0)
{
return v___x_2523_;
}
else
{
uint8_t v___x_2524_; 
v___x_2524_ = 0;
return v___x_2524_;
}
}
}
else
{
uint8_t v___x_2525_; 
v___x_2525_ = 0;
return v___x_2525_;
}
}
else
{
uint8_t v___x_2526_; 
v___x_2526_ = 0;
return v___x_2526_;
}
}
else
{
uint8_t v___x_2527_; 
v___x_2527_ = 0;
return v___x_2527_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2517_ = stack[0].m_obj;
uint8_t v_res_2528_;
v_res_2528_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_x_2517_);
stack->m_num = v_res_2528_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef___boxed(lean_object* v_x_2529_){
_start:
{
uint8_t v_res_2530_; lean_object* v_r_2531_; 
v_res_2530_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_x_2529_);
lean_dec_ref(v_x_2529_);
v_r_2531_ = lean_box(v_res_2530_);
return v_r_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object* v_x_2532_){
_start:
{
if (lean_obj_tag(v_x_2532_) == 4)
{
lean_object* v_declName_2539_; 
v_declName_2539_ = lean_ctor_get(v_x_2532_, 0);
if (lean_obj_tag(v_declName_2539_) == 1)
{
lean_object* v_pre_2540_; 
v_pre_2540_ = lean_ctor_get(v_declName_2539_, 0);
if (lean_obj_tag(v_pre_2540_) == 0)
{
lean_object* v_us_2541_; lean_object* v_str_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v_us_2541_ = lean_ctor_get(v_x_2532_, 1);
v_str_2542_ = lean_ctor_get(v_declName_2539_, 1);
v___x_2543_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2544_ = lean_string_dec_eq(v_str_2542_, v___x_2543_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2545_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__0));
v___x_2546_ = lean_string_dec_eq(v_str_2542_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; uint8_t v___x_2548_; 
v___x_2547_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__0));
v___x_2548_ = lean_string_dec_eq(v_str_2542_, v___x_2547_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2549_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0));
v___x_2550_ = lean_string_dec_eq(v_str_2542_, v___x_2549_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; uint8_t v___x_2552_; 
v___x_2551_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__0));
v___x_2552_ = lean_string_dec_eq(v_str_2542_, v___x_2551_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; uint8_t v___x_2554_; 
v___x_2553_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0));
v___x_2554_ = lean_string_dec_eq(v_str_2542_, v___x_2553_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; uint8_t v___x_2556_; 
v___x_2555_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0));
v___x_2556_ = lean_string_dec_eq(v_str_2542_, v___x_2555_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2557_; uint8_t v___x_2558_; 
v___x_2557_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0));
v___x_2558_ = lean_string_dec_eq(v_str_2542_, v___x_2557_);
if (v___x_2558_ == 0)
{
goto v___jp_2533_;
}
else
{
if (lean_obj_tag(v_us_2541_) == 0)
{
goto v___jp_2537_;
}
else
{
goto v___jp_2533_;
}
}
}
else
{
if (lean_obj_tag(v_us_2541_) == 0)
{
goto v___jp_2537_;
}
else
{
goto v___jp_2533_;
}
}
}
else
{
if (lean_obj_tag(v_us_2541_) == 0)
{
goto v___jp_2537_;
}
else
{
goto v___jp_2533_;
}
}
}
else
{
if (lean_obj_tag(v_us_2541_) == 0)
{
goto v___jp_2537_;
}
else
{
goto v___jp_2533_;
}
}
}
else
{
if (lean_obj_tag(v_us_2541_) == 0)
{
goto v___jp_2535_;
}
else
{
goto v___jp_2533_;
}
}
}
else
{
if (lean_obj_tag(v_us_2541_) == 0)
{
goto v___jp_2535_;
}
else
{
goto v___jp_2533_;
}
}
}
else
{
if (lean_obj_tag(v_us_2541_) == 0)
{
goto v___jp_2535_;
}
else
{
goto v___jp_2533_;
}
}
}
else
{
if (lean_obj_tag(v_us_2541_) == 0)
{
goto v___jp_2535_;
}
else
{
goto v___jp_2533_;
}
}
}
else
{
goto v___jp_2533_;
}
}
else
{
goto v___jp_2533_;
}
}
else
{
goto v___jp_2533_;
}
v___jp_2533_:
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2);
return v___x_2534_;
}
v___jp_2535_:
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_object___closed__2, &l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2);
return v___x_2536_;
}
v___jp_2537_:
{
lean_object* v___x_2538_; 
v___x_2538_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed___boxed(lean_object* v_x_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_x_2559_);
lean_dec_ref(v_x_2559_);
return v_res_2560_;
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
