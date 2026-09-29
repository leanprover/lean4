// Lean compiler output
// Module: Lean.Elab.Term
// Imports: public import Lean.Elab.DeclModifiers public import Lean.Elab.Term.TermElabM
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
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_Elab_expandDeclId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_expandDeclId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid declaration name `"};
static const lean_object* l_Lean_Elab_Term_expandDeclId___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandDeclId___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Term_expandDeclId___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_expandDeclId___closed__1;
static const lean_string_object l_Lean_Elab_Term_expandDeclId___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "`, there is a section variable with the same name"};
static const lean_object* l_Lean_Elab_Term_expandDeclId___closed__2 = (const lean_object*)&l_Lean_Elab_Term_expandDeclId___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Term_expandDeclId___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_expandDeclId___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandDeclId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandDeclId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "postpone"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 252, 100, 110, 65, 100, 32, 172)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 141, 62, 103, 155, 43, 121, 156)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(153, 191, 61, 221, 68, 164, 15, 27)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 104, 185, 153, 51, 35, 102, 207)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 176, 166, 92, 249, 40, 73, 88)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(27, 140, 202, 20, 52, 120, 32, 222)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 34, 145, 48, 249, 219, 208, 12)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(71, 235, 138, 3, 62, 227, 74, 180)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 82, 154, 48, 79, 247, 157, 121)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(69, 115, 136, 150, 160, 11, 202, 212)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "coe"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 100, 207, 97, 100, 108, 211, 217)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(22, 140, 229, 241, 82, 77, 142, 120)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__30_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "reuse"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__30_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__30_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__31_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__31_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__31_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__30_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 45, 118, 246, 35, 112, 183, 90)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__31_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__31_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "incremental"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(2, 169, 95, 71, 64, 177, 207, 154)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 238, .m_capacity = 238, .m_length = 237, .m_data = "Marks an elaborator (tactic or command, currently) as supporting incremental elaboration. For unmarked elaborators, the corresponding snapshot bundle field in the elaboration context is unset so as to prevent accidental, incorrect reuse."};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "incrementalAttr"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 159, 55, 199, 93, 160, 16, 206)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_incrementalAttr;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 239, .m_capacity = 239, .m_length = 238, .m_data = "Marks an elaborator (tactic or command, currently) as supporting incremental elaboration.\n\nFor unmarked elaborators, the corresponding snapshot bundle field in the elaboration context is\nunset so as to prevent accidental, incorrect reuse."};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(40) << 1) | 1)),((lean_object*)(((size_t)(88) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(88) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_428335796____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_428335796____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_builtinIncrementalElabs;
LEAN_EXPORT lean_object* l_Lean_Elab_addBuiltinIncrementalElab(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addBuiltinIncrementalElab___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__6_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__7 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__7_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "addBuiltinIncrementalElab"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2114473129) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(176, 196, 25, 171, 36, 203, 133, 40)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 251, 186, 11, 114, 233, 48, 81)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(175, 138, 217, 150, 187, 31, 4, 241)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(170, 143, 167, 36, 170, 127, 248, 32)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "builtin_incremental"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 9, 66, 145, 219, 200, 153, 238)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed, .m_arity = 9, .m_num_fixed = 3, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "(builtin) "};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___regBuiltin___private_Lean_Elab_Term_0__Lean_Elab_initFn_docString__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___regBuiltin___private_Lean_Elab_Term_0__Lean_Elab_initFn_docString__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_isIncrementalElab___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_isIncrementalElab___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitForall"};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 106, 166, 245, 117, 46, 241, 54)}};
static const lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_box(1);
v___x_2_ = l_Lean_MessageData_ofFormat(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__2));
v___x_7_ = l_Lean_MessageData_ofFormat(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3(lean_object* v_x_8_, lean_object* v_x_9_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
return v_x_8_;
}
else
{
lean_object* v_head_10_; lean_object* v_tail_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_33_; 
v_head_10_ = lean_ctor_get(v_x_9_, 0);
v_tail_11_ = lean_ctor_get(v_x_9_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_x_9_);
if (v_isSharedCheck_33_ == 0)
{
v___x_13_ = v_x_9_;
v_isShared_14_ = v_isSharedCheck_33_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_tail_11_);
lean_inc(v_head_10_);
lean_dec(v_x_9_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_33_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v_before_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_31_; 
v_before_15_ = lean_ctor_get(v_head_10_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v_head_10_);
if (v_isSharedCheck_31_ == 0)
{
lean_object* v_unused_32_; 
v_unused_32_ = lean_ctor_get(v_head_10_, 1);
lean_dec(v_unused_32_);
v___x_17_ = v_head_10_;
v_isShared_18_ = v_isSharedCheck_31_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_before_15_);
lean_dec(v_head_10_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_31_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_19_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_18_ == 0)
{
lean_ctor_set_tag(v___x_17_, 7);
lean_ctor_set(v___x_17_, 1, v___x_19_);
lean_ctor_set(v___x_17_, 0, v_x_8_);
v___x_21_ = v___x_17_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_x_8_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v___x_19_);
v___x_21_ = v_reuseFailAlloc_30_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_22_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_14_ == 0)
{
lean_ctor_set_tag(v___x_13_, 7);
lean_ctor_set(v___x_13_, 1, v___x_22_);
lean_ctor_set(v___x_13_, 0, v___x_21_);
v___x_24_ = v___x_13_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_21_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v___x_22_);
v___x_24_ = v_reuseFailAlloc_29_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = l_Lean_MessageData_ofSyntax(v_before_15_);
v___x_26_ = l_Lean_indentD(v___x_25_);
v___x_27_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_24_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
v_x_8_ = v___x_27_;
v_x_9_ = v_tail_11_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__2(lean_object* v_opts_34_, lean_object* v_opt_35_){
_start:
{
lean_object* v_name_36_; lean_object* v_defValue_37_; lean_object* v_map_38_; lean_object* v___x_39_; 
v_name_36_ = lean_ctor_get(v_opt_35_, 0);
v_defValue_37_ = lean_ctor_get(v_opt_35_, 1);
v_map_38_ = lean_ctor_get(v_opts_34_, 0);
v___x_39_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_38_, v_name_36_);
if (lean_obj_tag(v___x_39_) == 0)
{
uint8_t v___x_40_; 
v___x_40_ = lean_unbox(v_defValue_37_);
return v___x_40_;
}
else
{
lean_object* v_val_41_; 
v_val_41_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_val_41_);
lean_dec_ref_known(v___x_39_, 1);
if (lean_obj_tag(v_val_41_) == 1)
{
uint8_t v_v_42_; 
v_v_42_ = lean_ctor_get_uint8(v_val_41_, 0);
lean_dec_ref_known(v_val_41_, 0);
return v_v_42_;
}
else
{
uint8_t v___x_43_; 
lean_dec(v_val_41_);
v___x_43_ = lean_unbox(v_defValue_37_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_44_, lean_object* v_opt_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__2(v_opts_44_, v_opt_45_);
lean_dec_ref(v_opt_45_);
lean_dec_ref(v_opts_44_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__1));
v___x_52_ = l_Lean_MessageData_ofFormat(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg(lean_object* v_msgData_53_, lean_object* v_macroStack_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_57_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_55_);
v___x_58_ = l_Lean_Elab_pp_macroStack;
v___x_59_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__2(v___x_57_, v___x_58_);
lean_dec_ref(v___x_57_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
lean_dec(v_macroStack_54_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v_msgData_53_);
return v___x_60_;
}
else
{
if (lean_obj_tag(v_macroStack_54_) == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_msgData_53_);
return v___x_61_;
}
else
{
lean_object* v_head_62_; lean_object* v_after_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_78_; 
v_head_62_ = lean_ctor_get(v_macroStack_54_, 0);
lean_inc(v_head_62_);
v_after_63_ = lean_ctor_get(v_head_62_, 1);
v_isSharedCheck_78_ = !lean_is_exclusive(v_head_62_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; 
v_unused_79_ = lean_ctor_get(v_head_62_, 0);
lean_dec(v_unused_79_);
v___x_65_ = v_head_62_;
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_after_63_);
lean_dec(v_head_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 7);
lean_ctor_set(v___x_65_, 1, v___x_67_);
lean_ctor_set(v___x_65_, 0, v_msgData_53_);
v___x_69_ = v___x_65_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_msgData_53_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v___x_67_);
v___x_69_ = v_reuseFailAlloc_77_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v_msgData_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_70_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___closed__2);
v___x_71_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = l_Lean_MessageData_ofSyntax(v_after_63_);
v___x_73_ = l_Lean_indentD(v___x_72_);
v_msgData_74_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_74_, 0, v___x_71_);
lean_ctor_set(v_msgData_74_, 1, v___x_73_);
v___x_75_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3(v_msgData_74_, v_macroStack_54_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_80_, lean_object* v_macroStack_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg(v_msgData_80_, v_macroStack_81_, v___y_82_);
lean_dec_ref(v___y_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__0(lean_object* v_msgData_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; lean_object* v_env_92_; lean_object* v___x_93_; lean_object* v_toCold_94_; lean_object* v_mctx_95_; lean_object* v_lctx_96_; lean_object* v_options_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_91_ = lean_st_ref_get(v___y_89_);
v_env_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_env_92_);
lean_dec(v___x_91_);
v___x_93_ = lean_st_ref_get(v___y_87_);
v_toCold_94_ = lean_ctor_get(v___y_88_, 0);
v_mctx_95_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_mctx_95_);
lean_dec(v___x_93_);
v_lctx_96_ = lean_ctor_get(v___y_86_, 2);
v_options_97_ = lean_ctor_get(v_toCold_94_, 2);
lean_inc_ref(v_options_97_);
lean_inc_ref(v_lctx_96_);
v___x_98_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_98_, 0, v_env_92_);
lean_ctor_set(v___x_98_, 1, v_mctx_95_);
lean_ctor_set(v___x_98_, 2, v_lctx_96_);
lean_ctor_set(v___x_98_, 3, v_options_97_);
v___x_99_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v_msgData_85_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__0___boxed(lean_object* v_msgData_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__0(v_msgData_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg(lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_ref_116_; lean_object* v_macroStack_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_a_120_; lean_object* v___x_121_; lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_130_; 
v_ref_116_ = lean_ctor_get(v___y_113_, 2);
v_macroStack_117_ = lean_ctor_get(v___y_109_, 1);
v___x_118_ = l_Lean_Elab_getBetterRef(v_ref_116_, v_macroStack_117_);
v___x_119_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__0(v_msg_108_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
lean_dec_ref(v___x_119_);
lean_inc(v_macroStack_117_);
v___x_121_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg(v_a_120_, v_macroStack_117_, v___y_113_);
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_130_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_118_);
lean_ctor_set(v___x_126_, 1, v_a_122_);
if (v_isShared_125_ == 0)
{
lean_ctor_set_tag(v___x_124_, 1);
lean_ctor_set(v___x_124_, 0, v___x_126_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg___boxed(lean_object* v_msg_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg(v_msg_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_139_;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDeclId___closed__1(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lean_Elab_Term_expandDeclId___closed__0));
v___x_142_ = l_Lean_stringToMessageData(v___x_141_);
return v___x_142_;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDeclId___closed__3(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l_Lean_Elab_Term_expandDeclId___closed__2));
v___x_145_ = l_Lean_stringToMessageData(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandDeclId(lean_object* v_currNamespace_146_, lean_object* v_currLevelNames_147_, lean_object* v_declId_148_, lean_object* v_modifiers_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Elab_expandDeclId(v_currNamespace_146_, v_currLevelNames_147_, v_declId_148_, v_modifiers_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v_sectionVars_159_; lean_object* v_shortName_160_; uint8_t v___x_161_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
v_sectionVars_159_ = lean_ctor_get(v_a_150_, 4);
v_shortName_160_ = lean_ctor_get(v_a_158_, 0);
lean_inc(v_shortName_160_);
lean_dec(v_a_158_);
v___x_161_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_shortName_160_, v_sectionVars_159_);
if (v___x_161_ == 0)
{
lean_dec(v_shortName_160_);
return v___x_157_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_dec_ref_known(v___x_157_, 1);
v___x_162_ = lean_obj_once(&l_Lean_Elab_Term_expandDeclId___closed__1, &l_Lean_Elab_Term_expandDeclId___closed__1_once, _init_l_Lean_Elab_Term_expandDeclId___closed__1);
v___x_163_ = l_Lean_MessageData_ofName(v_shortName_160_);
v___x_164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = lean_obj_once(&l_Lean_Elab_Term_expandDeclId___closed__3, &l_Lean_Elab_Term_expandDeclId___closed__3_once, _init_l_Lean_Elab_Term_expandDeclId___closed__3);
v___x_166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg(v___x_166_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandDeclId___boxed(lean_object* v_currNamespace_176_, lean_object* v_currLevelNames_177_, lean_object* v_declId_178_, lean_object* v_modifiers_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Elab_Term_expandDeclId(v_currNamespace_176_, v_currLevelNames_177_, v_declId_178_, v_modifiers_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec_ref(v_modifiers_179_);
lean_dec(v_declId_178_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0(lean_object* v_00_u03b1_188_, lean_object* v_msg_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg(v_msg_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___boxed(lean_object* v_00_u03b1_198_, lean_object* v_msg_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0(v_00_u03b1_198_, v_msg_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1(lean_object* v_msgData_208_, lean_object* v_macroStack_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg(v_msgData_208_, v_macroStack_209_, v___y_214_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___boxed(lean_object* v_msgData_218_, lean_object* v_macroStack_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1(v_msgData_218_, v_macroStack_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
return v_res_227_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_unsigned_to_nat(2544510742u);
v___x_275_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_276_ = l_Lean_Name_num___override(v___x_275_, v___x_274_);
return v___x_276_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_279_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_);
v___x_280_ = l_Lean_Name_str___override(v___x_279_, v___x_278_);
return v___x_280_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_283_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_);
v___x_284_ = l_Lean_Name_str___override(v___x_283_, v___x_282_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_unsigned_to_nat(2u);
v___x_286_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_);
v___x_287_ = l_Lean_Name_num___override(v___x_286_, v___x_285_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_302_ = 0;
v___x_303_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_);
v___x_304_ = l_Lean_registerTraceClass(v___x_301_, v___x_302_, v___x_303_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec_ref_known(v___x_304_, 1);
v___x_305_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_306_ = l_Lean_registerTraceClass(v___x_305_, v___x_302_, v___x_303_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec_ref_known(v___x_306_, 1);
v___x_307_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_308_ = l_Lean_registerTraceClass(v___x_307_, v___x_302_, v___x_303_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec_ref_known(v___x_308_, 1);
v___x_309_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__31_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_310_ = l_Lean_registerTraceClass(v___x_309_, v___x_302_, v___x_303_);
return v___x_310_;
}
else
{
return v___x_308_;
}
}
else
{
return v___x_306_;
}
}
else
{
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2____boxed(lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_();
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_(lean_object* v_x_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_box(0);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2____boxed(lean_object* v_x_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_(v_x_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v_x_319_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___f_335_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_));
v___x_336_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_));
v___x_337_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_));
v___x_338_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_));
v___x_339_ = 0;
v___x_340_ = lean_box(2);
v___x_341_ = l_Lean_registerTagAttribute(v___x_336_, v___x_337_, v___f_335_, v___x_338_, v___x_339_, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2____boxed(lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_();
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1(){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_));
v___x_347_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___closed__0));
v___x_348_ = l_Lean_addBuiltinDocString(v___x_346_, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___boxed(lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1();
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3(){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_));
v___x_378_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__6));
v___x_379_ = l_Lean_addBuiltinDeclarationRanges(v___x_377_, v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___boxed(lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3();
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_428335796____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = l_Lean_NameSet_empty;
v___x_384_ = lean_st_mk_ref(v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_428335796____hygCtx___hyg_2____boxed(lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_428335796____hygCtx___hyg_2_();
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addBuiltinIncrementalElab(lean_object* v_decl_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_390_ = l_Lean_Elab_builtinIncrementalElabs;
v___x_391_ = lean_st_ref_take(v___x_390_);
v___x_392_ = l_Lean_NameSet_insert(v___x_391_, v_decl_388_);
v___x_393_ = lean_st_ref_put(v___x_390_, v___x_392_);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addBuiltinIncrementalElab___boxed(lean_object* v_decl_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Elab_addBuiltinIncrementalElab(v_decl_395_);
return v_res_397_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_398_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_401_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
lean_ctor_set(v___x_403_, 2, v___x_402_);
lean_ctor_set(v___x_403_, 3, v___x_402_);
lean_ctor_set(v___x_403_, 4, v___x_401_);
lean_ctor_set(v___x_403_, 5, v___x_401_);
lean_ctor_set(v___x_403_, 6, v___x_401_);
lean_ctor_set(v___x_403_, 7, v___x_401_);
lean_ctor_set(v___x_403_, 8, v___x_401_);
lean_ctor_set(v___x_403_, 9, v___x_401_);
lean_ctor_set(v___x_403_, 10, v___x_401_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_unsigned_to_nat(32u);
v___x_405_ = lean_mk_empty_array_with_capacity(v___x_404_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_407_ = ((size_t)5ULL);
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = lean_unsigned_to_nat(32u);
v___x_410_ = lean_mk_empty_array_with_capacity(v___x_409_);
v___x_411_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_412_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
lean_ctor_set(v___x_412_, 2, v___x_408_);
lean_ctor_set(v___x_412_, 3, v___x_408_);
lean_ctor_set_usize(v___x_412_, 4, v___x_407_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_413_ = lean_box(1);
v___x_414_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_415_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
lean_ctor_set(v___x_416_, 2, v___x_413_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; lean_object* v_toCold_422_; lean_object* v_env_423_; lean_object* v_options_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_421_ = lean_st_ref_get(v___y_419_);
v_toCold_422_ = lean_ctor_get(v___y_418_, 0);
v_env_423_ = lean_ctor_get(v___x_421_, 0);
lean_inc_ref(v_env_423_);
lean_dec(v___x_421_);
v_options_424_ = lean_ctor_get(v_toCold_422_, 2);
v___x_425_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_426_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_424_);
v___x_427_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_427_, 0, v_env_423_);
lean_ctor_set(v___x_427_, 1, v___x_425_);
lean_ctor_set(v___x_427_, 2, v___x_426_);
lean_ctor_set(v___x_427_, 3, v_options_424_);
v___x_428_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v_msgData_417_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0(v_msgData_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_ref_439_; lean_object* v___x_440_; lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_449_; 
v_ref_439_ = lean_ctor_get(v___y_436_, 2);
v___x_440_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0(v_msg_435_, v___y_436_, v___y_437_);
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_449_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_447_; 
lean_inc(v_ref_439_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_ref_439_);
lean_ctor_set(v___x_445_, 1, v_a_441_);
if (v_isShared_444_ == 0)
{
lean_ctor_set_tag(v___x_443_, 1);
lean_ctor_set(v___x_443_, 0, v___x_445_);
v___x_447_ = v___x_443_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(v_msg_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_454_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__2));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__4));
v___x_463_ = l_Lean_stringToMessageData(v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg(lean_object* v_name_467_, uint8_t v_kind_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___y_478_; 
v___x_472_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_473_ = l_Lean_MessageData_ofName(v_name_467_);
v___x_474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3);
v___x_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
switch(v_kind_468_)
{
case 0:
{
lean_object* v___x_485_; 
v___x_485_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__6));
v___y_478_ = v___x_485_;
goto v___jp_477_;
}
case 1:
{
lean_object* v___x_486_; 
v___x_486_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__7));
v___y_478_ = v___x_486_;
goto v___jp_477_;
}
default: 
{
lean_object* v___x_487_; 
v___x_487_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__8));
v___y_478_ = v___x_487_;
goto v___jp_477_;
}
}
v___jp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
lean_inc_ref(v___y_478_);
v___x_479_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_479_, 0, v___y_478_);
v___x_480_ = l_Lean_MessageData_ofFormat(v___x_479_);
v___x_481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_476_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5);
v___x_483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(v___x_483_, v___y_469_, v___y_470_);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_name_488_, lean_object* v_kind_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
uint8_t v_kind_boxed_493_; lean_object* v_res_494_; 
v_kind_boxed_493_ = lean_unbox(v_kind_489_);
v_res_494_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg(v_name_488_, v_kind_boxed_493_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(lean_object* v___x_496_, lean_object* v___x_497_, lean_object* v___x_498_, lean_object* v_decl_499_, lean_object* v_stx_500_, uint8_t v_kind_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_500_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_513_) == 0)
{
uint8_t v___x_514_; uint8_t v___x_515_; 
lean_dec_ref_known(v___x_513_, 1);
v___x_514_ = 0;
v___x_515_ = l_Lean_instBEqAttributeKind_beq(v_kind_501_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
lean_dec(v_decl_499_);
lean_dec_ref(v___x_497_);
lean_dec_ref(v___x_496_);
v___x_516_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg(v___x_498_, v_kind_501_, v___y_502_, v___y_503_);
return v___x_516_;
}
else
{
lean_dec(v___x_498_);
goto v___jp_505_;
}
}
else
{
lean_dec(v_decl_499_);
lean_dec(v___x_498_);
lean_dec_ref(v___x_497_);
lean_dec_ref(v___x_496_);
return v___x_513_;
}
v___jp_505_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_506_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___x_507_ = l_Lean_Name_mkStr3(v___x_496_, v___x_497_, v___x_506_);
v___x_508_ = lean_box(0);
v___x_509_ = l_Lean_mkConst(v___x_507_, v___x_508_);
lean_inc(v_decl_499_);
v___x_510_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_decl_499_);
v___x_511_ = l_Lean_Expr_app___override(v___x_509_, v___x_510_);
v___x_512_ = l_Lean_declareBuiltin(v_decl_499_, v___x_511_, v___y_502_, v___y_503_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v_decl_520_, lean_object* v_stx_521_, lean_object* v_kind_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
uint8_t v_kind_boxed_526_; lean_object* v_res_527_; 
v_kind_boxed_526_ = lean_unbox(v_kind_522_);
v_res_527_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(v___x_517_, v___x_518_, v___x_519_, v_decl_520_, v_stx_521_, v_kind_boxed_526_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_527_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___x_530_ = l_Lean_stringToMessageData(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(lean_object* v___x_534_, lean_object* v_decl_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_539_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_);
v___x_540_ = l_Lean_MessageData_ofName(v___x_534_);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_);
v___x_543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(v___x_543_, v___y_536_, v___y_537_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(lean_object* v___x_545_, lean_object* v_decl_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(v___x_545_, v_decl_546_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v_decl_546_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_574_; lean_object* v_attr_575_; lean_object* v_toAttributeImplCore_576_; lean_object* v_descr_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___f_580_; lean_object* v___f_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_574_ = l_Lean_Elab_incrementalAttr;
v_attr_575_ = lean_ctor_get(v___x_574_, 0);
v_toAttributeImplCore_576_ = lean_ctor_get(v_attr_575_, 0);
v_descr_577_ = lean_ctor_get(v_toAttributeImplCore_576_, 2);
v___x_578_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___x_579_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___f_580_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___f_581_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___x_582_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___x_583_ = lean_string_append(v___x_582_, v_descr_577_);
v___x_584_ = 1;
v___x_585_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_585_, 0, v___x_578_);
lean_ctor_set(v___x_585_, 1, v___x_579_);
lean_ctor_set(v___x_585_, 2, v___x_583_);
lean_ctor_set_uint8(v___x_585_, sizeof(void*)*3, v___x_584_);
v___x_586_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___f_580_);
lean_ctor_set(v___x_586_, 2, v___f_581_);
v___x_587_ = l_Lean_registerBuiltinAttribute(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_();
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_590_, lean_object* v_msg_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(v_msg_591_, v___y_592_, v___y_593_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_596_, lean_object* v_msg_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0(v_00_u03b1_596_, v_msg_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_602_, lean_object* v_name_603_, uint8_t v_kind_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg(v_name_603_, v_kind_604_, v___y_605_, v___y_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_609_, lean_object* v_name_610_, lean_object* v_kind_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
uint8_t v_kind_boxed_615_; lean_object* v_res_616_; 
v_kind_boxed_615_ = lean_unbox(v_kind_611_);
v_res_616_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1(v_00_u03b1_609_, v_name_610_, v_kind_boxed_615_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___regBuiltin___private_Lean_Elab_Term_0__Lean_Elab_initFn_docString__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___x_619_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___closed__0));
v___x_620_ = l_Lean_addBuiltinDocString(v___x_618_, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___regBuiltin___private_Lean_Elab_Term_0__Lean_Elab_initFn_docString__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___regBuiltin___private_Lean_Elab_Term_0__Lean_Elab_initFn_docString__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_();
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__0(lean_object* v___x_623_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_st_ref_get(v___x_623_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__0___boxed(lean_object* v___x_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Elab_isIncrementalElab___redArg___lam__0(v___x_627_);
lean_dec(v___x_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__1(lean_object* v_decl_630_, lean_object* v_toPure_631_, lean_object* v_____do__lift_632_){
_start:
{
uint8_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = l_Lean_NameSet_contains(v_____do__lift_632_, v_decl_630_);
v___x_634_ = lean_box(v___x_633_);
v___x_635_ = lean_apply_2(v_toPure_631_, lean_box(0), v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__1___boxed(lean_object* v_decl_636_, lean_object* v_toPure_637_, lean_object* v_____do__lift_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Elab_isIncrementalElab___redArg___lam__1(v_decl_636_, v_toPure_637_, v_____do__lift_638_);
lean_dec(v_____do__lift_638_);
lean_dec(v_decl_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__2(lean_object* v_decl_640_, lean_object* v_toPure_641_, lean_object* v_____do__lift_642_){
_start:
{
lean_object* v___x_643_; uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_643_ = l_Lean_Elab_incrementalAttr;
v___x_644_ = l_Lean_TagAttribute_hasTag(v___x_643_, v_____do__lift_642_, v_decl_640_);
v___x_645_ = lean_box(v___x_644_);
v___x_646_ = lean_apply_2(v_toPure_641_, lean_box(0), v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__3(lean_object* v_inst_647_, lean_object* v_toBind_648_, lean_object* v___f_649_, lean_object* v_toPure_650_, uint8_t v_b_651_){
_start:
{
if (v_b_651_ == 0)
{
lean_object* v_getEnv_652_; lean_object* v___x_653_; 
lean_dec(v_toPure_650_);
v_getEnv_652_ = lean_ctor_get(v_inst_647_, 0);
lean_inc(v_getEnv_652_);
lean_dec_ref(v_inst_647_);
v___x_653_ = lean_apply_4(v_toBind_648_, lean_box(0), lean_box(0), v_getEnv_652_, v___f_649_);
return v___x_653_;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec(v___f_649_);
lean_dec(v_toBind_648_);
lean_dec_ref(v_inst_647_);
v___x_654_ = lean_box(v_b_651_);
v___x_655_ = lean_apply_2(v_toPure_650_, lean_box(0), v___x_654_);
return v___x_655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__3___boxed(lean_object* v_inst_656_, lean_object* v_toBind_657_, lean_object* v___f_658_, lean_object* v_toPure_659_, lean_object* v_b_660_){
_start:
{
uint8_t v_b_boxed_661_; lean_object* v_res_662_; 
v_b_boxed_661_ = lean_unbox(v_b_660_);
v_res_662_ = l_Lean_Elab_isIncrementalElab___redArg___lam__3(v_inst_656_, v_toBind_657_, v___f_658_, v_toPure_659_, v_b_boxed_661_);
return v_res_662_;
}
}
static lean_object* _init_l_Lean_Elab_isIncrementalElab___redArg___closed__0(void){
_start:
{
lean_object* v___x_663_; lean_object* v___f_664_; 
v___x_663_ = l_Lean_Elab_builtinIncrementalElabs;
v___f_664_ = lean_alloc_closure((void*)(l_Lean_Elab_isIncrementalElab___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_664_, 0, v___x_663_);
return v___f_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg(lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_decl_668_){
_start:
{
lean_object* v_toApplicative_669_; lean_object* v_toBind_670_; lean_object* v_toPure_671_; lean_object* v___f_672_; lean_object* v___x_673_; lean_object* v___f_674_; lean_object* v___f_675_; lean_object* v___f_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_toApplicative_669_ = lean_ctor_get(v_inst_665_, 0);
lean_inc_ref(v_toApplicative_669_);
v_toBind_670_ = lean_ctor_get(v_inst_665_, 1);
lean_inc_n(v_toBind_670_, 3);
lean_dec_ref(v_inst_665_);
v_toPure_671_ = lean_ctor_get(v_toApplicative_669_, 1);
lean_inc_n(v_toPure_671_, 3);
lean_dec_ref(v_toApplicative_669_);
v___f_672_ = lean_obj_once(&l_Lean_Elab_isIncrementalElab___redArg___closed__0, &l_Lean_Elab_isIncrementalElab___redArg___closed__0_once, _init_l_Lean_Elab_isIncrementalElab___redArg___closed__0);
v___x_673_ = lean_apply_2(v_inst_667_, lean_box(0), v___f_672_);
lean_inc(v_decl_668_);
v___f_674_ = lean_alloc_closure((void*)(l_Lean_Elab_isIncrementalElab___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_674_, 0, v_decl_668_);
lean_closure_set(v___f_674_, 1, v_toPure_671_);
v___f_675_ = lean_alloc_closure((void*)(l_Lean_Elab_isIncrementalElab___redArg___lam__2), 3, 2);
lean_closure_set(v___f_675_, 0, v_decl_668_);
lean_closure_set(v___f_675_, 1, v_toPure_671_);
v___f_676_ = lean_alloc_closure((void*)(l_Lean_Elab_isIncrementalElab___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_676_, 0, v_inst_666_);
lean_closure_set(v___f_676_, 1, v_toBind_670_);
lean_closure_set(v___f_676_, 2, v___f_675_);
lean_closure_set(v___f_676_, 3, v_toPure_671_);
v___x_677_ = lean_apply_4(v_toBind_670_, lean_box(0), lean_box(0), v___x_673_, v___f_674_);
v___x_678_ = lean_apply_4(v_toBind_670_, lean_box(0), lean_box(0), v___x_677_, v___f_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab(lean_object* v_m_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_decl_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Elab_isIncrementalElab___redArg(v_inst_680_, v_inst_681_, v_inst_682_, v_decl_683_);
return v___x_684_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_unsigned_to_nat(3314678858u);
v___x_690_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_691_ = l_Lean_Name_num___override(v___x_690_, v___x_689_);
return v___x_691_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_693_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_);
v___x_694_ = l_Lean_Name_str___override(v___x_693_, v___x_692_);
return v___x_694_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_696_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_);
v___x_697_ = l_Lean_Name_str___override(v___x_696_, v___x_695_);
return v___x_697_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_unsigned_to_nat(2u);
v___x_699_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_);
v___x_700_ = l_Lean_Name_num___override(v___x_699_, v___x_698_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_702_; uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_702_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_));
v___x_703_ = 0;
v___x_704_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_);
v___x_705_ = l_Lean_registerTraceClass(v___x_702_, v___x_703_, v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2____boxed(lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_();
return v_res_707_;
}
}
lean_object* runtime_initialize_Lean_Elab_DeclModifiers(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_DeclModifiers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_incrementalAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_incrementalAttr);
lean_dec_ref(res);
res = l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_428335796____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_builtinIncrementalElabs = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_builtinIncrementalElabs);
lean_dec_ref(res);
res = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___regBuiltin___private_Lean_Elab_Term_0__Lean_Elab_initFn_docString__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Term(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_DeclModifiers(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Term(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_DeclModifiers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Term(builtin);
}
#ifdef __cplusplus
}
#endif
