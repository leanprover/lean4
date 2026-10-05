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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t);
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
lean_object* v___x_91_; lean_object* v_env_92_; uint8_t v___x_93_; lean_object* v_env_94_; lean_object* v___x_95_; lean_object* v_toCold_96_; lean_object* v_mctx_97_; lean_object* v_lctx_98_; lean_object* v_options_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_91_ = lean_st_ref_get(v___y_89_);
v_env_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_env_92_);
lean_dec(v___x_91_);
v___x_93_ = 0;
v_env_94_ = l_Lean_Environment_setRecordingDeps(v_env_92_, v___x_93_);
v___x_95_ = lean_st_ref_get(v___y_87_);
v_toCold_96_ = lean_ctor_get(v___y_88_, 0);
v_mctx_97_ = lean_ctor_get(v___x_95_, 0);
lean_inc_ref(v_mctx_97_);
lean_dec(v___x_95_);
v_lctx_98_ = lean_ctor_get(v___y_86_, 2);
v_options_99_ = lean_ctor_get(v_toCold_96_, 2);
lean_inc_ref(v_options_99_);
lean_inc_ref(v_lctx_98_);
v___x_100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_100_, 0, v_env_94_);
lean_ctor_set(v___x_100_, 1, v_mctx_97_);
lean_ctor_set(v___x_100_, 2, v_lctx_98_);
lean_ctor_set(v___x_100_, 3, v_options_99_);
v___x_101_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_msgData_85_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__0___boxed(lean_object* v_msgData_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__0(v_msgData_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg(lean_object* v_msg_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_ref_118_; lean_object* v_macroStack_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_a_122_; lean_object* v___x_123_; lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_132_; 
v_ref_118_ = lean_ctor_get(v___y_115_, 2);
v_macroStack_119_ = lean_ctor_get(v___y_111_, 1);
v___x_120_ = l_Lean_Elab_getBetterRef(v_ref_118_, v_macroStack_119_);
v___x_121_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__0(v_msg_110_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
lean_dec_ref(v___x_121_);
lean_inc(v_macroStack_119_);
v___x_123_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg(v_a_122_, v_macroStack_119_, v___y_115_);
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_132_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_120_);
lean_ctor_set(v___x_128_, 1, v_a_124_);
if (v_isShared_127_ == 0)
{
lean_ctor_set_tag(v___x_126_, 1);
lean_ctor_set(v___x_126_, 0, v___x_128_);
v___x_130_ = v___x_126_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg___boxed(lean_object* v_msg_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg(v_msg_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_141_;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDeclId___closed__1(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lean_Elab_Term_expandDeclId___closed__0));
v___x_144_ = l_Lean_stringToMessageData(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDeclId___closed__3(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l_Lean_Elab_Term_expandDeclId___closed__2));
v___x_147_ = l_Lean_stringToMessageData(v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandDeclId(lean_object* v_currNamespace_148_, lean_object* v_currLevelNames_149_, lean_object* v_declId_150_, lean_object* v_modifiers_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Elab_expandDeclId(v_currNamespace_148_, v_currLevelNames_149_, v_declId_150_, v_modifiers_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v_sectionVars_161_; lean_object* v_shortName_162_; uint8_t v___x_163_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_sectionVars_161_ = lean_ctor_get(v_a_152_, 4);
v_shortName_162_ = lean_ctor_get(v_a_160_, 0);
v___x_163_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_shortName_162_, v_sectionVars_161_);
if (v___x_163_ == 0)
{
return v___x_159_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
lean_inc(v_shortName_162_);
lean_dec_ref_known(v___x_159_, 1);
v___x_164_ = lean_obj_once(&l_Lean_Elab_Term_expandDeclId___closed__1, &l_Lean_Elab_Term_expandDeclId___closed__1_once, _init_l_Lean_Elab_Term_expandDeclId___closed__1);
v___x_165_ = l_Lean_MessageData_ofName(v_shortName_162_);
v___x_166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = lean_obj_once(&l_Lean_Elab_Term_expandDeclId___closed__3, &l_Lean_Elab_Term_expandDeclId___closed__3_once, _init_l_Lean_Elab_Term_expandDeclId___closed__3);
v___x_168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg(v___x_168_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_);
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
else
{
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandDeclId___boxed(lean_object* v_currNamespace_178_, lean_object* v_currLevelNames_179_, lean_object* v_declId_180_, lean_object* v_modifiers_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Elab_Term_expandDeclId(v_currNamespace_178_, v_currLevelNames_179_, v_declId_180_, v_modifiers_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec_ref(v_modifiers_181_);
lean_dec(v_declId_180_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0(lean_object* v_00_u03b1_190_, lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___redArg(v_msg_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0___boxed(lean_object* v_00_u03b1_200_, lean_object* v_msg_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0(v_00_u03b1_200_, v_msg_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1(lean_object* v_msgData_210_, lean_object* v_macroStack_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___redArg(v_msgData_210_, v_macroStack_211_, v___y_216_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1___boxed(lean_object* v_msgData_220_, lean_object* v_macroStack_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_expandDeclId_spec__0_spec__1(v_msgData_220_, v_macroStack_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
return v_res_229_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_unsigned_to_nat(2544510742u);
v___x_277_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_278_ = l_Lean_Name_num___override(v___x_277_, v___x_276_);
return v___x_278_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_281_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_);
v___x_282_ = l_Lean_Name_str___override(v___x_281_, v___x_280_);
return v___x_282_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_285_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_);
v___x_286_ = l_Lean_Name_str___override(v___x_285_, v___x_284_);
return v___x_286_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_unsigned_to_nat(2u);
v___x_288_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_);
v___x_289_ = l_Lean_Name_num___override(v___x_288_, v___x_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_303_; uint8_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_303_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_304_ = 0;
v___x_305_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_);
v___x_306_ = l_Lean_registerTraceClass(v___x_303_, v___x_304_, v___x_305_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec_ref_known(v___x_306_, 1);
v___x_307_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_308_ = l_Lean_registerTraceClass(v___x_307_, v___x_304_, v___x_305_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec_ref_known(v___x_308_, 1);
v___x_309_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_310_ = l_Lean_registerTraceClass(v___x_309_, v___x_304_, v___x_305_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec_ref_known(v___x_310_, 1);
v___x_311_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__31_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_312_ = l_Lean_registerTraceClass(v___x_311_, v___x_304_, v___x_305_);
return v___x_312_;
}
else
{
return v___x_310_;
}
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2____boxed(lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_();
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_(lean_object* v_x_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_box(0);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2____boxed(lean_object* v_x_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_(v_x_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v_x_321_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; 
v___f_337_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_));
v___x_338_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_));
v___x_339_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_));
v___x_340_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_));
v___x_341_ = 0;
v___x_342_ = lean_box(2);
v___x_343_ = 0;
v___x_344_ = l_Lean_registerTagAttribute(v___x_338_, v___x_339_, v___f_337_, v___x_340_, v___x_341_, v___x_342_, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2____boxed(lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_();
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1(){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_));
v___x_350_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___closed__0));
v___x_351_ = l_Lean_addBuiltinDocString(v___x_349_, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___boxed(lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1();
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3(){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_725559045____hygCtx___hyg_2_));
v___x_381_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___closed__6));
v___x_382_ = l_Lean_addBuiltinDeclarationRanges(v___x_380_, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3___boxed(lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_declRange__3();
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_428335796____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = l_Lean_NameSet_empty;
v___x_387_ = lean_st_mk_ref(v___x_386_);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_428335796____hygCtx___hyg_2____boxed(lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_428335796____hygCtx___hyg_2_();
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addBuiltinIncrementalElab(lean_object* v_decl_391_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_393_ = l_Lean_Elab_builtinIncrementalElabs;
v___x_394_ = lean_st_ref_take(v___x_393_);
v___x_395_ = l_Lean_NameSet_insert(v___x_394_, v_decl_391_);
v___x_396_ = lean_st_ref_put(v___x_393_, v___x_395_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addBuiltinIncrementalElab___boxed(lean_object* v_decl_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Elab_addBuiltinIncrementalElab(v_decl_398_);
return v_res_400_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_401_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_404_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_405_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_ctor_set(v___x_407_, 2, v___x_406_);
lean_ctor_set(v___x_407_, 3, v___x_406_);
lean_ctor_set(v___x_407_, 4, v___x_405_);
lean_ctor_set(v___x_407_, 5, v___x_405_);
lean_ctor_set(v___x_407_, 6, v___x_405_);
lean_ctor_set(v___x_407_, 7, v___x_405_);
lean_ctor_set(v___x_407_, 8, v___x_405_);
lean_ctor_set(v___x_407_, 9, v___x_405_);
lean_ctor_set(v___x_407_, 10, v___x_405_);
lean_ctor_set(v___x_407_, 11, v___x_404_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_unsigned_to_nat(32u);
v___x_409_ = lean_mk_empty_array_with_capacity(v___x_408_);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_411_ = ((size_t)5ULL);
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_unsigned_to_nat(32u);
v___x_414_ = lean_mk_empty_array_with_capacity(v___x_413_);
v___x_415_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_416_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
lean_ctor_set(v___x_416_, 2, v___x_412_);
lean_ctor_set(v___x_416_, 3, v___x_412_);
lean_ctor_set_usize(v___x_416_, 4, v___x_411_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_417_ = lean_box(1);
v___x_418_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_419_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_418_);
lean_ctor_set(v___x_420_, 2, v___x_417_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_425_; lean_object* v_toCold_426_; lean_object* v_env_427_; lean_object* v_options_428_; uint8_t v___x_429_; lean_object* v_env_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_425_ = lean_st_ref_get(v___y_423_);
v_toCold_426_ = lean_ctor_get(v___y_422_, 0);
v_env_427_ = lean_ctor_get(v___x_425_, 0);
lean_inc_ref(v_env_427_);
lean_dec(v___x_425_);
v_options_428_ = lean_ctor_get(v_toCold_426_, 2);
v___x_429_ = 0;
v_env_430_ = l_Lean_Environment_setRecordingDeps(v_env_427_, v___x_429_);
v___x_431_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_432_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_428_);
v___x_433_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_433_, 0, v_env_430_);
lean_ctor_set(v___x_433_, 1, v___x_431_);
lean_ctor_set(v___x_433_, 2, v___x_432_);
lean_ctor_set(v___x_433_, 3, v_options_428_);
v___x_434_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v_msgData_421_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0(v_msgData_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_ref_445_; lean_object* v___x_446_; lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
v_ref_445_ = lean_ctor_get(v___y_442_, 2);
v___x_446_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0_spec__0(v_msg_441_, v___y_442_, v___y_443_);
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_455_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
lean_inc(v_ref_445_);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v_ref_445_);
lean_ctor_set(v___x_451_, 1, v_a_447_);
if (v_isShared_450_ == 0)
{
lean_ctor_set_tag(v___x_449_, 1);
lean_ctor_set(v___x_449_, 0, v___x_451_);
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(v_msg_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
return v_res_460_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_463_ = l_Lean_stringToMessageData(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__2));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__4));
v___x_469_ = l_Lean_stringToMessageData(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg(lean_object* v_name_473_, uint8_t v_kind_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___y_484_; 
v___x_478_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_479_ = l_Lean_MessageData_ofName(v_name_473_);
v___x_480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__3);
v___x_482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_480_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
switch(v_kind_474_)
{
case 0:
{
lean_object* v___x_491_; 
v___x_491_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__6));
v___y_484_ = v___x_491_;
goto v___jp_483_;
}
case 1:
{
lean_object* v___x_492_; 
v___x_492_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__7));
v___y_484_ = v___x_492_;
goto v___jp_483_;
}
default: 
{
lean_object* v___x_493_; 
v___x_493_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__8));
v___y_484_ = v___x_493_;
goto v___jp_483_;
}
}
v___jp_483_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
lean_inc_ref(v___y_484_);
v___x_485_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_485_, 0, v___y_484_);
v___x_486_ = l_Lean_MessageData_ofFormat(v___x_485_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_482_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___closed__5);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(v___x_489_, v___y_475_, v___y_476_);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_name_494_, lean_object* v_kind_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
uint8_t v_kind_boxed_499_; lean_object* v_res_500_; 
v_kind_boxed_499_ = lean_unbox(v_kind_495_);
v_res_500_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg(v_name_494_, v_kind_boxed_499_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(lean_object* v___x_502_, lean_object* v___x_503_, lean_object* v___x_504_, lean_object* v_decl_505_, lean_object* v_stx_506_, uint8_t v_kind_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_506_, v___y_508_, v___y_509_);
if (lean_obj_tag(v___x_519_) == 0)
{
uint8_t v___x_520_; uint8_t v___x_521_; 
lean_dec_ref_known(v___x_519_, 1);
v___x_520_ = 0;
v___x_521_ = l_Lean_instBEqAttributeKind_beq(v_kind_507_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
lean_dec(v_decl_505_);
lean_dec_ref(v___x_503_);
lean_dec_ref(v___x_502_);
v___x_522_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg(v___x_504_, v_kind_507_, v___y_508_, v___y_509_);
return v___x_522_;
}
else
{
lean_dec(v___x_504_);
goto v___jp_511_;
}
}
else
{
lean_dec(v_decl_505_);
lean_dec(v___x_504_);
lean_dec_ref(v___x_503_);
lean_dec_ref(v___x_502_);
return v___x_519_;
}
v___jp_511_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_512_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___x_513_ = l_Lean_Name_mkStr3(v___x_502_, v___x_503_, v___x_512_);
v___x_514_ = lean_box(0);
v___x_515_ = l_Lean_mkConst(v___x_513_, v___x_514_);
lean_inc(v_decl_505_);
v___x_516_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_decl_505_);
v___x_517_ = l_Lean_Expr_app___override(v___x_515_, v___x_516_);
v___x_518_ = l_Lean_declareBuiltin(v_decl_505_, v___x_517_, v___y_508_, v___y_509_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(lean_object* v___x_523_, lean_object* v___x_524_, lean_object* v___x_525_, lean_object* v_decl_526_, lean_object* v_stx_527_, lean_object* v_kind_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v_kind_boxed_532_; lean_object* v_res_533_; 
v_kind_boxed_532_ = lean_unbox(v_kind_528_);
v_res_533_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(v___x_523_, v___x_524_, v___x_525_, v_decl_526_, v_stx_527_, v_kind_boxed_532_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
return v_res_533_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(lean_object* v___x_540_, lean_object* v_decl_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_545_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_);
v___x_546_ = l_Lean_MessageData_ofName(v___x_540_);
v___x_547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_);
v___x_549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(v___x_549_, v___y_542_, v___y_543_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(lean_object* v___x_551_, lean_object* v_decl_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(v___x_551_, v_decl_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v_decl_552_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_580_; lean_object* v_attr_581_; lean_object* v_toAttributeImplCore_582_; lean_object* v_descr_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_580_ = l_Lean_Elab_incrementalAttr;
v_attr_581_ = lean_ctor_get(v___x_580_, 0);
v_toAttributeImplCore_582_ = lean_ctor_get(v_attr_581_, 0);
v_descr_583_ = lean_ctor_get(v_toAttributeImplCore_582_, 2);
v___x_584_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___x_585_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___f_586_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___f_587_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___x_588_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___x_589_ = lean_string_append(v___x_588_, v_descr_583_);
v___x_590_ = 1;
v___x_591_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_591_, 0, v___x_584_);
lean_ctor_set(v___x_591_, 1, v___x_585_);
lean_ctor_set(v___x_591_, 2, v___x_589_);
lean_ctor_set_uint8(v___x_591_, sizeof(void*)*3, v___x_590_);
v___x_592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___f_586_);
lean_ctor_set(v___x_592_, 2, v___f_587_);
v___x_593_ = l_Lean_registerBuiltinAttribute(v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_();
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_596_, lean_object* v_msg_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___redArg(v_msg_597_, v___y_598_, v___y_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_602_, lean_object* v_msg_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_throwError___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__0(v_00_u03b1_602_, v_msg_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_608_, lean_object* v_name_609_, uint8_t v_kind_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___redArg(v_name_609_, v_kind_610_, v___y_611_, v___y_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_615_, lean_object* v_name_616_, lean_object* v_kind_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
uint8_t v_kind_boxed_621_; lean_object* v_res_622_; 
v_kind_boxed_621_ = lean_unbox(v_kind_617_);
v_res_622_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2__spec__1(v_00_u03b1_615_, v_name_616_, v_kind_boxed_621_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___regBuiltin___private_Lean_Elab_Term_0__Lean_Elab_initFn_docString__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_));
v___x_625_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_incrementalAttr___regBuiltin_Lean_Elab_incrementalAttr_docString__1___closed__0));
v___x_626_ = l_Lean_addBuiltinDocString(v___x_624_, v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn___regBuiltin___private_Lean_Elab_Term_0__Lean_Elab_initFn_docString__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2____boxed(lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn___regBuiltin___private_Lean_Elab_Term_0__Lean_Elab_initFn_docString__1_00___x40_Lean_Elab_Term_2114473129____hygCtx___hyg_2_();
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__0(lean_object* v___x_629_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_st_ref_get(v___x_629_);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__0___boxed(lean_object* v___x_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Elab_isIncrementalElab___redArg___lam__0(v___x_633_);
lean_dec(v___x_633_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__1(lean_object* v_decl_636_, lean_object* v_toPure_637_, lean_object* v_____do__lift_638_){
_start:
{
uint8_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = l_Lean_NameSet_contains(v_____do__lift_638_, v_decl_636_);
v___x_640_ = lean_box(v___x_639_);
v___x_641_ = lean_apply_2(v_toPure_637_, lean_box(0), v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__1___boxed(lean_object* v_decl_642_, lean_object* v_toPure_643_, lean_object* v_____do__lift_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Elab_isIncrementalElab___redArg___lam__1(v_decl_642_, v_toPure_643_, v_____do__lift_644_);
lean_dec(v_____do__lift_644_);
lean_dec(v_decl_642_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__2(lean_object* v_decl_646_, lean_object* v_toPure_647_, lean_object* v_____do__lift_648_){
_start:
{
lean_object* v___x_649_; uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_649_ = l_Lean_Elab_incrementalAttr;
v___x_650_ = l_Lean_TagAttribute_hasTag(v___x_649_, v_____do__lift_648_, v_decl_646_);
v___x_651_ = lean_box(v___x_650_);
v___x_652_ = lean_apply_2(v_toPure_647_, lean_box(0), v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__3(lean_object* v_inst_653_, lean_object* v_toBind_654_, lean_object* v___f_655_, lean_object* v_toPure_656_, uint8_t v_b_657_){
_start:
{
if (v_b_657_ == 0)
{
lean_object* v_getEnv_658_; lean_object* v___x_659_; 
lean_dec(v_toPure_656_);
v_getEnv_658_ = lean_ctor_get(v_inst_653_, 0);
lean_inc(v_getEnv_658_);
lean_dec_ref(v_inst_653_);
v___x_659_ = lean_apply_4(v_toBind_654_, lean_box(0), lean_box(0), v_getEnv_658_, v___f_655_);
return v___x_659_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec(v___f_655_);
lean_dec(v_toBind_654_);
lean_dec_ref(v_inst_653_);
v___x_660_ = lean_box(v_b_657_);
v___x_661_ = lean_apply_2(v_toPure_656_, lean_box(0), v___x_660_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg___lam__3___boxed(lean_object* v_inst_662_, lean_object* v_toBind_663_, lean_object* v___f_664_, lean_object* v_toPure_665_, lean_object* v_b_666_){
_start:
{
uint8_t v_b_boxed_667_; lean_object* v_res_668_; 
v_b_boxed_667_ = lean_unbox(v_b_666_);
v_res_668_ = l_Lean_Elab_isIncrementalElab___redArg___lam__3(v_inst_662_, v_toBind_663_, v___f_664_, v_toPure_665_, v_b_boxed_667_);
return v_res_668_;
}
}
static lean_object* _init_l_Lean_Elab_isIncrementalElab___redArg___closed__0(void){
_start:
{
lean_object* v___x_669_; lean_object* v___f_670_; 
v___x_669_ = l_Lean_Elab_builtinIncrementalElabs;
v___f_670_ = lean_alloc_closure((void*)(l_Lean_Elab_isIncrementalElab___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_670_, 0, v___x_669_);
return v___f_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___redArg(lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_decl_674_){
_start:
{
lean_object* v_toApplicative_675_; lean_object* v_toBind_676_; lean_object* v_toPure_677_; lean_object* v___f_678_; lean_object* v___x_679_; lean_object* v___f_680_; lean_object* v___f_681_; lean_object* v___f_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_toApplicative_675_ = lean_ctor_get(v_inst_671_, 0);
lean_inc_ref(v_toApplicative_675_);
v_toBind_676_ = lean_ctor_get(v_inst_671_, 1);
lean_inc_n(v_toBind_676_, 3);
lean_dec_ref(v_inst_671_);
v_toPure_677_ = lean_ctor_get(v_toApplicative_675_, 1);
lean_inc_n(v_toPure_677_, 3);
lean_dec_ref(v_toApplicative_675_);
v___f_678_ = lean_obj_once(&l_Lean_Elab_isIncrementalElab___redArg___closed__0, &l_Lean_Elab_isIncrementalElab___redArg___closed__0_once, _init_l_Lean_Elab_isIncrementalElab___redArg___closed__0);
v___x_679_ = lean_apply_2(v_inst_673_, lean_box(0), v___f_678_);
lean_inc(v_decl_674_);
v___f_680_ = lean_alloc_closure((void*)(l_Lean_Elab_isIncrementalElab___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_680_, 0, v_decl_674_);
lean_closure_set(v___f_680_, 1, v_toPure_677_);
v___f_681_ = lean_alloc_closure((void*)(l_Lean_Elab_isIncrementalElab___redArg___lam__2), 3, 2);
lean_closure_set(v___f_681_, 0, v_decl_674_);
lean_closure_set(v___f_681_, 1, v_toPure_677_);
v___f_682_ = lean_alloc_closure((void*)(l_Lean_Elab_isIncrementalElab___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_682_, 0, v_inst_672_);
lean_closure_set(v___f_682_, 1, v_toBind_676_);
lean_closure_set(v___f_682_, 2, v___f_681_);
lean_closure_set(v___f_682_, 3, v_toPure_677_);
v___x_683_ = lean_apply_4(v_toBind_676_, lean_box(0), lean_box(0), v___x_679_, v___f_680_);
v___x_684_ = lean_apply_4(v_toBind_676_, lean_box(0), lean_box(0), v___x_683_, v___f_682_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab(lean_object* v_m_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_decl_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Elab_isIncrementalElab___redArg(v_inst_686_, v_inst_687_, v_inst_688_, v_decl_689_);
return v___x_690_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_unsigned_to_nat(3314678858u);
v___x_696_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_697_ = l_Lean_Name_num___override(v___x_696_, v___x_695_);
return v___x_697_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_699_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_);
v___x_700_ = l_Lean_Name_str___override(v___x_699_, v___x_698_);
return v___x_700_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Term_2544510742____hygCtx___hyg_2_));
v___x_702_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_);
v___x_703_ = l_Lean_Name_str___override(v___x_702_, v___x_701_);
return v___x_703_;
}
}
static lean_object* _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_unsigned_to_nat(2u);
v___x_705_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_);
v___x_706_ = l_Lean_Name_num___override(v___x_705_, v___x_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_708_ = ((lean_object*)(l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_));
v___x_709_ = 0;
v___x_710_ = lean_obj_once(&l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_, &l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Term_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_);
v___x_711_ = l_Lean_registerTraceClass(v___x_708_, v___x_709_, v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2____boxed(lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___private_Lean_Elab_Term_0__Lean_Elab_initFn_00___x40_Lean_Elab_Term_3314678858____hygCtx___hyg_2_();
return v_res_713_;
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
