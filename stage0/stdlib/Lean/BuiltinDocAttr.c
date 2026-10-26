// Lean compiler output
// Module: Lean.BuiltinDocAttr
// Imports: public import Lean.Compiler.InitAttr import Lean.DocString.Markdown
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_builtinDeclRanges;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t l_Lean_isAuxRecursor(lean_object*, lean_object*);
uint8_t l_Lean_isNoConfusion(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_findSimpleDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_declareBuiltinDocStringAndRanges___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__0 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__0_value;
static const lean_string_object l_Lean_declareBuiltinDocStringAndRanges___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "addBuiltinDeclarationRanges"};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__1 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__1_value;
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__2_value_aux_0),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 90, 197, 82, 236, 73, 141, 50)}};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__2 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__2_value;
static lean_once_cell_t l_Lean_declareBuiltinDocStringAndRanges___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__3;
static const lean_string_object l_Lean_declareBuiltinDocStringAndRanges___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "DeclarationRanges"};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__4 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__4_value;
static const lean_string_object l_Lean_declareBuiltinDocStringAndRanges___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__5 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__5_value;
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__6_value_aux_0),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__4_value),LEAN_SCALAR_PTR_LITERAL(175, 178, 233, 239, 130, 231, 201, 68)}};
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__6_value_aux_1),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__5_value),LEAN_SCALAR_PTR_LITERAL(131, 154, 194, 162, 5, 60, 128, 221)}};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__6 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__6_value;
static lean_once_cell_t l_Lean_declareBuiltinDocStringAndRanges___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__7;
static const lean_string_object l_Lean_declareBuiltinDocStringAndRanges___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "DeclarationRange"};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__8 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__8_value;
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__9_value_aux_0),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__8_value),LEAN_SCALAR_PTR_LITERAL(64, 40, 210, 72, 47, 189, 205, 127)}};
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__9_value_aux_1),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__5_value),LEAN_SCALAR_PTR_LITERAL(56, 158, 56, 135, 240, 198, 44, 53)}};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__9 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__9_value;
static lean_once_cell_t l_Lean_declareBuiltinDocStringAndRanges___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__10;
static const lean_string_object l_Lean_declareBuiltinDocStringAndRanges___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Position"};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__11 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__11_value;
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__12_value_aux_0),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__11_value),LEAN_SCALAR_PTR_LITERAL(65, 243, 169, 21, 0, 54, 19, 101)}};
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__12_value_aux_1),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__5_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 160, 114, 110, 41, 100, 154)}};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__12 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__12_value;
static lean_once_cell_t l_Lean_declareBuiltinDocStringAndRanges___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__13;
static const lean_string_object l_Lean_declareBuiltinDocStringAndRanges___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "declRange"};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__14 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__14_value;
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__14_value),LEAN_SCALAR_PTR_LITERAL(226, 15, 94, 125, 84, 10, 192, 46)}};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__15 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__15_value;
static const lean_string_object l_Lean_declareBuiltinDocStringAndRanges___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "docString"};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__16 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__16_value;
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__16_value),LEAN_SCALAR_PTR_LITERAL(252, 97, 215, 39, 22, 62, 121, 128)}};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__17 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__17_value;
static const lean_string_object l_Lean_declareBuiltinDocStringAndRanges___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "addBuiltinDocString"};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__18 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__18_value;
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_declareBuiltinDocStringAndRanges___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__19_value_aux_0),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__18_value),LEAN_SCALAR_PTR_LITERAL(9, 163, 17, 40, 184, 219, 245, 11)}};
static const lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__19 = (const lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__19_value;
static lean_once_cell_t l_Lean_declareBuiltinDocStringAndRanges___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_declareBuiltinDocStringAndRanges___closed__20;
LEAN_EXPORT lean_object* l_Lean_declareBuiltinDocStringAndRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_declareBuiltinDocStringAndRanges___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__4_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "BuiltinDocAttr"};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__4_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__4_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__5_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__4_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(91, 148, 208, 29, 123, 175, 125, 94)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__5_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__5_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__6_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__5_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(230, 182, 140, 9, 34, 229, 213, 109)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__6_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__6_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__7_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__6_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 38, 189, 40, 25, 183, 19, 195)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__7_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__7_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__8_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__8_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__8_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__9_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__7_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__8_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(110, 25, 10, 13, 149, 117, 173, 109)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__9_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__9_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__10_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__10_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__10_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__11_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__9_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__10_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 125, 112, 156, 204, 49, 229, 228)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__11_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__11_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__12_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__11_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)&l_Lean_declareBuiltinDocStringAndRanges___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 92, 201, 214, 11, 139, 210, 230)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__12_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__12_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__13_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__12_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__4_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 82, 85, 112, 42, 136, 249, 78)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__13_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__13_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__14_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__13_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)(((size_t)(939411776) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(58, 174, 188, 136, 99, 39, 4, 74)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__14_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__14_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__15_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__15_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__15_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__16_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__14_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__15_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(21, 116, 134, 16, 18, 32, 192, 44)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__16_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__16_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__17_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__17_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__17_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__18_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__16_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__17_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 231, 138, 33, 2, 104, 69, 176)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__18_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__18_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__19_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__18_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(88, 27, 218, 162, 220, 195, 65, 101)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__19_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__19_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__20_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "builtin_doc"};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__20_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__20_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__21_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__20_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(159, 139, 112, 191, 70, 175, 106, 62)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__21_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__21_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__22_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__21_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__22_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__22_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__23_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "make the docs and location of this declaration available as a builtin"};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__23_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__23_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__24_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__19_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__21_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__23_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__24_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__24_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__25_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__24_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__22_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__25_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__25_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 290, .m_capacity = 290, .m_length = 289, .m_data = "Makes the documentation and location of a declaration available as a builtin.\n\nThis allows the documentation of core Lean features to be visible without importing the file they\nare defined in. This is only useful during bootstrapping and should not be used outside of\nthe Lean source code."};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(lean_object* v_declName_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_env_5_; lean_object* v___x_6_; lean_object* v_env_7_; lean_object* v___x_8_; lean_object* v_toEnvExtension_9_; lean_object* v_asyncMode_10_; uint8_t v___x_11_; lean_object* v___x_12_; 
v___x_4_ = lean_st_ref_get(v___y_2_);
v_env_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_env_5_);
lean_dec(v___x_4_);
v___x_6_ = lean_st_ref_get(v___y_2_);
v_env_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_env_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_declRangeExt;
v_toEnvExtension_9_ = lean_ctor_get(v___x_8_, 0);
v_asyncMode_10_ = lean_ctor_get(v_toEnvExtension_9_, 2);
v___x_11_ = 0;
lean_inc(v_declName_1_);
v___x_12_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_8_, v_env_5_, v_declName_1_, v_asyncMode_10_, v___x_11_);
if (lean_obj_tag(v___x_12_) == 0)
{
uint8_t v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = 1;
v___x_14_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_8_, v_env_7_, v_declName_1_, v_asyncMode_10_, v___x_13_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
else
{
lean_object* v___x_16_; 
lean_dec_ref(v_env_7_);
lean_dec(v_declName_1_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_12_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg___boxed(lean_object* v_declName_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(v_declName_17_, v___y_18_);
lean_dec(v___y_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(lean_object* v_declName_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; lean_object* v_env_25_; uint8_t v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_env_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_25_);
lean_dec(v___x_24_);
v___x_26_ = l_Lean_isRecCore(v_env_25_, v_declName_21_);
v___x_27_ = lean_box(v___x_26_);
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg___boxed(lean_object* v_declName_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(v_declName_29_, v___y_30_);
lean_dec(v___y_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0(lean_object* v_declName_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_ranges_38_; lean_object* v___x_44_; lean_object* v_env_45_; lean_object* v___x_46_; lean_object* v_a_47_; uint8_t v___x_52_; 
v___x_44_ = lean_st_ref_get(v___y_35_);
v_env_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc_ref_n(v_env_45_, 2);
lean_dec(v___x_44_);
lean_inc_n(v_declName_33_, 2);
v___x_46_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(v_declName_33_, v___y_35_);
v_a_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_47_);
lean_dec_ref(v___x_46_);
v___x_52_ = l_Lean_isAuxRecursor(v_env_45_, v_declName_33_);
if (v___x_52_ == 0)
{
uint8_t v___x_53_; 
lean_inc(v_declName_33_);
v___x_53_ = l_Lean_isNoConfusion(v_env_45_, v_declName_33_);
if (v___x_53_ == 0)
{
uint8_t v___x_54_; 
v___x_54_ = lean_unbox(v_a_47_);
lean_dec(v_a_47_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; lean_object* v_a_56_; 
lean_inc(v_declName_33_);
v___x_55_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(v_declName_33_, v___y_35_);
v_a_56_ = lean_ctor_get(v___x_55_, 0);
lean_inc(v_a_56_);
lean_dec_ref(v___x_55_);
v_ranges_38_ = v_a_56_;
goto v___jp_37_;
}
else
{
goto v___jp_48_;
}
}
else
{
lean_dec(v_a_47_);
goto v___jp_48_;
}
}
else
{
lean_dec(v_a_47_);
lean_dec_ref(v_env_45_);
goto v___jp_48_;
}
v___jp_37_:
{
if (lean_obj_tag(v_ranges_38_) == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_39_ = l_Lean_builtinDeclRanges;
v___x_40_ = lean_st_ref_get(v___x_39_);
v___x_41_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_40_, v_declName_33_);
lean_dec(v_declName_33_);
lean_dec(v___x_40_);
v___x_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
return v___x_42_;
}
else
{
lean_object* v___x_43_; 
lean_dec(v_declName_33_);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v_ranges_38_);
return v___x_43_;
}
}
v___jp_48_:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v_a_51_; 
v___x_49_ = l_Lean_Name_getPrefix(v_declName_33_);
v___x_50_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(v___x_49_, v___y_35_);
v_a_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_a_51_);
lean_dec_ref(v___x_50_);
v_ranges_38_ = v_a_51_;
goto v___jp_37_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0___boxed(lean_object* v_declName_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0(v_declName_57_, v___y_58_, v___y_59_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_61_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__3(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_box(0);
v___x_68_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__2));
v___x_69_ = l_Lean_mkConst(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__7(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_box(0);
v___x_77_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__6));
v___x_78_ = l_Lean_mkConst(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__10(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_box(0);
v___x_85_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__9));
v___x_86_ = l_Lean_mkConst(v___x_85_, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__13(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_box(0);
v___x_93_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__12));
v___x_94_ = l_Lean_mkConst(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__20(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_box(0);
v___x_106_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__19));
v___x_107_ = l_Lean_mkConst(v___x_106_, v___x_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_declareBuiltinDocStringAndRanges(lean_object* v_declName_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___y_113_; lean_object* v___y_114_; lean_object* v___x_204_; lean_object* v_env_205_; lean_object* v_ref_206_; uint8_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_204_ = lean_st_ref_get(v_a_110_);
v_env_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc_ref(v_env_205_);
lean_dec(v___x_204_);
v_ref_206_ = lean_ctor_get(v_a_109_, 2);
v___x_207_ = 0;
v___x_208_ = l_Lean_Options_empty;
v___x_209_ = lean_box(0);
v___x_210_ = lean_box(0);
v___x_211_ = lean_box(0);
lean_inc(v_declName_108_);
v___x_212_ = l_Lean_findSimpleDocString_x3f(v_env_205_, v_declName_108_, v___x_207_, v___x_208_, v___x_209_, v___x_210_, v___x_211_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_212_, 1);
if (lean_obj_tag(v_a_213_) == 1)
{
lean_object* v_val_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_val_214_ = lean_ctor_get(v_a_213_, 0);
lean_inc(v_val_214_);
lean_dec_ref_known(v_a_213_, 1);
v___x_215_ = l_String_removeLeadingSpaces(v_val_214_);
v___x_216_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__17));
lean_inc_n(v_declName_108_, 2);
v___x_217_ = l_Lean_Name_append(v_declName_108_, v___x_216_);
v___x_218_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__20, &l_Lean_declareBuiltinDocStringAndRanges___closed__20_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__20);
v___x_219_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_108_);
v___x_220_ = l_Lean_mkStrLit(v___x_215_);
v___x_221_ = lean_unsigned_to_nat(2u);
v___x_222_ = lean_mk_empty_array_with_capacity(v___x_221_);
v___x_223_ = lean_array_push(v___x_222_, v___x_219_);
v___x_224_ = lean_array_push(v___x_223_, v___x_220_);
v___x_225_ = l_Lean_mkAppN(v___x_218_, v___x_224_);
lean_dec_ref(v___x_224_);
v___x_226_ = l_Lean_declareBuiltin(v___x_217_, v___x_225_, v_a_109_, v_a_110_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_dec_ref_known(v___x_226_, 1);
v___y_113_ = v_a_109_;
v___y_114_ = v_a_110_;
goto v___jp_112_;
}
else
{
lean_dec(v_declName_108_);
return v___x_226_;
}
}
else
{
lean_dec(v_a_213_);
v___y_113_ = v_a_109_;
v___y_114_ = v_a_110_;
goto v___jp_112_;
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_238_; 
lean_dec(v_declName_108_);
v_a_227_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_238_ == 0)
{
v___x_229_ = v___x_212_;
v_isShared_230_ = v_isSharedCheck_238_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_212_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_238_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_231_ = lean_io_error_to_string(v_a_227_);
v___x_232_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
v___x_233_ = l_Lean_MessageData_ofFormat(v___x_232_);
lean_inc(v_ref_206_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v_ref_206_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_234_);
v___x_236_ = v___x_229_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
v___jp_112_:
{
lean_object* v___x_115_; 
lean_inc(v_declName_108_);
v___x_115_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0(v_declName_108_, v___y_113_, v___y_114_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_195_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_195_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_195_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_195_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
if (lean_obj_tag(v_a_116_) == 1)
{
lean_object* v_val_120_; lean_object* v_range_121_; lean_object* v_selectionRange_122_; lean_object* v___x_123_; lean_object* v_pos_124_; lean_object* v_charUtf16_125_; lean_object* v_endPos_126_; lean_object* v_endCharUtf16_127_; lean_object* v___x_128_; lean_object* v_line_129_; lean_object* v_column_130_; lean_object* v_line_131_; lean_object* v_column_132_; lean_object* v___x_133_; lean_object* v_pos_134_; lean_object* v_charUtf16_135_; lean_object* v_endPos_136_; lean_object* v_endCharUtf16_137_; lean_object* v_line_138_; lean_object* v_column_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v_line_148_; lean_object* v_column_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
lean_del_object(v___x_118_);
v_val_120_ = lean_ctor_get(v_a_116_, 0);
lean_inc(v_val_120_);
lean_dec_ref_known(v_a_116_, 1);
v_range_121_ = lean_ctor_get(v_val_120_, 0);
lean_inc_ref(v_range_121_);
v_selectionRange_122_ = lean_ctor_get(v_val_120_, 1);
lean_inc_ref(v_selectionRange_122_);
lean_dec(v_val_120_);
v___x_123_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__3, &l_Lean_declareBuiltinDocStringAndRanges___closed__3_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__3);
v_pos_124_ = lean_ctor_get(v_range_121_, 0);
lean_inc_ref(v_pos_124_);
v_charUtf16_125_ = lean_ctor_get(v_range_121_, 1);
lean_inc(v_charUtf16_125_);
v_endPos_126_ = lean_ctor_get(v_range_121_, 2);
lean_inc_ref(v_endPos_126_);
v_endCharUtf16_127_ = lean_ctor_get(v_range_121_, 3);
lean_inc(v_endCharUtf16_127_);
lean_dec_ref(v_range_121_);
v___x_128_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__7, &l_Lean_declareBuiltinDocStringAndRanges___closed__7_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__7);
v_line_129_ = lean_ctor_get(v_pos_124_, 0);
lean_inc(v_line_129_);
v_column_130_ = lean_ctor_get(v_pos_124_, 1);
lean_inc(v_column_130_);
lean_dec_ref(v_pos_124_);
v_line_131_ = lean_ctor_get(v_endPos_126_, 0);
lean_inc(v_line_131_);
v_column_132_ = lean_ctor_get(v_endPos_126_, 1);
lean_inc(v_column_132_);
lean_dec_ref(v_endPos_126_);
v___x_133_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__10, &l_Lean_declareBuiltinDocStringAndRanges___closed__10_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__10);
v_pos_134_ = lean_ctor_get(v_selectionRange_122_, 0);
lean_inc_ref(v_pos_134_);
v_charUtf16_135_ = lean_ctor_get(v_selectionRange_122_, 1);
lean_inc(v_charUtf16_135_);
v_endPos_136_ = lean_ctor_get(v_selectionRange_122_, 2);
lean_inc_ref(v_endPos_136_);
v_endCharUtf16_137_ = lean_ctor_get(v_selectionRange_122_, 3);
lean_inc(v_endCharUtf16_137_);
lean_dec_ref(v_selectionRange_122_);
v_line_138_ = lean_ctor_get(v_pos_134_, 0);
lean_inc(v_line_138_);
v_column_139_ = lean_ctor_get(v_pos_134_, 1);
lean_inc(v_column_139_);
lean_dec_ref(v_pos_134_);
v___x_140_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__13, &l_Lean_declareBuiltinDocStringAndRanges___closed__13_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__13);
v___x_141_ = l_Lean_mkNatLit(v_line_129_);
v___x_142_ = l_Lean_mkNatLit(v_column_130_);
v___x_143_ = lean_unsigned_to_nat(2u);
v___x_144_ = lean_mk_empty_array_with_capacity(v___x_143_);
lean_inc_ref_n(v___x_144_, 5);
v___x_145_ = lean_array_push(v___x_144_, v___x_141_);
v___x_146_ = lean_array_push(v___x_145_, v___x_142_);
v___x_147_ = l_Lean_mkAppN(v___x_140_, v___x_146_);
lean_dec_ref(v___x_146_);
v_line_148_ = lean_ctor_get(v_endPos_136_, 0);
lean_inc(v_line_148_);
v_column_149_ = lean_ctor_get(v_endPos_136_, 1);
lean_inc(v_column_149_);
lean_dec_ref(v_endPos_136_);
v___x_150_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__15));
lean_inc(v_declName_108_);
v___x_151_ = l_Lean_Name_append(v_declName_108_, v___x_150_);
v___x_152_ = l_Lean_mkNatLit(v_line_131_);
v___x_153_ = l_Lean_mkNatLit(v_column_132_);
v___x_154_ = lean_array_push(v___x_144_, v___x_152_);
v___x_155_ = lean_array_push(v___x_154_, v___x_153_);
v___x_156_ = l_Lean_mkAppN(v___x_140_, v___x_155_);
lean_dec_ref(v___x_155_);
v___x_157_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_108_);
v___x_158_ = l_Lean_mkNatLit(v_charUtf16_125_);
v___x_159_ = l_Lean_mkNatLit(v_endCharUtf16_127_);
v___x_160_ = lean_unsigned_to_nat(4u);
v___x_161_ = lean_mk_empty_array_with_capacity(v___x_160_);
lean_inc_ref(v___x_161_);
v___x_162_ = lean_array_push(v___x_161_, v___x_147_);
v___x_163_ = lean_array_push(v___x_162_, v___x_158_);
v___x_164_ = lean_array_push(v___x_163_, v___x_156_);
v___x_165_ = lean_array_push(v___x_164_, v___x_159_);
v___x_166_ = l_Lean_mkAppN(v___x_133_, v___x_165_);
lean_dec_ref(v___x_165_);
v___x_167_ = l_Lean_mkNatLit(v_line_138_);
v___x_168_ = l_Lean_mkNatLit(v_column_139_);
v___x_169_ = lean_array_push(v___x_144_, v___x_167_);
v___x_170_ = lean_array_push(v___x_169_, v___x_168_);
v___x_171_ = l_Lean_mkAppN(v___x_140_, v___x_170_);
lean_dec_ref(v___x_170_);
v___x_172_ = l_Lean_mkNatLit(v_charUtf16_135_);
v___x_173_ = l_Lean_mkNatLit(v_line_148_);
v___x_174_ = l_Lean_mkNatLit(v_column_149_);
v___x_175_ = lean_array_push(v___x_144_, v___x_173_);
v___x_176_ = lean_array_push(v___x_175_, v___x_174_);
v___x_177_ = l_Lean_mkAppN(v___x_140_, v___x_176_);
lean_dec_ref(v___x_176_);
v___x_178_ = l_Lean_mkNatLit(v_endCharUtf16_137_);
v___x_179_ = lean_array_push(v___x_161_, v___x_171_);
v___x_180_ = lean_array_push(v___x_179_, v___x_172_);
v___x_181_ = lean_array_push(v___x_180_, v___x_177_);
v___x_182_ = lean_array_push(v___x_181_, v___x_178_);
v___x_183_ = l_Lean_mkAppN(v___x_133_, v___x_182_);
lean_dec_ref(v___x_182_);
v___x_184_ = lean_array_push(v___x_144_, v___x_166_);
v___x_185_ = lean_array_push(v___x_184_, v___x_183_);
v___x_186_ = l_Lean_mkAppN(v___x_128_, v___x_185_);
lean_dec_ref(v___x_185_);
v___x_187_ = lean_array_push(v___x_144_, v___x_157_);
v___x_188_ = lean_array_push(v___x_187_, v___x_186_);
v___x_189_ = l_Lean_mkAppN(v___x_123_, v___x_188_);
lean_dec_ref(v___x_188_);
v___x_190_ = l_Lean_declareBuiltin(v___x_151_, v___x_189_, v___y_113_, v___y_114_);
return v___x_190_;
}
else
{
lean_object* v___x_191_; lean_object* v___x_193_; 
lean_dec(v_a_116_);
lean_dec(v_declName_108_);
v___x_191_ = lean_box(0);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_191_);
v___x_193_ = v___x_118_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec(v_declName_108_);
v_a_196_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_115_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_115_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_declareBuiltinDocStringAndRanges___boxed(lean_object* v_declName_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_239_, v_a_240_, v_a_241_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0(lean_object* v_declName_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(v_declName_244_, v___y_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___boxed(lean_object* v_declName_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0(v_declName_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1(lean_object* v_declName_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(v_declName_254_, v___y_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___boxed(lean_object* v_declName_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1(v_declName_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(lean_object* v_decl_264_, lean_object* v_stx_265_, uint8_t v_x_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_265_, v___y_267_, v___y_268_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_271_; 
lean_dec_ref_known(v___x_270_, 1);
v___x_271_ = l_Lean_declareBuiltinDocStringAndRanges(v_decl_264_, v___y_267_, v___y_268_);
return v___x_271_;
}
else
{
lean_dec(v_decl_264_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object* v_decl_272_, lean_object* v_stx_273_, lean_object* v_x_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
uint8_t v_x_1092__boxed_278_; lean_object* v_res_279_; 
v_x_1092__boxed_278_ = lean_unbox(v_x_274_);
v_res_279_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(v_decl_272_, v_stx_273_, v_x_1092__boxed_278_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_279_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_280_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_283_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_284_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
lean_ctor_set(v___x_286_, 2, v___x_285_);
lean_ctor_set(v___x_286_, 3, v___x_285_);
lean_ctor_set(v___x_286_, 4, v___x_284_);
lean_ctor_set(v___x_286_, 5, v___x_284_);
lean_ctor_set(v___x_286_, 6, v___x_284_);
lean_ctor_set(v___x_286_, 7, v___x_284_);
lean_ctor_set(v___x_286_, 8, v___x_284_);
lean_ctor_set(v___x_286_, 9, v___x_284_);
lean_ctor_set(v___x_286_, 10, v___x_284_);
lean_ctor_set(v___x_286_, 11, v___x_283_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_unsigned_to_nat(32u);
v___x_288_ = lean_mk_empty_array_with_capacity(v___x_287_);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_290_ = ((size_t)5ULL);
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = lean_unsigned_to_nat(32u);
v___x_293_ = lean_mk_empty_array_with_capacity(v___x_292_);
v___x_294_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_295_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
lean_ctor_set(v___x_295_, 2, v___x_291_);
lean_ctor_set(v___x_295_, 3, v___x_291_);
lean_ctor_set_usize(v___x_295_, 4, v___x_290_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_296_ = lean_box(1);
v___x_297_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_298_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
lean_ctor_set(v___x_299_, 2, v___x_296_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; lean_object* v_toCold_305_; lean_object* v_env_306_; lean_object* v_options_307_; uint8_t v___x_308_; lean_object* v_env_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_304_ = lean_st_ref_get(v___y_302_);
v_toCold_305_ = lean_ctor_get(v___y_301_, 0);
v_env_306_ = lean_ctor_get(v___x_304_, 0);
lean_inc_ref(v_env_306_);
lean_dec(v___x_304_);
v_options_307_ = lean_ctor_get(v_toCold_305_, 2);
v___x_308_ = 0;
v_env_309_ = l_Lean_Environment_setRecordingDeps(v_env_306_, v___x_308_);
v___x_310_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_311_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_307_);
v___x_312_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_312_, 0, v_env_309_);
lean_ctor_set(v___x_312_, 1, v___x_310_);
lean_ctor_set(v___x_312_, 2, v___x_311_);
lean_ctor_set(v___x_312_, 3, v_options_307_);
v___x_313_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v_msgData_300_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0(v_msgData_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_ref_324_; lean_object* v___x_325_; lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_334_; 
v_ref_324_ = lean_ctor_get(v___y_321_, 2);
v___x_325_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0(v_msg_320_, v___y_321_, v___y_322_);
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_334_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
lean_inc(v_ref_324_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v_ref_324_);
lean_ctor_set(v___x_330_, 1, v_a_326_);
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 1);
lean_ctor_set(v___x_328_, 0, v___x_330_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(v_msg_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_339_;
}
}
static lean_object* _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_345_ = l_Lean_stringToMessageData(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(lean_object* v___x_346_, lean_object* v_decl_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_351_ = lean_obj_once(&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_, &l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__once, _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_);
v___x_352_ = l_Lean_MessageData_ofName(v___x_346_);
v___x_353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_351_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_obj_once(&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_, &l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__once, _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_);
v___x_355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_353_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(v___x_355_, v___y_348_, v___y_349_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object* v___x_357_, lean_object* v_decl_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(v___x_357_, v_decl_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v_decl_358_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__25_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_426_ = l_Lean_registerBuiltinAttribute(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_429_, lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(v_msg_430_, v___y_431_, v___y_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_435_, lean_object* v_msg_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0(v_00_u03b1_435_, v_msg_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__19_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_444_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_445_ = l_Lean_addBuiltinDocString(v___x_443_, v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
return v_res_447_;
}
}
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Markdown(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_BuiltinDocAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Markdown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_BuiltinDocAttr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* initialize_Lean_DocString_Markdown(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_BuiltinDocAttr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Markdown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_BuiltinDocAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_BuiltinDocAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_BuiltinDocAttr(builtin);
}
#ifdef __cplusplus
}
#endif
