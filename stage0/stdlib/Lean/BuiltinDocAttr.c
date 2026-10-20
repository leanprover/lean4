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
extern lean_object* l_Lean_instInhabitedDeclarationRanges_default;
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v_env_6_; lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_toEnvExtension_10_; lean_object* v_asyncMode_11_; uint8_t v___x_12_; lean_object* v___x_13_; 
v___x_4_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_5_ = lean_st_ref_get(v___y_2_);
v_env_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc_ref(v_env_6_);
lean_dec(v___x_5_);
v___x_7_ = lean_st_ref_get(v___y_2_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = l_Lean_declRangeExt;
v_toEnvExtension_10_ = lean_ctor_get(v___x_9_, 0);
v_asyncMode_11_ = lean_ctor_get(v_toEnvExtension_10_, 2);
v___x_12_ = 0;
lean_inc(v_declName_1_);
v___x_13_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4_, v___x_9_, v_env_6_, v_declName_1_, v_asyncMode_11_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = 1;
v___x_15_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4_, v___x_9_, v_env_8_, v_declName_1_, v_asyncMode_11_, v___x_14_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; 
lean_dec_ref(v_env_8_);
lean_dec(v_declName_1_);
v___x_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_13_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg___boxed(lean_object* v_declName_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(v_declName_18_, v___y_19_);
lean_dec(v___y_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(lean_object* v_declName_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_25_; lean_object* v_env_26_; uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_25_ = lean_st_ref_get(v___y_23_);
v_env_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc_ref(v_env_26_);
lean_dec(v___x_25_);
v___x_27_ = l_Lean_isRecCore(v_env_26_, v_declName_22_);
v___x_28_ = lean_box(v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg___boxed(lean_object* v_declName_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(v_declName_30_, v___y_31_);
lean_dec(v___y_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0(lean_object* v_declName_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_ranges_39_; lean_object* v___x_45_; lean_object* v_env_46_; lean_object* v___x_47_; lean_object* v_a_48_; uint8_t v___x_53_; 
v___x_45_ = lean_st_ref_get(v___y_36_);
v_env_46_ = lean_ctor_get(v___x_45_, 0);
lean_inc_ref_n(v_env_46_, 2);
lean_dec(v___x_45_);
lean_inc_n(v_declName_34_, 2);
v___x_47_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(v_declName_34_, v___y_36_);
v_a_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_a_48_);
lean_dec_ref(v___x_47_);
v___x_53_ = l_Lean_isAuxRecursor(v_env_46_, v_declName_34_);
if (v___x_53_ == 0)
{
uint8_t v___x_54_; 
lean_inc(v_declName_34_);
v___x_54_ = l_Lean_isNoConfusion(v_env_46_, v_declName_34_);
if (v___x_54_ == 0)
{
uint8_t v___x_55_; 
v___x_55_ = lean_unbox(v_a_48_);
lean_dec(v_a_48_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v_a_57_; 
lean_inc(v_declName_34_);
v___x_56_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(v_declName_34_, v___y_36_);
v_a_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_a_57_);
lean_dec_ref(v___x_56_);
v_ranges_39_ = v_a_57_;
goto v___jp_38_;
}
else
{
goto v___jp_49_;
}
}
else
{
lean_dec(v_a_48_);
goto v___jp_49_;
}
}
else
{
lean_dec(v_a_48_);
lean_dec_ref(v_env_46_);
goto v___jp_49_;
}
v___jp_38_:
{
if (lean_obj_tag(v_ranges_39_) == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = l_Lean_builtinDeclRanges;
v___x_41_ = lean_st_ref_get(v___x_40_);
v___x_42_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_41_, v_declName_34_);
lean_dec(v_declName_34_);
lean_dec(v___x_41_);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
else
{
lean_object* v___x_44_; 
lean_dec(v_declName_34_);
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v_ranges_39_);
return v___x_44_;
}
}
v___jp_49_:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v_a_52_; 
v___x_50_ = l_Lean_Name_getPrefix(v_declName_34_);
v___x_51_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(v___x_50_, v___y_36_);
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_52_);
lean_dec_ref(v___x_51_);
v_ranges_39_ = v_a_52_;
goto v___jp_38_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0___boxed(lean_object* v_declName_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0(v_declName_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
return v_res_62_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__3(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_box(0);
v___x_69_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__2));
v___x_70_ = l_Lean_mkConst(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__7(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_box(0);
v___x_78_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__6));
v___x_79_ = l_Lean_mkConst(v___x_78_, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__10(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_box(0);
v___x_86_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__9));
v___x_87_ = l_Lean_mkConst(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__13(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_box(0);
v___x_94_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__12));
v___x_95_ = l_Lean_mkConst(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__20(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_box(0);
v___x_107_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__19));
v___x_108_ = l_Lean_mkConst(v___x_107_, v___x_106_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_declareBuiltinDocStringAndRanges(lean_object* v_declName_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___y_114_; lean_object* v___y_115_; lean_object* v___x_205_; lean_object* v_env_206_; lean_object* v_ref_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_205_ = lean_st_ref_get(v_a_111_);
v_env_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc_ref(v_env_206_);
lean_dec(v___x_205_);
v_ref_207_ = lean_ctor_get(v_a_110_, 2);
v___x_208_ = 0;
v___x_209_ = l_Lean_Options_empty;
v___x_210_ = lean_box(0);
v___x_211_ = lean_box(0);
v___x_212_ = lean_box(0);
lean_inc(v_declName_109_);
v___x_213_ = l_Lean_findSimpleDocString_x3f(v_env_206_, v_declName_109_, v___x_208_, v___x_209_, v___x_210_, v___x_211_, v___x_212_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_213_, 1);
if (lean_obj_tag(v_a_214_) == 1)
{
lean_object* v_val_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_val_215_ = lean_ctor_get(v_a_214_, 0);
lean_inc(v_val_215_);
lean_dec_ref_known(v_a_214_, 1);
v___x_216_ = l_String_removeLeadingSpaces(v_val_215_);
v___x_217_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__17));
lean_inc_n(v_declName_109_, 2);
v___x_218_ = l_Lean_Name_append(v_declName_109_, v___x_217_);
v___x_219_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__20, &l_Lean_declareBuiltinDocStringAndRanges___closed__20_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__20);
v___x_220_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_109_);
v___x_221_ = l_Lean_mkStrLit(v___x_216_);
v___x_222_ = lean_unsigned_to_nat(2u);
v___x_223_ = lean_mk_empty_array_with_capacity(v___x_222_);
v___x_224_ = lean_array_push(v___x_223_, v___x_220_);
v___x_225_ = lean_array_push(v___x_224_, v___x_221_);
v___x_226_ = l_Lean_mkAppN(v___x_219_, v___x_225_);
lean_dec_ref(v___x_225_);
v___x_227_ = l_Lean_declareBuiltin(v___x_218_, v___x_226_, v_a_110_, v_a_111_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_dec_ref_known(v___x_227_, 1);
v___y_114_ = v_a_110_;
v___y_115_ = v_a_111_;
goto v___jp_113_;
}
else
{
lean_dec(v_declName_109_);
return v___x_227_;
}
}
else
{
lean_dec(v_a_214_);
v___y_114_ = v_a_110_;
v___y_115_ = v_a_111_;
goto v___jp_113_;
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_239_; 
lean_dec(v_declName_109_);
v_a_228_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_239_ == 0)
{
v___x_230_ = v___x_213_;
v_isShared_231_ = v_isSharedCheck_239_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_213_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_239_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_232_ = lean_io_error_to_string(v_a_228_);
v___x_233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
v___x_234_ = l_Lean_MessageData_ofFormat(v___x_233_);
lean_inc(v_ref_207_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_ref_207_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_235_);
v___x_237_ = v___x_230_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
v___jp_113_:
{
lean_object* v___x_116_; 
lean_inc(v_declName_109_);
v___x_116_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0(v_declName_109_, v___y_114_, v___y_115_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_196_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_196_ == 0)
{
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_196_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_196_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
if (lean_obj_tag(v_a_117_) == 1)
{
lean_object* v_val_121_; lean_object* v_range_122_; lean_object* v_selectionRange_123_; lean_object* v___x_124_; lean_object* v_pos_125_; lean_object* v_charUtf16_126_; lean_object* v_endPos_127_; lean_object* v_endCharUtf16_128_; lean_object* v___x_129_; lean_object* v_line_130_; lean_object* v_column_131_; lean_object* v_line_132_; lean_object* v_column_133_; lean_object* v___x_134_; lean_object* v_pos_135_; lean_object* v_charUtf16_136_; lean_object* v_endPos_137_; lean_object* v_endCharUtf16_138_; lean_object* v_line_139_; lean_object* v_column_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v_line_149_; lean_object* v_column_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
lean_del_object(v___x_119_);
v_val_121_ = lean_ctor_get(v_a_117_, 0);
lean_inc(v_val_121_);
lean_dec_ref_known(v_a_117_, 1);
v_range_122_ = lean_ctor_get(v_val_121_, 0);
lean_inc_ref(v_range_122_);
v_selectionRange_123_ = lean_ctor_get(v_val_121_, 1);
lean_inc_ref(v_selectionRange_123_);
lean_dec(v_val_121_);
v___x_124_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__3, &l_Lean_declareBuiltinDocStringAndRanges___closed__3_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__3);
v_pos_125_ = lean_ctor_get(v_range_122_, 0);
lean_inc_ref(v_pos_125_);
v_charUtf16_126_ = lean_ctor_get(v_range_122_, 1);
lean_inc(v_charUtf16_126_);
v_endPos_127_ = lean_ctor_get(v_range_122_, 2);
lean_inc_ref(v_endPos_127_);
v_endCharUtf16_128_ = lean_ctor_get(v_range_122_, 3);
lean_inc(v_endCharUtf16_128_);
lean_dec_ref(v_range_122_);
v___x_129_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__7, &l_Lean_declareBuiltinDocStringAndRanges___closed__7_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__7);
v_line_130_ = lean_ctor_get(v_pos_125_, 0);
lean_inc(v_line_130_);
v_column_131_ = lean_ctor_get(v_pos_125_, 1);
lean_inc(v_column_131_);
lean_dec_ref(v_pos_125_);
v_line_132_ = lean_ctor_get(v_endPos_127_, 0);
lean_inc(v_line_132_);
v_column_133_ = lean_ctor_get(v_endPos_127_, 1);
lean_inc(v_column_133_);
lean_dec_ref(v_endPos_127_);
v___x_134_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__10, &l_Lean_declareBuiltinDocStringAndRanges___closed__10_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__10);
v_pos_135_ = lean_ctor_get(v_selectionRange_123_, 0);
lean_inc_ref(v_pos_135_);
v_charUtf16_136_ = lean_ctor_get(v_selectionRange_123_, 1);
lean_inc(v_charUtf16_136_);
v_endPos_137_ = lean_ctor_get(v_selectionRange_123_, 2);
lean_inc_ref(v_endPos_137_);
v_endCharUtf16_138_ = lean_ctor_get(v_selectionRange_123_, 3);
lean_inc(v_endCharUtf16_138_);
lean_dec_ref(v_selectionRange_123_);
v_line_139_ = lean_ctor_get(v_pos_135_, 0);
lean_inc(v_line_139_);
v_column_140_ = lean_ctor_get(v_pos_135_, 1);
lean_inc(v_column_140_);
lean_dec_ref(v_pos_135_);
v___x_141_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__13, &l_Lean_declareBuiltinDocStringAndRanges___closed__13_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__13);
v___x_142_ = l_Lean_mkNatLit(v_line_130_);
v___x_143_ = l_Lean_mkNatLit(v_column_131_);
v___x_144_ = lean_unsigned_to_nat(2u);
v___x_145_ = lean_mk_empty_array_with_capacity(v___x_144_);
lean_inc_ref_n(v___x_145_, 5);
v___x_146_ = lean_array_push(v___x_145_, v___x_142_);
v___x_147_ = lean_array_push(v___x_146_, v___x_143_);
v___x_148_ = l_Lean_mkAppN(v___x_141_, v___x_147_);
lean_dec_ref(v___x_147_);
v_line_149_ = lean_ctor_get(v_endPos_137_, 0);
lean_inc(v_line_149_);
v_column_150_ = lean_ctor_get(v_endPos_137_, 1);
lean_inc(v_column_150_);
lean_dec_ref(v_endPos_137_);
v___x_151_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__15));
lean_inc(v_declName_109_);
v___x_152_ = l_Lean_Name_append(v_declName_109_, v___x_151_);
v___x_153_ = l_Lean_mkNatLit(v_line_132_);
v___x_154_ = l_Lean_mkNatLit(v_column_133_);
v___x_155_ = lean_array_push(v___x_145_, v___x_153_);
v___x_156_ = lean_array_push(v___x_155_, v___x_154_);
v___x_157_ = l_Lean_mkAppN(v___x_141_, v___x_156_);
lean_dec_ref(v___x_156_);
v___x_158_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_109_);
v___x_159_ = l_Lean_mkNatLit(v_charUtf16_126_);
v___x_160_ = l_Lean_mkNatLit(v_endCharUtf16_128_);
v___x_161_ = lean_unsigned_to_nat(4u);
v___x_162_ = lean_mk_empty_array_with_capacity(v___x_161_);
lean_inc_ref(v___x_162_);
v___x_163_ = lean_array_push(v___x_162_, v___x_148_);
v___x_164_ = lean_array_push(v___x_163_, v___x_159_);
v___x_165_ = lean_array_push(v___x_164_, v___x_157_);
v___x_166_ = lean_array_push(v___x_165_, v___x_160_);
v___x_167_ = l_Lean_mkAppN(v___x_134_, v___x_166_);
lean_dec_ref(v___x_166_);
v___x_168_ = l_Lean_mkNatLit(v_line_139_);
v___x_169_ = l_Lean_mkNatLit(v_column_140_);
v___x_170_ = lean_array_push(v___x_145_, v___x_168_);
v___x_171_ = lean_array_push(v___x_170_, v___x_169_);
v___x_172_ = l_Lean_mkAppN(v___x_141_, v___x_171_);
lean_dec_ref(v___x_171_);
v___x_173_ = l_Lean_mkNatLit(v_charUtf16_136_);
v___x_174_ = l_Lean_mkNatLit(v_line_149_);
v___x_175_ = l_Lean_mkNatLit(v_column_150_);
v___x_176_ = lean_array_push(v___x_145_, v___x_174_);
v___x_177_ = lean_array_push(v___x_176_, v___x_175_);
v___x_178_ = l_Lean_mkAppN(v___x_141_, v___x_177_);
lean_dec_ref(v___x_177_);
v___x_179_ = l_Lean_mkNatLit(v_endCharUtf16_138_);
v___x_180_ = lean_array_push(v___x_162_, v___x_172_);
v___x_181_ = lean_array_push(v___x_180_, v___x_173_);
v___x_182_ = lean_array_push(v___x_181_, v___x_178_);
v___x_183_ = lean_array_push(v___x_182_, v___x_179_);
v___x_184_ = l_Lean_mkAppN(v___x_134_, v___x_183_);
lean_dec_ref(v___x_183_);
v___x_185_ = lean_array_push(v___x_145_, v___x_167_);
v___x_186_ = lean_array_push(v___x_185_, v___x_184_);
v___x_187_ = l_Lean_mkAppN(v___x_129_, v___x_186_);
lean_dec_ref(v___x_186_);
v___x_188_ = lean_array_push(v___x_145_, v___x_158_);
v___x_189_ = lean_array_push(v___x_188_, v___x_187_);
v___x_190_ = l_Lean_mkAppN(v___x_124_, v___x_189_);
lean_dec_ref(v___x_189_);
v___x_191_ = l_Lean_declareBuiltin(v___x_152_, v___x_190_, v___y_114_, v___y_115_);
return v___x_191_;
}
else
{
lean_object* v___x_192_; lean_object* v___x_194_; 
lean_dec(v_a_117_);
lean_dec(v_declName_109_);
v___x_192_ = lean_box(0);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_192_);
v___x_194_ = v___x_119_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec(v_declName_109_);
v_a_197_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_116_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_116_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_declareBuiltinDocStringAndRanges___boxed(lean_object* v_declName_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_240_, v_a_241_, v_a_242_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0(lean_object* v_declName_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(v_declName_245_, v___y_247_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___boxed(lean_object* v_declName_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0(v_declName_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1(lean_object* v_declName_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(v_declName_255_, v___y_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___boxed(lean_object* v_declName_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1(v_declName_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(lean_object* v_decl_265_, lean_object* v_stx_266_, uint8_t v_x_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_266_, v___y_268_, v___y_269_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v___x_272_; 
lean_dec_ref_known(v___x_271_, 1);
v___x_272_ = l_Lean_declareBuiltinDocStringAndRanges(v_decl_265_, v___y_268_, v___y_269_);
return v___x_272_;
}
else
{
lean_dec(v_decl_265_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object* v_decl_273_, lean_object* v_stx_274_, lean_object* v_x_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
uint8_t v_x_1091__boxed_279_; lean_object* v_res_280_; 
v_x_1091__boxed_279_ = lean_unbox(v_x_275_);
v_res_280_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(v_decl_273_, v_stx_274_, v_x_1091__boxed_279_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
return v_res_280_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_281_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_284_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_285_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
lean_ctor_set(v___x_287_, 2, v___x_286_);
lean_ctor_set(v___x_287_, 3, v___x_286_);
lean_ctor_set(v___x_287_, 4, v___x_285_);
lean_ctor_set(v___x_287_, 5, v___x_285_);
lean_ctor_set(v___x_287_, 6, v___x_285_);
lean_ctor_set(v___x_287_, 7, v___x_285_);
lean_ctor_set(v___x_287_, 8, v___x_285_);
lean_ctor_set(v___x_287_, 9, v___x_285_);
lean_ctor_set(v___x_287_, 10, v___x_285_);
lean_ctor_set(v___x_287_, 11, v___x_284_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_unsigned_to_nat(32u);
v___x_289_ = lean_mk_empty_array_with_capacity(v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_291_ = ((size_t)5ULL);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_unsigned_to_nat(32u);
v___x_294_ = lean_mk_empty_array_with_capacity(v___x_293_);
v___x_295_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_296_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_294_);
lean_ctor_set(v___x_296_, 2, v___x_292_);
lean_ctor_set(v___x_296_, 3, v___x_292_);
lean_ctor_set_usize(v___x_296_, 4, v___x_291_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_297_ = lean_box(1);
v___x_298_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_299_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_298_);
lean_ctor_set(v___x_300_, 2, v___x_297_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; lean_object* v_toCold_306_; lean_object* v_env_307_; lean_object* v_options_308_; uint8_t v___x_309_; lean_object* v_env_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_305_ = lean_st_ref_get(v___y_303_);
v_toCold_306_ = lean_ctor_get(v___y_302_, 0);
v_env_307_ = lean_ctor_get(v___x_305_, 0);
lean_inc_ref(v_env_307_);
lean_dec(v___x_305_);
v_options_308_ = lean_ctor_get(v_toCold_306_, 2);
v___x_309_ = 0;
v_env_310_ = l_Lean_Environment_setRecordingDeps(v_env_307_, v___x_309_);
v___x_311_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_312_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_308_);
v___x_313_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_313_, 0, v_env_310_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
lean_ctor_set(v___x_313_, 2, v___x_312_);
lean_ctor_set(v___x_313_, 3, v_options_308_);
v___x_314_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v_msgData_301_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0(v_msgData_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_ref_325_; lean_object* v___x_326_; lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_335_; 
v_ref_325_ = lean_ctor_get(v___y_322_, 2);
v___x_326_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0(v_msg_321_, v___y_322_, v___y_323_);
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_335_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
lean_inc(v_ref_325_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v_ref_325_);
lean_ctor_set(v___x_331_, 1, v_a_327_);
if (v_isShared_330_ == 0)
{
lean_ctor_set_tag(v___x_329_, 1);
lean_ctor_set(v___x_329_, 0, v___x_331_);
v___x_333_ = v___x_329_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(v_msg_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_340_;
}
}
static lean_object* _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_343_ = l_Lean_stringToMessageData(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_346_ = l_Lean_stringToMessageData(v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(lean_object* v___x_347_, lean_object* v_decl_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_352_ = lean_obj_once(&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_, &l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__once, _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_);
v___x_353_ = l_Lean_MessageData_ofName(v___x_347_);
v___x_354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = lean_obj_once(&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_, &l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__once, _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(v___x_356_, v___y_349_, v___y_350_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object* v___x_358_, lean_object* v_decl_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(v___x_358_, v_decl_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v_decl_359_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__25_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_427_ = l_Lean_registerBuiltinAttribute(v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_430_, lean_object* v_msg_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(v_msg_431_, v___y_432_, v___y_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_436_, lean_object* v_msg_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0(v_00_u03b1_436_, v_msg_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__19_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_445_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_446_ = l_Lean_addBuiltinDocString(v___x_444_, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
return v_res_448_;
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
