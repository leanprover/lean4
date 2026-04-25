// Lean compiler output
// Module: Lean.BuiltinDocAttr
// Imports: public import Lean.Compiler.InitAttr
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
extern lean_object* l_Lean_instInhabitedDeclarationRanges_default;
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
lean_object* l_Lean_findSimpleDocString_x3f(lean_object*, lean_object*, uint8_t);
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
static const lean_string_object l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 291, .m_capacity = 291, .m_length = 290, .m_data = "Makes the documentation and location of a declaration available as a builtin.\n\nThis allows the documentation of core Lean features to be visible without importing the file they\nare defined in. This is only useful during bootstrapping and should not be used outside of\nthe Lean source code.\n"};
static const lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(lean_object* v_declName_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_env_5_; lean_object* v___x_6_; lean_object* v_env_7_; lean_object* v___x_8_; lean_object* v_toEnvExtension_9_; lean_object* v_asyncMode_10_; lean_object* v___x_11_; uint8_t v___x_12_; lean_object* v___x_13_; 
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
v___x_11_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_12_ = 0;
lean_inc(v_declName_1_);
v___x_13_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_11_, v___x_8_, v_env_5_, v_declName_1_, v_asyncMode_10_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = 1;
v___x_15_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_11_, v___x_8_, v_env_7_, v_declName_1_, v_asyncMode_10_, v___x_14_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; 
lean_dec_ref(v_env_7_);
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
lean_object* v_ranges_39_; lean_object* v___x_45_; lean_object* v_env_46_; lean_object* v___x_47_; lean_object* v_a_48_; uint8_t v___y_54_; uint8_t v___x_58_; 
v___x_45_ = lean_st_ref_get(v___y_36_);
v_env_46_ = lean_ctor_get(v___x_45_, 0);
lean_inc_ref_n(v_env_46_, 2);
lean_dec(v___x_45_);
lean_inc_n(v_declName_34_, 2);
v___x_47_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(v_declName_34_, v___y_36_);
v_a_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_a_48_);
lean_dec_ref(v___x_47_);
v___x_58_ = l_Lean_isAuxRecursor(v_env_46_, v_declName_34_);
if (v___x_58_ == 0)
{
uint8_t v___x_59_; 
lean_inc(v_declName_34_);
v___x_59_ = l_Lean_isNoConfusion(v_env_46_, v_declName_34_);
v___y_54_ = v___x_59_;
goto v___jp_53_;
}
else
{
lean_dec_ref(v_env_46_);
v___y_54_ = v___x_58_;
goto v___jp_53_;
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
v___jp_53_:
{
if (v___y_54_ == 0)
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
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0___boxed(lean_object* v_declName_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0(v_declName_60_, v___y_61_, v___y_62_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
return v_res_64_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__3(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_box(0);
v___x_71_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__2));
v___x_72_ = l_Lean_mkConst(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__7(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_box(0);
v___x_80_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__6));
v___x_81_ = l_Lean_mkConst(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__10(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_box(0);
v___x_88_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__9));
v___x_89_ = l_Lean_mkConst(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__13(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_box(0);
v___x_96_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__12));
v___x_97_ = l_Lean_mkConst(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_declareBuiltinDocStringAndRanges___closed__20(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_box(0);
v___x_109_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__19));
v___x_110_ = l_Lean_mkConst(v___x_109_, v___x_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_declareBuiltinDocStringAndRanges(lean_object* v_declName_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___y_116_; lean_object* v___y_117_; lean_object* v___x_207_; lean_object* v_env_208_; uint8_t v___x_209_; lean_object* v___x_210_; 
v___x_207_ = lean_st_ref_get(v_a_113_);
v_env_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc_ref(v_env_208_);
lean_dec(v___x_207_);
v___x_209_ = 0;
lean_inc(v_declName_111_);
v___x_210_ = l_Lean_findSimpleDocString_x3f(v_env_208_, v_declName_111_, v___x_209_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref(v___x_210_);
if (lean_obj_tag(v_a_211_) == 1)
{
lean_object* v_val_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_val_212_ = lean_ctor_get(v_a_211_, 0);
lean_inc(v_val_212_);
lean_dec_ref(v_a_211_);
v___x_213_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__17));
lean_inc_n(v_declName_111_, 2);
v___x_214_ = l_Lean_Name_append(v_declName_111_, v___x_213_);
v___x_215_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__20, &l_Lean_declareBuiltinDocStringAndRanges___closed__20_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__20);
v___x_216_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_111_);
v___x_217_ = l_Lean_mkStrLit(v_val_212_);
v___x_218_ = lean_unsigned_to_nat(2u);
v___x_219_ = lean_mk_empty_array_with_capacity(v___x_218_);
v___x_220_ = lean_array_push(v___x_219_, v___x_216_);
v___x_221_ = lean_array_push(v___x_220_, v___x_217_);
v___x_222_ = l_Lean_mkAppN(v___x_215_, v___x_221_);
lean_dec_ref(v___x_221_);
v___x_223_ = l_Lean_declareBuiltin(v___x_214_, v___x_222_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_dec_ref(v___x_223_);
v___y_116_ = v_a_112_;
v___y_117_ = v_a_113_;
goto v___jp_115_;
}
else
{
lean_dec(v_declName_111_);
return v___x_223_;
}
}
else
{
lean_dec(v_a_211_);
v___y_116_ = v_a_112_;
v___y_117_ = v_a_113_;
goto v___jp_115_;
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_236_; 
lean_dec(v_declName_111_);
v_a_224_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_236_ == 0)
{
v___x_226_ = v___x_210_;
v_isShared_227_ = v_isSharedCheck_236_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_210_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_236_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v_ref_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v_ref_228_ = lean_ctor_get(v_a_112_, 5);
v___x_229_ = lean_io_error_to_string(v_a_224_);
v___x_230_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
v___x_231_ = l_Lean_MessageData_ofFormat(v___x_230_);
lean_inc(v_ref_228_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v_ref_228_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_232_);
v___x_234_ = v___x_226_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
v___jp_115_:
{
lean_object* v___x_118_; 
lean_inc(v_declName_111_);
v___x_118_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0(v_declName_111_, v___y_116_, v___y_117_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_198_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_198_ == 0)
{
v___x_121_ = v___x_118_;
v_isShared_122_ = v_isSharedCheck_198_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_118_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_198_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
if (lean_obj_tag(v_a_119_) == 1)
{
lean_object* v_val_123_; lean_object* v_range_124_; lean_object* v_pos_125_; lean_object* v_endPos_126_; lean_object* v_selectionRange_127_; lean_object* v_pos_128_; lean_object* v_charUtf16_129_; lean_object* v_endCharUtf16_130_; lean_object* v_line_131_; lean_object* v_column_132_; lean_object* v_line_133_; lean_object* v_column_134_; lean_object* v_charUtf16_135_; lean_object* v_endPos_136_; lean_object* v_endCharUtf16_137_; lean_object* v_line_138_; lean_object* v_column_139_; lean_object* v___x_140_; lean_object* v_line_141_; lean_object* v_column_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
lean_del_object(v___x_121_);
v_val_123_ = lean_ctor_get(v_a_119_, 0);
lean_inc(v_val_123_);
lean_dec_ref(v_a_119_);
v_range_124_ = lean_ctor_get(v_val_123_, 0);
lean_inc_ref(v_range_124_);
v_pos_125_ = lean_ctor_get(v_range_124_, 0);
lean_inc_ref(v_pos_125_);
v_endPos_126_ = lean_ctor_get(v_range_124_, 2);
lean_inc_ref(v_endPos_126_);
v_selectionRange_127_ = lean_ctor_get(v_val_123_, 1);
lean_inc_ref(v_selectionRange_127_);
lean_dec(v_val_123_);
v_pos_128_ = lean_ctor_get(v_selectionRange_127_, 0);
lean_inc_ref(v_pos_128_);
v_charUtf16_129_ = lean_ctor_get(v_range_124_, 1);
lean_inc(v_charUtf16_129_);
v_endCharUtf16_130_ = lean_ctor_get(v_range_124_, 3);
lean_inc(v_endCharUtf16_130_);
lean_dec_ref(v_range_124_);
v_line_131_ = lean_ctor_get(v_pos_125_, 0);
lean_inc(v_line_131_);
v_column_132_ = lean_ctor_get(v_pos_125_, 1);
lean_inc(v_column_132_);
lean_dec_ref(v_pos_125_);
v_line_133_ = lean_ctor_get(v_endPos_126_, 0);
lean_inc(v_line_133_);
v_column_134_ = lean_ctor_get(v_endPos_126_, 1);
lean_inc(v_column_134_);
lean_dec_ref(v_endPos_126_);
v_charUtf16_135_ = lean_ctor_get(v_selectionRange_127_, 1);
lean_inc(v_charUtf16_135_);
v_endPos_136_ = lean_ctor_get(v_selectionRange_127_, 2);
lean_inc_ref(v_endPos_136_);
v_endCharUtf16_137_ = lean_ctor_get(v_selectionRange_127_, 3);
lean_inc(v_endCharUtf16_137_);
lean_dec_ref(v_selectionRange_127_);
v_line_138_ = lean_ctor_get(v_pos_128_, 0);
lean_inc(v_line_138_);
v_column_139_ = lean_ctor_get(v_pos_128_, 1);
lean_inc(v_column_139_);
lean_dec_ref(v_pos_128_);
v___x_140_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__3, &l_Lean_declareBuiltinDocStringAndRanges___closed__3_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__3);
v_line_141_ = lean_ctor_get(v_endPos_136_, 0);
lean_inc(v_line_141_);
v_column_142_ = lean_ctor_get(v_endPos_136_, 1);
lean_inc(v_column_142_);
lean_dec_ref(v_endPos_136_);
v___x_143_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__7, &l_Lean_declareBuiltinDocStringAndRanges___closed__7_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__7);
v___x_144_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__10, &l_Lean_declareBuiltinDocStringAndRanges___closed__10_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__10);
v___x_145_ = lean_obj_once(&l_Lean_declareBuiltinDocStringAndRanges___closed__13, &l_Lean_declareBuiltinDocStringAndRanges___closed__13_once, _init_l_Lean_declareBuiltinDocStringAndRanges___closed__13);
v___x_146_ = l_Lean_mkNatLit(v_line_131_);
v___x_147_ = l_Lean_mkNatLit(v_column_132_);
v___x_148_ = lean_unsigned_to_nat(2u);
v___x_149_ = lean_mk_empty_array_with_capacity(v___x_148_);
lean_inc_ref_n(v___x_149_, 5);
v___x_150_ = lean_array_push(v___x_149_, v___x_146_);
v___x_151_ = lean_array_push(v___x_150_, v___x_147_);
v___x_152_ = l_Lean_mkAppN(v___x_145_, v___x_151_);
lean_dec_ref(v___x_151_);
v___x_153_ = ((lean_object*)(l_Lean_declareBuiltinDocStringAndRanges___closed__15));
lean_inc(v_declName_111_);
v___x_154_ = l_Lean_Name_append(v_declName_111_, v___x_153_);
v___x_155_ = l_Lean_mkNatLit(v_line_133_);
v___x_156_ = l_Lean_mkNatLit(v_column_134_);
v___x_157_ = lean_array_push(v___x_149_, v___x_155_);
v___x_158_ = lean_array_push(v___x_157_, v___x_156_);
v___x_159_ = l_Lean_mkAppN(v___x_145_, v___x_158_);
lean_dec_ref(v___x_158_);
v___x_160_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_111_);
v___x_161_ = l_Lean_mkNatLit(v_charUtf16_129_);
v___x_162_ = l_Lean_mkNatLit(v_endCharUtf16_130_);
v___x_163_ = lean_unsigned_to_nat(4u);
v___x_164_ = lean_mk_empty_array_with_capacity(v___x_163_);
lean_inc_ref(v___x_164_);
v___x_165_ = lean_array_push(v___x_164_, v___x_152_);
v___x_166_ = lean_array_push(v___x_165_, v___x_161_);
v___x_167_ = lean_array_push(v___x_166_, v___x_159_);
v___x_168_ = lean_array_push(v___x_167_, v___x_162_);
v___x_169_ = l_Lean_mkAppN(v___x_144_, v___x_168_);
lean_dec_ref(v___x_168_);
v___x_170_ = l_Lean_mkNatLit(v_line_138_);
v___x_171_ = l_Lean_mkNatLit(v_column_139_);
v___x_172_ = lean_array_push(v___x_149_, v___x_170_);
v___x_173_ = lean_array_push(v___x_172_, v___x_171_);
v___x_174_ = l_Lean_mkAppN(v___x_145_, v___x_173_);
lean_dec_ref(v___x_173_);
v___x_175_ = l_Lean_mkNatLit(v_charUtf16_135_);
v___x_176_ = l_Lean_mkNatLit(v_line_141_);
v___x_177_ = l_Lean_mkNatLit(v_column_142_);
v___x_178_ = lean_array_push(v___x_149_, v___x_176_);
v___x_179_ = lean_array_push(v___x_178_, v___x_177_);
v___x_180_ = l_Lean_mkAppN(v___x_145_, v___x_179_);
lean_dec_ref(v___x_179_);
v___x_181_ = l_Lean_mkNatLit(v_endCharUtf16_137_);
v___x_182_ = lean_array_push(v___x_164_, v___x_174_);
v___x_183_ = lean_array_push(v___x_182_, v___x_175_);
v___x_184_ = lean_array_push(v___x_183_, v___x_180_);
v___x_185_ = lean_array_push(v___x_184_, v___x_181_);
v___x_186_ = l_Lean_mkAppN(v___x_144_, v___x_185_);
lean_dec_ref(v___x_185_);
v___x_187_ = lean_array_push(v___x_149_, v___x_169_);
v___x_188_ = lean_array_push(v___x_187_, v___x_186_);
v___x_189_ = l_Lean_mkAppN(v___x_143_, v___x_188_);
lean_dec_ref(v___x_188_);
v___x_190_ = lean_array_push(v___x_149_, v___x_160_);
v___x_191_ = lean_array_push(v___x_190_, v___x_189_);
v___x_192_ = l_Lean_mkAppN(v___x_140_, v___x_191_);
lean_dec_ref(v___x_191_);
v___x_193_ = l_Lean_declareBuiltin(v___x_154_, v___x_192_, v___y_116_, v___y_117_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_196_; 
lean_dec(v_a_119_);
lean_dec(v_declName_111_);
v___x_194_ = lean_box(0);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_194_);
v___x_196_ = v___x_121_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec(v_declName_111_);
v_a_199_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_118_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_118_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_declareBuiltinDocStringAndRanges___boxed(lean_object* v_declName_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_237_, v_a_238_, v_a_239_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0(lean_object* v_declName_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(v_declName_242_, v___y_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___boxed(lean_object* v_declName_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0(v_declName_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1(lean_object* v_declName_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(v_declName_252_, v___y_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___boxed(lean_object* v_declName_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1(v_declName_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(lean_object* v_decl_262_, lean_object* v_stx_263_, uint8_t v_x_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_263_, v___y_265_, v___y_266_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v___x_269_; 
lean_dec_ref(v___x_268_);
v___x_269_ = l_Lean_declareBuiltinDocStringAndRanges(v_decl_262_, v___y_265_, v___y_266_);
return v___x_269_;
}
else
{
lean_dec(v_decl_262_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object* v_decl_270_, lean_object* v_stx_271_, lean_object* v_x_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
uint8_t v_x_1051__boxed_276_; lean_object* v_res_277_; 
v_x_1051__boxed_276_ = lean_unbox(v_x_272_);
v_res_277_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(v_decl_270_, v_stx_271_, v_x_1051__boxed_276_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_277_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_278_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
lean_ctor_set(v___x_283_, 2, v___x_282_);
lean_ctor_set(v___x_283_, 3, v___x_282_);
lean_ctor_set(v___x_283_, 4, v___x_281_);
lean_ctor_set(v___x_283_, 5, v___x_281_);
lean_ctor_set(v___x_283_, 6, v___x_281_);
lean_ctor_set(v___x_283_, 7, v___x_281_);
lean_ctor_set(v___x_283_, 8, v___x_281_);
lean_ctor_set(v___x_283_, 9, v___x_281_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_unsigned_to_nat(32u);
v___x_285_ = lean_mk_empty_array_with_capacity(v___x_284_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_287_ = ((size_t)5ULL);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_unsigned_to_nat(32u);
v___x_290_ = lean_mk_empty_array_with_capacity(v___x_289_);
v___x_291_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_292_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_290_);
lean_ctor_set(v___x_292_, 2, v___x_288_);
lean_ctor_set(v___x_292_, 3, v___x_288_);
lean_ctor_set_usize(v___x_292_, 4, v___x_287_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_293_ = lean_box(1);
v___x_294_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_295_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_294_);
lean_ctor_set(v___x_296_, 2, v___x_293_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; lean_object* v_env_302_; lean_object* v_options_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_301_ = lean_st_ref_get(v___y_299_);
v_env_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc_ref(v_env_302_);
lean_dec(v___x_301_);
v_options_303_ = lean_ctor_get(v___y_298_, 2);
v___x_304_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_305_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_303_);
v___x_306_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_306_, 0, v_env_302_);
lean_ctor_set(v___x_306_, 1, v___x_304_);
lean_ctor_set(v___x_306_, 2, v___x_305_);
lean_ctor_set(v___x_306_, 3, v_options_303_);
v___x_307_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v_msgData_297_);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0(v_msgData_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_ref_318_; lean_object* v___x_319_; lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_328_; 
v_ref_318_ = lean_ctor_get(v___y_315_, 5);
v___x_319_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0(v_msg_314_, v___y_315_, v___y_316_);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_328_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_326_; 
lean_inc(v_ref_318_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v_ref_318_);
lean_ctor_set(v___x_324_, 1, v_a_320_);
if (v_isShared_323_ == 0)
{
lean_ctor_set_tag(v___x_322_, 1);
lean_ctor_set(v___x_322_, 0, v___x_324_);
v___x_326_ = v___x_322_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(v_msg_329_, v___y_330_, v___y_331_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
return v_res_333_;
}
}
static lean_object* _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_336_ = l_Lean_stringToMessageData(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_339_ = l_Lean_stringToMessageData(v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(lean_object* v___x_340_, lean_object* v_decl_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_345_ = lean_obj_once(&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_, &l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__once, _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_);
v___x_346_ = l_Lean_MessageData_ofName(v___x_340_);
v___x_347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_345_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_obj_once(&l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_, &l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__once, _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_);
v___x_349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(v___x_349_, v___y_342_, v___y_343_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object* v___x_351_, lean_object* v_decl_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(v___x_351_, v_decl_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v_decl_352_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__25_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_420_ = l_Lean_registerBuiltinAttribute(v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_423_, lean_object* v_msg_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(v_msg_424_, v___y_425_, v___y_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_429_, lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0(v_00_u03b1_429_, v_msg_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__19_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_438_ = ((lean_object*)(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_));
v___x_439_ = l_Lean_addBuiltinDocString(v___x_437_, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
return v_res_441_;
}
}
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_BuiltinDocAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
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
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_BuiltinDocAttr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_InitAttr(builtin);
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
