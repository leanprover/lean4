// Lean compiler output
// Module: Lean.Elab.DocString.Builtin.Scopes
// Imports: public import Lean.Elab.DocString public import Lean.Elab.DocString.Builtin.Parsing
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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadLogCoreM;
lean_object* l_Lean_instMonadLogOfMonadLift___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadEnvMetaM;
lean_object* l_Lean_instMonadEnvOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_local_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_local_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_import_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_import_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__0 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__1 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__1_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__1_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__3 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__3_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__4 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__3_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__4_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__5 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__5_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "DocString"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__6 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__5_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__6_value),LEAN_SCALAR_PTR_LITERAL(119, 232, 180, 69, 21, 196, 130, 34)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__7 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__7_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Builtin"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__8 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__7_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__8_value),LEAN_SCALAR_PTR_LITERAL(155, 234, 185, 91, 95, 3, 186, 9)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__9 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__9_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Scopes"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__10 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__9_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__10_value),LEAN_SCALAR_PTR_LITERAL(35, 24, 214, 11, 236, 113, 109, 63)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__11 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(238, 84, 52, 215, 218, 102, 236, 53)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__12 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__12_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2_value),LEAN_SCALAR_PTR_LITERAL(23, 105, 158, 181, 88, 85, 92, 100)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__13 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__13_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__14 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__13_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__14_value),LEAN_SCALAR_PTR_LITERAL(211, 73, 171, 246, 62, 78, 89, 194)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__15 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__15_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "imports"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__15_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16_value),LEAN_SCALAR_PTR_LITERAL(83, 97, 211, 41, 123, 200, 73, 131)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17_value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19_value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM;
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9_value;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__14;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__15;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__17;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__18;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__20;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__21;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__23;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__24;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25;
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__26 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__26_value;
static const lean_ctor_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(120, 104, 189, 185, 38, 81, 44, 71)}};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27_value;
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "Unexpected identifier, expected `local` or a string of imports"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__28 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__28_value;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29;
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unexpected number `"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__30 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__30_value;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31;
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__32 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__32_value;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instFromDocArgDocScope___private__1___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__34 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__34_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35_value)} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__36 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__36_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__36_value)} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37_value)} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__38 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__38_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__38_value)} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_whitespace, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instFromDocArgDocScope___private__1___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__34_value)} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__41 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__41_value;
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Expected comma-separated imports list, got `"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__42 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__42_value;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_getId___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__45 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__45_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__46 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__46_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__47 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__47_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__48 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__48_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__49 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__49_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__50 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__50_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__51 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__51_value;
static const lean_ctor_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__45_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__46_value)}};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__52 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__52_value;
static const lean_ctor_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__52_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__47_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__48_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__49_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__50_value)}};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__53 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__53_value;
static const lean_ctor_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__53_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__51_value)}};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__54 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__54_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instFromDocArgDocScope___lam__2___boxed, .m_arity = 10, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__34_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44_value)} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___closed__0 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instFromDocArgDocScope = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Doc_DocScope_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
return v_k_7_;
}
else
{
lean_object* v_mods_8_; lean_object* v___x_9_; 
v_mods_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_mods_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_mods_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Doc_DocScope_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_local_elim___redArg(lean_object* v_t_22_, lean_object* v_local_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_22_, v_local_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_local_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_local_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_26_, v_local_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_import_elim___redArg(lean_object* v_t_30_, lean_object* v_import_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_30_, v_import_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DocScope_import_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_import_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_34_, v_import_36_);
return v___x_37_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18(void){
_start:
{
uint8_t v___x_76_; uint8_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_76_ = 0;
v___x_77_ = 1;
v___x_78_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
v___x_79_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16));
v___x_80_ = l_Lean_Parser_mkAntiquot(v___x_79_, v___x_78_, v___x_77_, v___x_76_);
return v___x_80_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19));
v___x_83_ = l_Lean_Parser_symbol(v___x_82_);
return v___x_83_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21(void){
_start:
{
uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_84_ = 0;
v___x_85_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20, &l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20_once, _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20);
v___x_86_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19));
v___x_87_ = l_Lean_Parser_ident;
v___x_88_ = l_Lean_Parser_sepBy1(v___x_87_, v___x_86_, v___x_85_, v___x_84_);
return v___x_88_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21, &l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21_once, _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21);
v___x_90_ = lean_unsigned_to_nat(1024u);
v___x_91_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
v___x_92_ = l_Lean_Parser_leadingNode(v___x_91_, v___x_90_, v___x_89_);
return v___x_92_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22, &l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22_once, _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22);
v___x_94_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18, &l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18_once, _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18);
v___x_95_ = l_Lean_Parser_withAntiquot(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23, &l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23_once, _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23);
v___x_97_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
v___x_98_ = l_Lean_Parser_withCache(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24, &l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24_once, _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24);
return v___x_99_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM(void){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports;
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___lam__0(lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_103_; lean_object* v_fn_104_; lean_object* v___x_105_; 
v___x_103_ = l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports;
v_fn_104_ = lean_ctor_get(v___x_103_, 1);
lean_inc_ref(v_fn_104_);
v___x_105_ = lean_apply_2(v_fn_104_, v___y_101_, v___y_102_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___lam__1(lean_object* v___x_106_, lean_object* v___f_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Parser_andthenFn(v___x_106_, v___f_107_, v___y_108_, v___y_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_instMonadEIO(lean_box(0));
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0);
v___x_113_ = l_StateRefT_x27_instMonad___redArg(v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = l_Lean_Core_instMonadLogCoreM;
v___x_123_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9));
v___x_124_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_123_, v___x_122_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11(void){
_start:
{
lean_object* v___x_125_; lean_object* v___f_126_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10);
v___f_126_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8));
v___x_127_ = l_Lean_instMonadLogOfMonadLift___redArg(v___f_126_, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11);
v___x_129_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9));
v___x_130_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_129_, v___x_128_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13(void){
_start:
{
lean_object* v___x_131_; lean_object* v___f_132_; lean_object* v___x_133_; 
v___x_131_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12);
v___f_132_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8));
v___x_133_ = l_Lean_instMonadLogOfMonadLift___redArg(v___f_132_, v___x_131_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__14(void){
_start:
{
lean_object* v___x_134_; lean_object* v___f_135_; 
v___x_134_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_135_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_135_, 0, v___x_134_);
return v___f_135_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__15(void){
_start:
{
lean_object* v___x_136_; lean_object* v___f_137_; 
v___x_136_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_137_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_137_, 0, v___x_136_);
return v___f_137_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16(void){
_start:
{
lean_object* v___f_138_; lean_object* v___f_139_; lean_object* v___x_140_; 
v___f_138_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__15, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__15_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__15);
v___f_139_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__14, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__14_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__14);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v___f_139_);
lean_ctor_set(v___x_140_, 1, v___f_138_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__17(void){
_start:
{
lean_object* v___x_141_; lean_object* v___f_142_; 
v___x_141_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16);
v___f_142_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_142_, 0, v___x_141_);
return v___f_142_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__18(void){
_start:
{
lean_object* v___x_143_; lean_object* v___f_144_; 
v___x_143_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16);
v___f_144_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_144_, 0, v___x_143_);
return v___f_144_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19(void){
_start:
{
lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___x_147_; 
v___f_145_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__18, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__18_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__18);
v___f_146_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__17, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__17_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__17);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___f_146_);
lean_ctor_set(v___x_147_, 1, v___f_145_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__20(void){
_start:
{
lean_object* v___x_148_; lean_object* v___f_149_; 
v___x_148_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19);
v___f_149_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_149_, 0, v___x_148_);
return v___f_149_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__21(void){
_start:
{
lean_object* v___x_150_; lean_object* v___f_151_; 
v___x_150_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19);
v___f_151_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_151_, 0, v___x_150_);
return v___f_151_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22(void){
_start:
{
lean_object* v___f_152_; lean_object* v___f_153_; lean_object* v___x_154_; 
v___f_152_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__21, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__21_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__21);
v___f_153_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__20, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__20_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__20);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___f_153_);
lean_ctor_set(v___x_154_, 1, v___f_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__23(void){
_start:
{
lean_object* v___x_155_; lean_object* v___f_156_; 
v___x_155_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22);
v___f_156_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_156_, 0, v___x_155_);
return v___f_156_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__24(void){
_start:
{
lean_object* v___x_157_; lean_object* v___f_158_; 
v___x_157_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22);
v___f_158_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_158_, 0, v___x_157_);
return v___f_158_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25(void){
_start:
{
lean_object* v___f_159_; lean_object* v___f_160_; lean_object* v___x_161_; 
v___f_159_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__24, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__24_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__24);
v___f_160_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__23, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__23_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__23);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___f_160_);
lean_ctor_set(v___x_161_, 1, v___f_159_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__28));
v___x_167_ = l_Lean_stringToMessageData(v___x_166_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__30));
v___x_170_ = l_Lean_stringToMessageData(v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__32));
v___x_173_ = l_Lean_stringToMessageData(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__42));
v___x_190_ = l_Lean_stringToMessageData(v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1(lean_object* v_v_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_219_; lean_object* v_toApplicative_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_427_; 
v___x_219_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1);
v_toApplicative_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; 
v_unused_428_ = lean_ctor_get(v___x_219_, 1);
lean_dec(v_unused_428_);
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_427_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_toApplicative_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_427_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v_toFunctor_224_; lean_object* v_toSeq_225_; lean_object* v_toSeqLeft_226_; lean_object* v_toSeqRight_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_425_; 
v_toFunctor_224_ = lean_ctor_get(v_toApplicative_220_, 0);
v_toSeq_225_ = lean_ctor_get(v_toApplicative_220_, 2);
v_toSeqLeft_226_ = lean_ctor_get(v_toApplicative_220_, 3);
v_toSeqRight_227_ = lean_ctor_get(v_toApplicative_220_, 4);
v_isSharedCheck_425_ = !lean_is_exclusive(v_toApplicative_220_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v_toApplicative_220_, 1);
lean_dec(v_unused_426_);
v___x_229_ = v_toApplicative_220_;
v_isShared_230_ = v_isSharedCheck_425_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_toSeqRight_227_);
lean_inc(v_toSeqLeft_226_);
lean_inc(v_toSeq_225_);
lean_inc(v_toFunctor_224_);
lean_dec(v_toApplicative_220_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_425_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___f_233_; lean_object* v___f_234_; lean_object* v___x_235_; lean_object* v___f_236_; lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___x_240_; 
v___f_231_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2));
v___f_232_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3));
lean_inc_ref(v_toFunctor_224_);
v___f_233_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_233_, 0, v_toFunctor_224_);
v___f_234_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_234_, 0, v_toFunctor_224_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___f_233_);
lean_ctor_set(v___x_235_, 1, v___f_234_);
v___f_236_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_236_, 0, v_toSeqRight_227_);
v___f_237_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_237_, 0, v_toSeqLeft_226_);
v___f_238_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_238_, 0, v_toSeq_225_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 4, v___f_236_);
lean_ctor_set(v___x_229_, 3, v___f_237_);
lean_ctor_set(v___x_229_, 2, v___f_238_);
lean_ctor_set(v___x_229_, 1, v___f_231_);
lean_ctor_set(v___x_229_, 0, v___x_235_);
v___x_240_ = v___x_229_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___f_231_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v___f_238_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v___f_237_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v___f_236_);
v___x_240_ = v_reuseFailAlloc_424_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_242_; 
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 1, v___f_232_);
lean_ctor_set(v___x_222_, 0, v___x_240_);
v___x_242_ = v___x_222_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___f_232_);
v___x_242_ = v_reuseFailAlloc_423_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; lean_object* v_toApplicative_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_421_; 
v___x_243_ = l_StateRefT_x27_instMonad___redArg(v___x_242_);
v_toApplicative_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_243_, 1);
lean_dec(v_unused_422_);
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_421_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_toApplicative_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_421_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_toFunctor_248_; lean_object* v_toSeq_249_; lean_object* v_toSeqLeft_250_; lean_object* v_toSeqRight_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_419_; 
v_toFunctor_248_ = lean_ctor_get(v_toApplicative_244_, 0);
v_toSeq_249_ = lean_ctor_get(v_toApplicative_244_, 2);
v_toSeqLeft_250_ = lean_ctor_get(v_toApplicative_244_, 3);
v_toSeqRight_251_ = lean_ctor_get(v_toApplicative_244_, 4);
v_isSharedCheck_419_ = !lean_is_exclusive(v_toApplicative_244_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v_toApplicative_244_, 1);
lean_dec(v_unused_420_);
v___x_253_ = v_toApplicative_244_;
v_isShared_254_ = v_isSharedCheck_419_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_toSeqRight_251_);
lean_inc(v_toSeqLeft_250_);
lean_inc(v_toSeq_249_);
lean_inc(v_toFunctor_248_);
lean_dec(v_toApplicative_244_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_419_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___f_255_; lean_object* v___f_256_; lean_object* v___f_257_; lean_object* v___f_258_; lean_object* v___x_259_; lean_object* v___f_260_; lean_object* v___f_261_; lean_object* v___f_262_; lean_object* v___x_264_; 
v___f_255_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4));
v___f_256_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5));
lean_inc_ref(v_toFunctor_248_);
v___f_257_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_257_, 0, v_toFunctor_248_);
v___f_258_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_258_, 0, v_toFunctor_248_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___f_257_);
lean_ctor_set(v___x_259_, 1, v___f_258_);
v___f_260_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_260_, 0, v_toSeqRight_251_);
v___f_261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_261_, 0, v_toSeqLeft_250_);
v___f_262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_262_, 0, v_toSeq_249_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 4, v___f_260_);
lean_ctor_set(v___x_253_, 3, v___f_261_);
lean_ctor_set(v___x_253_, 2, v___f_262_);
lean_ctor_set(v___x_253_, 1, v___f_255_);
lean_ctor_set(v___x_253_, 0, v___x_259_);
v___x_264_ = v___x_253_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___f_255_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v___f_262_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v___f_261_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v___f_260_);
v___x_264_ = v_reuseFailAlloc_418_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_266_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v___f_256_);
lean_ctor_set(v___x_246_, 0, v___x_264_);
v___x_266_ = v___x_246_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v___f_256_);
v___x_266_ = v_reuseFailAlloc_417_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v_toApplicative_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_415_; 
v___x_267_ = l_StateRefT_x27_instMonad___redArg(v___x_266_);
v_toApplicative_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v___x_267_, 1);
lean_dec(v_unused_416_);
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_415_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_toApplicative_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_415_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v_toFunctor_272_; lean_object* v_toSeq_273_; lean_object* v_toSeqLeft_274_; lean_object* v_toSeqRight_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_413_; 
v_toFunctor_272_ = lean_ctor_get(v_toApplicative_268_, 0);
v_toSeq_273_ = lean_ctor_get(v_toApplicative_268_, 2);
v_toSeqLeft_274_ = lean_ctor_get(v_toApplicative_268_, 3);
v_toSeqRight_275_ = lean_ctor_get(v_toApplicative_268_, 4);
v_isSharedCheck_413_ = !lean_is_exclusive(v_toApplicative_268_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v_toApplicative_268_, 1);
lean_dec(v_unused_414_);
v___x_277_ = v_toApplicative_268_;
v_isShared_278_ = v_isSharedCheck_413_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_toSeqRight_275_);
lean_inc(v_toSeqLeft_274_);
lean_inc(v_toSeq_273_);
lean_inc(v_toFunctor_272_);
lean_dec(v_toApplicative_268_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_413_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___f_281_; lean_object* v___f_282_; lean_object* v___x_283_; lean_object* v___f_284_; lean_object* v___f_285_; lean_object* v___f_286_; lean_object* v___x_288_; 
v___f_279_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6));
v___f_280_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7));
lean_inc_ref(v_toFunctor_272_);
v___f_281_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_281_, 0, v_toFunctor_272_);
v___f_282_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_282_, 0, v_toFunctor_272_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___f_281_);
lean_ctor_set(v___x_283_, 1, v___f_282_);
v___f_284_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_284_, 0, v_toSeqRight_275_);
v___f_285_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_285_, 0, v_toSeqLeft_274_);
v___f_286_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_286_, 0, v_toSeq_273_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 4, v___f_284_);
lean_ctor_set(v___x_277_, 3, v___f_285_);
lean_ctor_set(v___x_277_, 2, v___f_286_);
lean_ctor_set(v___x_277_, 1, v___f_279_);
lean_ctor_set(v___x_277_, 0, v___x_283_);
v___x_288_ = v___x_277_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___f_279_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v___f_286_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v___f_285_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v___f_284_);
v___x_288_ = v_reuseFailAlloc_412_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_290_; 
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 1, v___f_280_);
lean_ctor_set(v___x_270_, 0, v___x_288_);
v___x_290_ = v___x_270_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___f_280_);
v___x_290_ = v_reuseFailAlloc_411_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; lean_object* v_toMonadQuotation_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_408_; 
v___x_291_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
v_toMonadQuotation_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; lean_object* v_unused_410_; 
v_unused_409_ = lean_ctor_get(v___x_291_, 2);
lean_dec(v_unused_409_);
v_unused_410_ = lean_ctor_get(v___x_291_, 1);
lean_dec(v_unused_410_);
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_408_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_toMonadQuotation_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_408_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v_toMonadRef_296_; lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_toMonadFileMap_300_; lean_object* v___x_301_; lean_object* v_getEnv_302_; lean_object* v_modifyEnv_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_407_; 
v_toMonadRef_296_ = lean_ctor_get(v_toMonadQuotation_292_, 0);
lean_inc_ref(v_toMonadRef_296_);
lean_dec_ref(v_toMonadQuotation_292_);
v___f_297_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8));
v___x_298_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9));
v___x_299_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13);
v_toMonadFileMap_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_toMonadFileMap_300_);
v___x_301_ = l_Lean_Meta_instMonadEnvMetaM;
v_getEnv_302_ = lean_ctor_get(v___x_301_, 0);
v_modifyEnv_303_ = lean_ctor_get(v___x_301_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_407_ == 0)
{
v___x_305_ = v___x_301_;
v_isShared_306_ = v_isSharedCheck_407_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_modifyEnv_303_);
lean_inc(v_getEnv_302_);
lean_dec(v___x_301_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_407_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___f_307_; lean_object* v___x_308_; lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
v___f_307_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_307_, 0, v_modifyEnv_303_);
lean_closure_set(v___f_307_, 1, v___x_298_);
v___x_308_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_308_, 0, lean_box(0));
lean_closure_set(v___x_308_, 1, lean_box(0));
lean_closure_set(v___x_308_, 2, lean_box(0));
lean_closure_set(v___x_308_, 3, lean_box(0));
lean_closure_set(v___x_308_, 4, v_getEnv_302_);
v___f_309_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_309_, 0, v___f_307_);
lean_closure_set(v___f_309_, 1, v___f_297_);
v___x_310_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_310_, 0, lean_box(0));
lean_closure_set(v___x_310_, 1, v___x_308_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v___f_309_);
lean_ctor_set(v___x_305_, 0, v___x_310_);
v___x_312_ = v___x_305_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___f_309_);
v___x_312_ = v_reuseFailAlloc_406_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_313_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25);
v___x_314_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 2, v___x_314_);
lean_ctor_set(v___x_294_, 1, v_toMonadRef_296_);
lean_ctor_set(v___x_294_, 0, v___x_313_);
v___x_316_ = v___x_294_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_toMonadRef_296_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v___x_314_);
v___x_316_ = v_reuseFailAlloc_405_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
switch(lean_obj_tag(v_v_211_))
{
case 0:
{
lean_object* v_val_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v___x_312_);
lean_dec(v_toMonadFileMap_300_);
v_val_317_ = lean_ctor_get(v_v_211_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v_v_211_);
if (v_isSharedCheck_332_ == 0)
{
v___x_319_ = v_v_211_;
v_isShared_320_ = v_isSharedCheck_332_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_val_317_);
lean_dec(v_v_211_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_332_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v_y_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_321_ = l_Lean_TSyntax_getId(v_val_317_);
v_y_322_ = lean_erase_macro_scopes(v___x_321_);
v___x_323_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27));
v___x_324_ = lean_name_eq(v_y_322_, v___x_323_);
lean_dec(v_y_322_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_2155__overap_326_; lean_object* v___x_327_; 
lean_del_object(v___x_319_);
v___x_325_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29);
v___x_2155__overap_326_ = l_Lean_throwErrorAt___redArg(v___x_290_, v___x_316_, v_val_317_, v___x_325_);
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
v___x_327_ = lean_apply_7(v___x_2155__overap_326_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, lean_box(0));
return v___x_327_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_330_; 
lean_dec(v_val_317_);
lean_dec_ref(v___x_316_);
lean_dec_ref(v___x_290_);
v___x_328_ = lean_box(0);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_328_);
v___x_330_ = v___x_319_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
case 1:
{
lean_object* v_val_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_1817__overap_339_; lean_object* v___x_340_; 
lean_dec_ref(v___x_312_);
lean_dec(v_toMonadFileMap_300_);
v_val_333_ = lean_ctor_get(v_v_211_, 0);
lean_inc(v_val_333_);
lean_dec_ref(v_v_211_);
v___x_334_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31);
lean_inc(v_val_333_);
v___x_335_ = l_Lean_MessageData_ofSyntax(v_val_333_);
v___x_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33);
v___x_338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_1817__overap_339_ = l_Lean_throwErrorAt___redArg(v___x_290_, v___x_316_, v_val_333_, v___x_338_);
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
v___x_340_ = lean_apply_7(v___x_1817__overap_339_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, lean_box(0));
return v___x_340_;
}
default: 
{
lean_object* v_val_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_404_; 
v_val_341_ = lean_ctor_get(v_v_211_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v_v_211_);
if (v_isSharedCheck_404_ == 0)
{
v___x_343_ = v_v_211_;
v_isShared_344_ = v_isSharedCheck_404_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_val_341_);
lean_dec(v_v_211_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_404_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v_fileName_345_; lean_object* v_fileMap_346_; lean_object* v_options_347_; lean_object* v_currRecDepth_348_; lean_object* v_maxRecDepth_349_; lean_object* v_ref_350_; lean_object* v_currNamespace_351_; lean_object* v_openDecls_352_; lean_object* v_initHeartbeats_353_; lean_object* v_maxHeartbeats_354_; lean_object* v_quotContext_355_; lean_object* v_currMacroScope_356_; uint8_t v_diag_357_; lean_object* v_cancelTk_x3f_358_; uint8_t v_suppressElabErrors_359_; lean_object* v_inheritedTraceOptions_360_; lean_object* v___x_361_; lean_object* v___f_362_; lean_object* v_ref_363_; lean_object* v___x_364_; lean_object* v___x_2088__overap_365_; lean_object* v___x_366_; 
v_fileName_345_ = lean_ctor_get(v_a_216_, 0);
v_fileMap_346_ = lean_ctor_get(v_a_216_, 1);
v_options_347_ = lean_ctor_get(v_a_216_, 2);
v_currRecDepth_348_ = lean_ctor_get(v_a_216_, 3);
v_maxRecDepth_349_ = lean_ctor_get(v_a_216_, 4);
v_ref_350_ = lean_ctor_get(v_a_216_, 5);
v_currNamespace_351_ = lean_ctor_get(v_a_216_, 6);
v_openDecls_352_ = lean_ctor_get(v_a_216_, 7);
v_initHeartbeats_353_ = lean_ctor_get(v_a_216_, 8);
v_maxHeartbeats_354_ = lean_ctor_get(v_a_216_, 9);
v_quotContext_355_ = lean_ctor_get(v_a_216_, 10);
v_currMacroScope_356_ = lean_ctor_get(v_a_216_, 11);
v_diag_357_ = lean_ctor_get_uint8(v_a_216_, sizeof(void*)*14);
v_cancelTk_x3f_358_ = lean_ctor_get(v_a_216_, 12);
v_suppressElabErrors_359_ = lean_ctor_get_uint8(v_a_216_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_360_ = lean_ctor_get(v_a_216_, 13);
v___x_361_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39));
v___f_362_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__41));
v_ref_363_ = l_Lean_replaceRef(v_val_341_, v_ref_350_);
lean_inc_ref(v_inheritedTraceOptions_360_);
lean_inc(v_cancelTk_x3f_358_);
lean_inc(v_currMacroScope_356_);
lean_inc(v_quotContext_355_);
lean_inc(v_maxHeartbeats_354_);
lean_inc(v_initHeartbeats_353_);
lean_inc(v_openDecls_352_);
lean_inc(v_currNamespace_351_);
lean_inc(v_maxRecDepth_349_);
lean_inc(v_currRecDepth_348_);
lean_inc_ref(v_options_347_);
lean_inc_ref(v_fileMap_346_);
lean_inc_ref(v_fileName_345_);
v___x_364_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_364_, 0, v_fileName_345_);
lean_ctor_set(v___x_364_, 1, v_fileMap_346_);
lean_ctor_set(v___x_364_, 2, v_options_347_);
lean_ctor_set(v___x_364_, 3, v_currRecDepth_348_);
lean_ctor_set(v___x_364_, 4, v_maxRecDepth_349_);
lean_ctor_set(v___x_364_, 5, v_ref_363_);
lean_ctor_set(v___x_364_, 6, v_currNamespace_351_);
lean_ctor_set(v___x_364_, 7, v_openDecls_352_);
lean_ctor_set(v___x_364_, 8, v_initHeartbeats_353_);
lean_ctor_set(v___x_364_, 9, v_maxHeartbeats_354_);
lean_ctor_set(v___x_364_, 10, v_quotContext_355_);
lean_ctor_set(v___x_364_, 11, v_currMacroScope_356_);
lean_ctor_set(v___x_364_, 12, v_cancelTk_x3f_358_);
lean_ctor_set(v___x_364_, 13, v_inheritedTraceOptions_360_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*14, v_diag_357_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*14 + 1, v_suppressElabErrors_359_);
lean_inc_ref(v___x_316_);
lean_inc_ref(v___x_290_);
v___x_2088__overap_365_ = l_Lean_Doc_parseQuotedStrLit___redArg(v___x_290_, v_toMonadFileMap_300_, v___x_312_, v___x_316_, v___x_299_, v___x_361_, v___f_362_, v_val_341_);
lean_inc(v_a_217_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
v___x_366_ = lean_apply_7(v___x_2088__overap_365_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v___x_364_, v_a_217_, lean_box(0));
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_395_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_395_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_395_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_395_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
lean_inc(v_a_367_);
v___x_373_ = l_Lean_Syntax_isOfKind(v_a_367_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_2199__overap_379_; lean_object* v___x_380_; 
lean_del_object(v___x_369_);
lean_del_object(v___x_343_);
v___x_374_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43);
lean_inc(v_a_367_);
v___x_375_ = l_Lean_MessageData_ofSyntax(v_a_367_);
v___x_376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33);
v___x_378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_2199__overap_379_ = l_Lean_throwErrorAt___redArg(v___x_290_, v___x_316_, v_a_367_, v___x_378_);
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
v___x_380_ = lean_apply_7(v___x_2199__overap_379_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, lean_box(0));
return v___x_380_;
}
else
{
lean_object* v___f_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; size_t v_sz_386_; size_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
lean_dec_ref(v___x_316_);
lean_dec_ref(v___x_290_);
v___f_381_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44));
v___x_382_ = l_Lean_Syntax_getArg(v_a_367_, v___x_371_);
lean_dec(v_a_367_);
v___x_383_ = l_Lean_Syntax_getArgs(v___x_382_);
lean_dec(v___x_382_);
v___x_384_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_383_);
lean_dec_ref(v___x_383_);
v___x_385_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__54));
v_sz_386_ = lean_array_size(v___x_384_);
v___x_387_ = ((size_t)0ULL);
v___x_388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_385_, v___f_381_, v_sz_386_, v___x_387_, v___x_384_);
if (v_isShared_344_ == 0)
{
lean_ctor_set_tag(v___x_343_, 1);
lean_ctor_set(v___x_343_, 0, v___x_388_);
v___x_390_ = v___x_343_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_394_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_390_);
v___x_392_ = v___x_369_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_del_object(v___x_343_);
lean_dec_ref(v___x_316_);
lean_dec_ref(v___x_290_);
v_a_396_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_366_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_366_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___boxed(lean_object* v_v_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Doc_instFromDocArgDocScope___private__1(v_v_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___lam__2(lean_object* v___f_438_, lean_object* v___f_439_, lean_object* v_v_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; lean_object* v_toApplicative_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_656_; 
v___x_448_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1);
v_toApplicative_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v___x_448_, 1);
lean_dec(v_unused_657_);
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_656_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_toApplicative_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_656_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v_toFunctor_453_; lean_object* v_toSeq_454_; lean_object* v_toSeqLeft_455_; lean_object* v_toSeqRight_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_654_; 
v_toFunctor_453_ = lean_ctor_get(v_toApplicative_449_, 0);
v_toSeq_454_ = lean_ctor_get(v_toApplicative_449_, 2);
v_toSeqLeft_455_ = lean_ctor_get(v_toApplicative_449_, 3);
v_toSeqRight_456_ = lean_ctor_get(v_toApplicative_449_, 4);
v_isSharedCheck_654_ = !lean_is_exclusive(v_toApplicative_449_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v_toApplicative_449_, 1);
lean_dec(v_unused_655_);
v___x_458_ = v_toApplicative_449_;
v_isShared_459_ = v_isSharedCheck_654_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_toSeqRight_456_);
lean_inc(v_toSeqLeft_455_);
lean_inc(v_toSeq_454_);
lean_inc(v_toFunctor_453_);
lean_dec(v_toApplicative_449_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_654_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___f_460_; lean_object* v___f_461_; lean_object* v___f_462_; lean_object* v___f_463_; lean_object* v___x_464_; lean_object* v___f_465_; lean_object* v___f_466_; lean_object* v___f_467_; lean_object* v___x_469_; 
v___f_460_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2));
v___f_461_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3));
lean_inc_ref(v_toFunctor_453_);
v___f_462_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_462_, 0, v_toFunctor_453_);
v___f_463_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_463_, 0, v_toFunctor_453_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___f_462_);
lean_ctor_set(v___x_464_, 1, v___f_463_);
v___f_465_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_465_, 0, v_toSeqRight_456_);
v___f_466_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_466_, 0, v_toSeqLeft_455_);
v___f_467_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_467_, 0, v_toSeq_454_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v___f_465_);
lean_ctor_set(v___x_458_, 3, v___f_466_);
lean_ctor_set(v___x_458_, 2, v___f_467_);
lean_ctor_set(v___x_458_, 1, v___f_460_);
lean_ctor_set(v___x_458_, 0, v___x_464_);
v___x_469_ = v___x_458_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___f_460_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v___f_467_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v___f_466_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v___f_465_);
v___x_469_ = v_reuseFailAlloc_653_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_471_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___f_461_);
lean_ctor_set(v___x_451_, 0, v___x_469_);
v___x_471_ = v___x_451_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___f_461_);
v___x_471_ = v_reuseFailAlloc_652_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v_toApplicative_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_650_; 
v___x_472_ = l_StateRefT_x27_instMonad___redArg(v___x_471_);
v_toApplicative_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v___x_472_, 1);
lean_dec(v_unused_651_);
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_650_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_toApplicative_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_650_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v_toFunctor_477_; lean_object* v_toSeq_478_; lean_object* v_toSeqLeft_479_; lean_object* v_toSeqRight_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_648_; 
v_toFunctor_477_ = lean_ctor_get(v_toApplicative_473_, 0);
v_toSeq_478_ = lean_ctor_get(v_toApplicative_473_, 2);
v_toSeqLeft_479_ = lean_ctor_get(v_toApplicative_473_, 3);
v_toSeqRight_480_ = lean_ctor_get(v_toApplicative_473_, 4);
v_isSharedCheck_648_ = !lean_is_exclusive(v_toApplicative_473_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; 
v_unused_649_ = lean_ctor_get(v_toApplicative_473_, 1);
lean_dec(v_unused_649_);
v___x_482_ = v_toApplicative_473_;
v_isShared_483_ = v_isSharedCheck_648_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_toSeqRight_480_);
lean_inc(v_toSeqLeft_479_);
lean_inc(v_toSeq_478_);
lean_inc(v_toFunctor_477_);
lean_dec(v_toApplicative_473_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_648_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___f_484_; lean_object* v___f_485_; lean_object* v___f_486_; lean_object* v___f_487_; lean_object* v___x_488_; lean_object* v___f_489_; lean_object* v___f_490_; lean_object* v___f_491_; lean_object* v___x_493_; 
v___f_484_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4));
v___f_485_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5));
lean_inc_ref(v_toFunctor_477_);
v___f_486_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_486_, 0, v_toFunctor_477_);
v___f_487_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_487_, 0, v_toFunctor_477_);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___f_486_);
lean_ctor_set(v___x_488_, 1, v___f_487_);
v___f_489_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_489_, 0, v_toSeqRight_480_);
v___f_490_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_490_, 0, v_toSeqLeft_479_);
v___f_491_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_491_, 0, v_toSeq_478_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 4, v___f_489_);
lean_ctor_set(v___x_482_, 3, v___f_490_);
lean_ctor_set(v___x_482_, 2, v___f_491_);
lean_ctor_set(v___x_482_, 1, v___f_484_);
lean_ctor_set(v___x_482_, 0, v___x_488_);
v___x_493_ = v___x_482_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v___f_484_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v___f_491_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v___f_490_);
lean_ctor_set(v_reuseFailAlloc_647_, 4, v___f_489_);
v___x_493_ = v_reuseFailAlloc_647_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_495_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v___f_485_);
lean_ctor_set(v___x_475_, 0, v___x_493_);
v___x_495_ = v___x_475_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___f_485_);
v___x_495_ = v_reuseFailAlloc_646_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_496_; lean_object* v_toApplicative_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_644_; 
v___x_496_ = l_StateRefT_x27_instMonad___redArg(v___x_495_);
v_toApplicative_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; 
v_unused_645_ = lean_ctor_get(v___x_496_, 1);
lean_dec(v_unused_645_);
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_644_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_toApplicative_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_644_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_toFunctor_501_; lean_object* v_toSeq_502_; lean_object* v_toSeqLeft_503_; lean_object* v_toSeqRight_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_642_; 
v_toFunctor_501_ = lean_ctor_get(v_toApplicative_497_, 0);
v_toSeq_502_ = lean_ctor_get(v_toApplicative_497_, 2);
v_toSeqLeft_503_ = lean_ctor_get(v_toApplicative_497_, 3);
v_toSeqRight_504_ = lean_ctor_get(v_toApplicative_497_, 4);
v_isSharedCheck_642_ = !lean_is_exclusive(v_toApplicative_497_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; 
v_unused_643_ = lean_ctor_get(v_toApplicative_497_, 1);
lean_dec(v_unused_643_);
v___x_506_ = v_toApplicative_497_;
v_isShared_507_ = v_isSharedCheck_642_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_toSeqRight_504_);
lean_inc(v_toSeqLeft_503_);
lean_inc(v_toSeq_502_);
lean_inc(v_toFunctor_501_);
lean_dec(v_toApplicative_497_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_642_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___f_508_; lean_object* v___f_509_; lean_object* v___f_510_; lean_object* v___f_511_; lean_object* v___x_512_; lean_object* v___f_513_; lean_object* v___f_514_; lean_object* v___f_515_; lean_object* v___x_517_; 
v___f_508_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6));
v___f_509_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7));
lean_inc_ref(v_toFunctor_501_);
v___f_510_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_510_, 0, v_toFunctor_501_);
v___f_511_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_511_, 0, v_toFunctor_501_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___f_510_);
lean_ctor_set(v___x_512_, 1, v___f_511_);
v___f_513_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_513_, 0, v_toSeqRight_504_);
v___f_514_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_514_, 0, v_toSeqLeft_503_);
v___f_515_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_515_, 0, v_toSeq_502_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v___f_513_);
lean_ctor_set(v___x_506_, 3, v___f_514_);
lean_ctor_set(v___x_506_, 2, v___f_515_);
lean_ctor_set(v___x_506_, 1, v___f_508_);
lean_ctor_set(v___x_506_, 0, v___x_512_);
v___x_517_ = v___x_506_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___f_508_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v___f_515_);
lean_ctor_set(v_reuseFailAlloc_641_, 3, v___f_514_);
lean_ctor_set(v_reuseFailAlloc_641_, 4, v___f_513_);
v___x_517_ = v_reuseFailAlloc_641_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_519_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 1, v___f_509_);
lean_ctor_set(v___x_499_, 0, v___x_517_);
v___x_519_ = v___x_499_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___f_509_);
v___x_519_ = v_reuseFailAlloc_640_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_520_; lean_object* v_toMonadQuotation_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_637_; 
v___x_520_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
v_toMonadQuotation_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; lean_object* v_unused_639_; 
v_unused_638_ = lean_ctor_get(v___x_520_, 2);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v___x_520_, 1);
lean_dec(v_unused_639_);
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_637_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_toMonadQuotation_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_637_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_toMonadRef_525_; lean_object* v___f_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_toMonadFileMap_529_; lean_object* v___x_530_; lean_object* v_getEnv_531_; lean_object* v_modifyEnv_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_636_; 
v_toMonadRef_525_ = lean_ctor_get(v_toMonadQuotation_521_, 0);
lean_inc_ref(v_toMonadRef_525_);
lean_dec_ref(v_toMonadQuotation_521_);
v___f_526_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8));
v___x_527_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9));
v___x_528_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13);
v_toMonadFileMap_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_toMonadFileMap_529_);
v___x_530_ = l_Lean_Meta_instMonadEnvMetaM;
v_getEnv_531_ = lean_ctor_get(v___x_530_, 0);
v_modifyEnv_532_ = lean_ctor_get(v___x_530_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_636_ == 0)
{
v___x_534_ = v___x_530_;
v_isShared_535_ = v_isSharedCheck_636_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_modifyEnv_532_);
lean_inc(v_getEnv_531_);
lean_dec(v___x_530_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_636_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___f_536_; lean_object* v___x_537_; lean_object* v___f_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v___f_536_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_536_, 0, v_modifyEnv_532_);
lean_closure_set(v___f_536_, 1, v___x_527_);
v___x_537_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_537_, 0, lean_box(0));
lean_closure_set(v___x_537_, 1, lean_box(0));
lean_closure_set(v___x_537_, 2, lean_box(0));
lean_closure_set(v___x_537_, 3, lean_box(0));
lean_closure_set(v___x_537_, 4, v_getEnv_531_);
v___f_538_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_538_, 0, v___f_536_);
lean_closure_set(v___f_538_, 1, v___f_526_);
v___x_539_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_539_, 0, lean_box(0));
lean_closure_set(v___x_539_, 1, v___x_537_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v___f_538_);
lean_ctor_set(v___x_534_, 0, v___x_539_);
v___x_541_ = v___x_534_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___f_538_);
v___x_541_ = v_reuseFailAlloc_635_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_542_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25);
v___x_543_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 2, v___x_543_);
lean_ctor_set(v___x_523_, 1, v_toMonadRef_525_);
lean_ctor_set(v___x_523_, 0, v___x_542_);
v___x_545_ = v___x_523_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_toMonadRef_525_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v___x_543_);
v___x_545_ = v_reuseFailAlloc_634_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
switch(lean_obj_tag(v_v_440_))
{
case 0:
{
lean_object* v_val_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_561_; 
lean_dec_ref(v___x_541_);
lean_dec(v_toMonadFileMap_529_);
lean_dec_ref(v___f_439_);
lean_dec_ref(v___f_438_);
v_val_546_ = lean_ctor_get(v_v_440_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v_v_440_);
if (v_isSharedCheck_561_ == 0)
{
v___x_548_ = v_v_440_;
v_isShared_549_ = v_isSharedCheck_561_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_val_546_);
lean_dec(v_v_440_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_561_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v_y_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_550_ = l_Lean_TSyntax_getId(v_val_546_);
v_y_551_ = lean_erase_macro_scopes(v___x_550_);
v___x_552_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27));
v___x_553_ = lean_name_eq(v_y_551_, v___x_552_);
lean_dec(v_y_551_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_306__overap_555_; lean_object* v___x_556_; 
lean_del_object(v___x_548_);
v___x_554_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29);
v___x_306__overap_555_ = l_Lean_throwErrorAt___redArg(v___x_519_, v___x_545_, v_val_546_, v___x_554_);
lean_inc(v___y_446_);
lean_inc_ref(v___y_445_);
lean_inc(v___y_444_);
lean_inc_ref(v___y_443_);
lean_inc(v___y_442_);
lean_inc_ref(v___y_441_);
v___x_556_ = lean_apply_7(v___x_306__overap_555_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, lean_box(0));
return v___x_556_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec(v_val_546_);
lean_dec_ref(v___x_545_);
lean_dec_ref(v___x_519_);
v___x_557_ = lean_box(0);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_557_);
v___x_559_ = v___x_548_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
case 1:
{
lean_object* v_val_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_317__overap_568_; lean_object* v___x_569_; 
lean_dec_ref(v___x_541_);
lean_dec(v_toMonadFileMap_529_);
lean_dec_ref(v___f_439_);
lean_dec_ref(v___f_438_);
v_val_562_ = lean_ctor_get(v_v_440_, 0);
lean_inc(v_val_562_);
lean_dec_ref(v_v_440_);
v___x_563_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31);
lean_inc(v_val_562_);
v___x_564_ = l_Lean_MessageData_ofSyntax(v_val_562_);
v___x_565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33);
v___x_567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_317__overap_568_ = l_Lean_throwErrorAt___redArg(v___x_519_, v___x_545_, v_val_562_, v___x_567_);
lean_inc(v___y_446_);
lean_inc_ref(v___y_445_);
lean_inc(v___y_444_);
lean_inc_ref(v___y_443_);
lean_inc(v___y_442_);
lean_inc_ref(v___y_441_);
v___x_569_ = lean_apply_7(v___x_317__overap_568_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, lean_box(0));
return v___x_569_;
}
default: 
{
lean_object* v_val_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_633_; 
v_val_570_ = lean_ctor_get(v_v_440_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v_v_440_);
if (v_isSharedCheck_633_ == 0)
{
v___x_572_ = v_v_440_;
v_isShared_573_ = v_isSharedCheck_633_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_val_570_);
lean_dec(v_v_440_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_633_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v_fileName_574_; lean_object* v_fileMap_575_; lean_object* v_options_576_; lean_object* v_currRecDepth_577_; lean_object* v_maxRecDepth_578_; lean_object* v_ref_579_; lean_object* v_currNamespace_580_; lean_object* v_openDecls_581_; lean_object* v_initHeartbeats_582_; lean_object* v_maxHeartbeats_583_; lean_object* v_quotContext_584_; lean_object* v_currMacroScope_585_; uint8_t v_diag_586_; lean_object* v_cancelTk_x3f_587_; uint8_t v_suppressElabErrors_588_; lean_object* v_inheritedTraceOptions_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___f_592_; lean_object* v_ref_593_; lean_object* v___x_594_; lean_object* v___x_327__overap_595_; lean_object* v___x_596_; 
v_fileName_574_ = lean_ctor_get(v___y_445_, 0);
v_fileMap_575_ = lean_ctor_get(v___y_445_, 1);
v_options_576_ = lean_ctor_get(v___y_445_, 2);
v_currRecDepth_577_ = lean_ctor_get(v___y_445_, 3);
v_maxRecDepth_578_ = lean_ctor_get(v___y_445_, 4);
v_ref_579_ = lean_ctor_get(v___y_445_, 5);
v_currNamespace_580_ = lean_ctor_get(v___y_445_, 6);
v_openDecls_581_ = lean_ctor_get(v___y_445_, 7);
v_initHeartbeats_582_ = lean_ctor_get(v___y_445_, 8);
v_maxHeartbeats_583_ = lean_ctor_get(v___y_445_, 9);
v_quotContext_584_ = lean_ctor_get(v___y_445_, 10);
v_currMacroScope_585_ = lean_ctor_get(v___y_445_, 11);
v_diag_586_ = lean_ctor_get_uint8(v___y_445_, sizeof(void*)*14);
v_cancelTk_x3f_587_ = lean_ctor_get(v___y_445_, 12);
v_suppressElabErrors_588_ = lean_ctor_get_uint8(v___y_445_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_589_ = lean_ctor_get(v___y_445_, 13);
v___x_590_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39));
v___x_591_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40));
v___f_592_ = lean_alloc_closure((void*)(l_Lean_Doc_instFromDocArgDocScope___private__1___lam__1), 4, 2);
lean_closure_set(v___f_592_, 0, v___x_591_);
lean_closure_set(v___f_592_, 1, v___f_438_);
v_ref_593_ = l_Lean_replaceRef(v_val_570_, v_ref_579_);
lean_inc_ref(v_inheritedTraceOptions_589_);
lean_inc(v_cancelTk_x3f_587_);
lean_inc(v_currMacroScope_585_);
lean_inc(v_quotContext_584_);
lean_inc(v_maxHeartbeats_583_);
lean_inc(v_initHeartbeats_582_);
lean_inc(v_openDecls_581_);
lean_inc(v_currNamespace_580_);
lean_inc(v_maxRecDepth_578_);
lean_inc(v_currRecDepth_577_);
lean_inc_ref(v_options_576_);
lean_inc_ref(v_fileMap_575_);
lean_inc_ref(v_fileName_574_);
v___x_594_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_594_, 0, v_fileName_574_);
lean_ctor_set(v___x_594_, 1, v_fileMap_575_);
lean_ctor_set(v___x_594_, 2, v_options_576_);
lean_ctor_set(v___x_594_, 3, v_currRecDepth_577_);
lean_ctor_set(v___x_594_, 4, v_maxRecDepth_578_);
lean_ctor_set(v___x_594_, 5, v_ref_593_);
lean_ctor_set(v___x_594_, 6, v_currNamespace_580_);
lean_ctor_set(v___x_594_, 7, v_openDecls_581_);
lean_ctor_set(v___x_594_, 8, v_initHeartbeats_582_);
lean_ctor_set(v___x_594_, 9, v_maxHeartbeats_583_);
lean_ctor_set(v___x_594_, 10, v_quotContext_584_);
lean_ctor_set(v___x_594_, 11, v_currMacroScope_585_);
lean_ctor_set(v___x_594_, 12, v_cancelTk_x3f_587_);
lean_ctor_set(v___x_594_, 13, v_inheritedTraceOptions_589_);
lean_ctor_set_uint8(v___x_594_, sizeof(void*)*14, v_diag_586_);
lean_ctor_set_uint8(v___x_594_, sizeof(void*)*14 + 1, v_suppressElabErrors_588_);
lean_inc_ref(v___x_545_);
lean_inc_ref(v___x_519_);
v___x_327__overap_595_ = l_Lean_Doc_parseQuotedStrLit___redArg(v___x_519_, v_toMonadFileMap_529_, v___x_541_, v___x_545_, v___x_528_, v___x_590_, v___f_592_, v_val_570_);
lean_inc(v___y_446_);
lean_inc(v___y_444_);
lean_inc_ref(v___y_443_);
lean_inc(v___y_442_);
lean_inc_ref(v___y_441_);
v___x_596_ = lean_apply_7(v___x_327__overap_595_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___x_594_, v___y_446_, lean_box(0));
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_624_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_624_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_624_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_624_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
lean_inc(v_a_597_);
v___x_603_ = l_Lean_Syntax_isOfKind(v_a_597_, v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_358__overap_609_; lean_object* v___x_610_; 
lean_del_object(v___x_599_);
lean_del_object(v___x_572_);
lean_dec_ref(v___f_439_);
v___x_604_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43);
lean_inc(v_a_597_);
v___x_605_ = l_Lean_MessageData_ofSyntax(v_a_597_);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_358__overap_609_ = l_Lean_throwErrorAt___redArg(v___x_519_, v___x_545_, v_a_597_, v___x_608_);
lean_inc(v___y_446_);
lean_inc_ref(v___y_445_);
lean_inc(v___y_444_);
lean_inc_ref(v___y_443_);
lean_inc(v___y_442_);
lean_inc_ref(v___y_441_);
v___x_610_ = lean_apply_7(v___x_358__overap_609_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, lean_box(0));
return v___x_610_;
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; size_t v_sz_615_; size_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
lean_dec_ref(v___x_545_);
lean_dec_ref(v___x_519_);
v___x_611_ = l_Lean_Syntax_getArg(v_a_597_, v___x_601_);
lean_dec(v_a_597_);
v___x_612_ = l_Lean_Syntax_getArgs(v___x_611_);
lean_dec(v___x_611_);
v___x_613_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_612_);
lean_dec_ref(v___x_612_);
v___x_614_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__54));
v_sz_615_ = lean_array_size(v___x_613_);
v___x_616_ = ((size_t)0ULL);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_614_, v___f_439_, v_sz_615_, v___x_616_, v___x_613_);
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 1);
lean_ctor_set(v___x_572_, 0, v___x_617_);
v___x_619_ = v___x_572_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_623_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_619_);
v___x_621_ = v___x_599_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_del_object(v___x_572_);
lean_dec_ref(v___x_545_);
lean_dec_ref(v___x_519_);
lean_dec_ref(v___f_439_);
v_a_625_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_596_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_596_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___lam__2___boxed(lean_object* v___f_658_, lean_object* v___f_659_, lean_object* v_v_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Doc_instFromDocArgDocScope___lam__2(v___f_658_, v___f_659_, v_v_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
return v_res_668_;
}
}
lean_object* runtime_initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Scopes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports = _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports();
lean_mark_persistent(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DocString_Builtin_Scopes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM = _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM();
lean_mark_persistent(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* initialize_Lean_Elab_DocString_Builtin_Parsing(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DocString_Builtin_Scopes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DocString_Builtin_Scopes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DocString_Builtin_Scopes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DocString_Builtin_Scopes(builtin);
}
#ifdef __cplusplus
}
#endif
