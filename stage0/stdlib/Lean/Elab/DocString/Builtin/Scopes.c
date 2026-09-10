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
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
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
lean_dec_ref_known(v_t_6_, 1);
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
lean_object* v___x_219_; lean_object* v_toApplicative_220_; lean_object* v_toFunctor_221_; lean_object* v_toSeq_222_; lean_object* v_toSeqLeft_223_; lean_object* v_toSeqRight_224_; lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_toApplicative_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_388_; 
v___x_219_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1);
v_toApplicative_220_ = lean_ctor_get(v___x_219_, 0);
v_toFunctor_221_ = lean_ctor_get(v_toApplicative_220_, 0);
v_toSeq_222_ = lean_ctor_get(v_toApplicative_220_, 2);
v_toSeqLeft_223_ = lean_ctor_get(v_toApplicative_220_, 3);
v_toSeqRight_224_ = lean_ctor_get(v_toApplicative_220_, 4);
v___f_225_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2));
v___f_226_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3));
lean_inc_ref_n(v_toFunctor_221_, 2);
v___f_227_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_227_, 0, v_toFunctor_221_);
v___f_228_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_228_, 0, v_toFunctor_221_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___f_227_);
lean_ctor_set(v___x_229_, 1, v___f_228_);
lean_inc(v_toSeqRight_224_);
v___f_230_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_230_, 0, v_toSeqRight_224_);
lean_inc(v_toSeqLeft_223_);
v___f_231_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_231_, 0, v_toSeqLeft_223_);
lean_inc(v_toSeq_222_);
v___f_232_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_232_, 0, v_toSeq_222_);
v___x_233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_233_, 0, v___x_229_);
lean_ctor_set(v___x_233_, 1, v___f_225_);
lean_ctor_set(v___x_233_, 2, v___f_232_);
lean_ctor_set(v___x_233_, 3, v___f_231_);
lean_ctor_set(v___x_233_, 4, v___f_230_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___f_226_);
v___x_235_ = l_StateRefT_x27_instMonad___redArg(v___x_234_);
v_toApplicative_236_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_388_ == 0)
{
lean_object* v_unused_389_; 
v_unused_389_ = lean_ctor_get(v___x_235_, 1);
lean_dec(v_unused_389_);
v___x_238_ = v___x_235_;
v_isShared_239_ = v_isSharedCheck_388_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_toApplicative_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_388_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v_toFunctor_240_; lean_object* v_toSeq_241_; lean_object* v_toSeqLeft_242_; lean_object* v_toSeqRight_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_386_; 
v_toFunctor_240_ = lean_ctor_get(v_toApplicative_236_, 0);
v_toSeq_241_ = lean_ctor_get(v_toApplicative_236_, 2);
v_toSeqLeft_242_ = lean_ctor_get(v_toApplicative_236_, 3);
v_toSeqRight_243_ = lean_ctor_get(v_toApplicative_236_, 4);
v_isSharedCheck_386_ = !lean_is_exclusive(v_toApplicative_236_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; 
v_unused_387_ = lean_ctor_get(v_toApplicative_236_, 1);
lean_dec(v_unused_387_);
v___x_245_ = v_toApplicative_236_;
v_isShared_246_ = v_isSharedCheck_386_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_toSeqRight_243_);
lean_inc(v_toSeqLeft_242_);
lean_inc(v_toSeq_241_);
lean_inc(v_toFunctor_240_);
lean_dec(v_toApplicative_236_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_386_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___f_249_; lean_object* v___f_250_; lean_object* v___x_251_; lean_object* v___f_252_; lean_object* v___f_253_; lean_object* v___f_254_; lean_object* v___x_256_; 
v___f_247_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4));
v___f_248_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5));
lean_inc_ref(v_toFunctor_240_);
v___f_249_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_249_, 0, v_toFunctor_240_);
v___f_250_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_250_, 0, v_toFunctor_240_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___f_249_);
lean_ctor_set(v___x_251_, 1, v___f_250_);
v___f_252_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_252_, 0, v_toSeqRight_243_);
v___f_253_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_253_, 0, v_toSeqLeft_242_);
v___f_254_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_254_, 0, v_toSeq_241_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 4, v___f_252_);
lean_ctor_set(v___x_245_, 3, v___f_253_);
lean_ctor_set(v___x_245_, 2, v___f_254_);
lean_ctor_set(v___x_245_, 1, v___f_247_);
lean_ctor_set(v___x_245_, 0, v___x_251_);
v___x_256_ = v___x_245_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___f_247_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v___f_254_);
lean_ctor_set(v_reuseFailAlloc_385_, 3, v___f_253_);
lean_ctor_set(v_reuseFailAlloc_385_, 4, v___f_252_);
v___x_256_ = v_reuseFailAlloc_385_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___f_248_);
lean_ctor_set(v___x_238_, 0, v___x_256_);
v___x_258_ = v___x_238_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___f_248_);
v___x_258_ = v_reuseFailAlloc_384_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; lean_object* v_toApplicative_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_382_; 
v___x_259_ = l_StateRefT_x27_instMonad___redArg(v___x_258_);
v_toApplicative_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; 
v_unused_383_ = lean_ctor_get(v___x_259_, 1);
lean_dec(v_unused_383_);
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_382_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_toApplicative_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_382_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_toFunctor_264_; lean_object* v_toSeq_265_; lean_object* v_toSeqLeft_266_; lean_object* v_toSeqRight_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_380_; 
v_toFunctor_264_ = lean_ctor_get(v_toApplicative_260_, 0);
v_toSeq_265_ = lean_ctor_get(v_toApplicative_260_, 2);
v_toSeqLeft_266_ = lean_ctor_get(v_toApplicative_260_, 3);
v_toSeqRight_267_ = lean_ctor_get(v_toApplicative_260_, 4);
v_isSharedCheck_380_ = !lean_is_exclusive(v_toApplicative_260_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v_toApplicative_260_, 1);
lean_dec(v_unused_381_);
v___x_269_ = v_toApplicative_260_;
v_isShared_270_ = v_isSharedCheck_380_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_toSeqRight_267_);
lean_inc(v_toSeqLeft_266_);
lean_inc(v_toSeq_265_);
lean_inc(v_toFunctor_264_);
lean_dec(v_toApplicative_260_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_380_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___f_271_; lean_object* v___f_272_; lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___f_276_; lean_object* v___f_277_; lean_object* v___f_278_; lean_object* v___x_280_; 
v___f_271_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6));
v___f_272_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7));
lean_inc_ref(v_toFunctor_264_);
v___f_273_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_273_, 0, v_toFunctor_264_);
v___f_274_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_274_, 0, v_toFunctor_264_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___f_273_);
lean_ctor_set(v___x_275_, 1, v___f_274_);
v___f_276_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_276_, 0, v_toSeqRight_267_);
v___f_277_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_277_, 0, v_toSeqLeft_266_);
v___f_278_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_278_, 0, v_toSeq_265_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 4, v___f_276_);
lean_ctor_set(v___x_269_, 3, v___f_277_);
lean_ctor_set(v___x_269_, 2, v___f_278_);
lean_ctor_set(v___x_269_, 1, v___f_271_);
lean_ctor_set(v___x_269_, 0, v___x_275_);
v___x_280_ = v___x_269_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___f_271_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v___f_278_);
lean_ctor_set(v_reuseFailAlloc_379_, 3, v___f_277_);
lean_ctor_set(v_reuseFailAlloc_379_, 4, v___f_276_);
v___x_280_ = v_reuseFailAlloc_379_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_282_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___f_272_);
lean_ctor_set(v___x_262_, 0, v___x_280_);
v___x_282_ = v___x_262_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v___f_272_);
v___x_282_ = v_reuseFailAlloc_378_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v_toMonadQuotation_284_; lean_object* v_toMonadRef_285_; lean_object* v___f_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_toMonadFileMap_289_; lean_object* v___x_290_; lean_object* v_getEnv_291_; lean_object* v_modifyEnv_292_; lean_object* v___f_293_; lean_object* v___x_294_; lean_object* v___f_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_283_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
v_toMonadQuotation_284_ = lean_ctor_get(v___x_283_, 0);
v_toMonadRef_285_ = lean_ctor_get(v_toMonadQuotation_284_, 0);
v___f_286_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8));
v___x_287_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9));
v___x_288_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13);
v_toMonadFileMap_289_ = lean_ctor_get(v___x_288_, 0);
v___x_290_ = l_Lean_Meta_instMonadEnvMetaM;
v_getEnv_291_ = lean_ctor_get(v___x_290_, 0);
v_modifyEnv_292_ = lean_ctor_get(v___x_290_, 1);
lean_inc(v_modifyEnv_292_);
v___f_293_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_293_, 0, v_modifyEnv_292_);
lean_closure_set(v___f_293_, 1, v___x_287_);
lean_inc(v_getEnv_291_);
v___x_294_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_294_, 0, lean_box(0));
lean_closure_set(v___x_294_, 1, lean_box(0));
lean_closure_set(v___x_294_, 2, lean_box(0));
lean_closure_set(v___x_294_, 3, lean_box(0));
lean_closure_set(v___x_294_, 4, v_getEnv_291_);
v___f_295_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_295_, 0, v___f_293_);
lean_closure_set(v___f_295_, 1, v___f_286_);
v___x_296_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_296_, 0, lean_box(0));
lean_closure_set(v___x_296_, 1, v___x_294_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___f_295_);
v___x_298_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25);
v___x_299_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
lean_inc_ref(v_toMonadRef_285_);
v___x_300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v_toMonadRef_285_);
lean_ctor_set(v___x_300_, 2, v___x_299_);
switch(lean_obj_tag(v_v_211_))
{
case 0:
{
lean_object* v_val_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_316_; 
lean_dec_ref_known(v___x_297_, 2);
v_val_301_ = lean_ctor_get(v_v_211_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v_v_211_);
if (v_isSharedCheck_316_ == 0)
{
v___x_303_ = v_v_211_;
v_isShared_304_ = v_isSharedCheck_316_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_val_301_);
lean_dec(v_v_211_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_316_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v_y_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_305_ = l_Lean_TSyntax_getId(v_val_301_);
v_y_306_ = l_Lean_Name_eraseMacroScopes(v___x_305_);
lean_dec(v___x_305_);
v___x_307_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27));
v___x_308_ = lean_name_eq(v_y_306_, v___x_307_);
lean_dec(v_y_306_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_1514__overap_310_; lean_object* v___x_311_; 
lean_del_object(v___x_303_);
v___x_309_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29);
v___x_1514__overap_310_ = l_Lean_throwErrorAt___redArg(v___x_282_, v___x_300_, v_val_301_, v___x_309_);
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
v___x_311_ = lean_apply_7(v___x_1514__overap_310_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, lean_box(0));
return v___x_311_;
}
else
{
lean_object* v___x_312_; lean_object* v___x_314_; 
lean_dec(v_val_301_);
lean_dec_ref_known(v___x_300_, 3);
lean_dec_ref(v___x_282_);
v___x_312_ = lean_box(0);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_312_);
v___x_314_ = v___x_303_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
case 1:
{
lean_object* v_val_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_1536__overap_323_; lean_object* v___x_324_; 
lean_dec_ref_known(v___x_297_, 2);
v_val_317_ = lean_ctor_get(v_v_211_, 0);
lean_inc_n(v_val_317_, 2);
lean_dec_ref_known(v_v_211_, 1);
v___x_318_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31);
v___x_319_ = l_Lean_MessageData_ofSyntax(v_val_317_);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33);
v___x_322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_1536__overap_323_ = l_Lean_throwErrorAt___redArg(v___x_282_, v___x_300_, v_val_317_, v___x_322_);
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
v___x_324_ = lean_apply_7(v___x_1536__overap_323_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, lean_box(0));
return v___x_324_;
}
default: 
{
lean_object* v_val_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_377_; 
v_val_325_ = lean_ctor_get(v_v_211_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_v_211_);
if (v_isSharedCheck_377_ == 0)
{
v___x_327_ = v_v_211_;
v_isShared_328_ = v_isSharedCheck_377_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_val_325_);
lean_dec(v_v_211_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_377_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_toCold_329_; lean_object* v_currRecDepth_330_; lean_object* v_ref_331_; uint8_t v_diag_332_; uint8_t v_suppressElabErrors_333_; lean_object* v___x_334_; lean_object* v___f_335_; lean_object* v_ref_336_; lean_object* v___x_337_; lean_object* v___x_1758__overap_338_; lean_object* v___x_339_; 
v_toCold_329_ = lean_ctor_get(v_a_216_, 0);
v_currRecDepth_330_ = lean_ctor_get(v_a_216_, 1);
v_ref_331_ = lean_ctor_get(v_a_216_, 2);
v_diag_332_ = lean_ctor_get_uint8(v_a_216_, sizeof(void*)*3);
v_suppressElabErrors_333_ = lean_ctor_get_uint8(v_a_216_, sizeof(void*)*3 + 1);
v___x_334_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39));
v___f_335_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__41));
v_ref_336_ = l_Lean_replaceRef(v_val_325_, v_ref_331_);
lean_inc(v_currRecDepth_330_);
lean_inc_ref(v_toCold_329_);
v___x_337_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_337_, 0, v_toCold_329_);
lean_ctor_set(v___x_337_, 1, v_currRecDepth_330_);
lean_ctor_set(v___x_337_, 2, v_ref_336_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*3, v_diag_332_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*3 + 1, v_suppressElabErrors_333_);
lean_inc_ref(v___x_300_);
lean_inc(v_toMonadFileMap_289_);
lean_inc_ref(v___x_282_);
v___x_1758__overap_338_ = l_Lean_Doc_parseQuotedStrLit___redArg(v___x_282_, v_toMonadFileMap_289_, v___x_297_, v___x_300_, v___x_288_, v___x_334_, v___f_335_, v_val_325_);
lean_inc(v_a_217_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
v___x_339_ = lean_apply_7(v___x_1758__overap_338_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v___x_337_, v_a_217_, lean_box(0));
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_368_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_368_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_368_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_368_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
lean_inc(v_a_340_);
v___x_346_ = l_Lean_Syntax_isOfKind(v_a_340_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_1792__overap_352_; lean_object* v___x_353_; 
lean_del_object(v___x_342_);
lean_del_object(v___x_327_);
v___x_347_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43);
lean_inc(v_a_340_);
v___x_348_ = l_Lean_MessageData_ofSyntax(v_a_340_);
v___x_349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33);
v___x_351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_349_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_1792__overap_352_ = l_Lean_throwErrorAt___redArg(v___x_282_, v___x_300_, v_a_340_, v___x_351_);
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
v___x_353_ = lean_apply_7(v___x_1792__overap_352_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, lean_box(0));
return v___x_353_;
}
else
{
lean_object* v___f_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; size_t v_sz_359_; size_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
lean_dec_ref_known(v___x_300_, 3);
lean_dec_ref(v___x_282_);
v___f_354_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44));
v___x_355_ = l_Lean_Syntax_getArg(v_a_340_, v___x_344_);
lean_dec(v_a_340_);
v___x_356_ = l_Lean_Syntax_getArgs(v___x_355_);
lean_dec(v___x_355_);
v___x_357_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_356_);
lean_dec_ref(v___x_356_);
v___x_358_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__54));
v_sz_359_ = lean_array_size(v___x_357_);
v___x_360_ = ((size_t)0ULL);
v___x_361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_358_, v___f_354_, v_sz_359_, v___x_360_, v___x_357_);
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 1);
lean_ctor_set(v___x_327_, 0, v___x_361_);
v___x_363_ = v___x_327_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_367_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_363_);
v___x_365_ = v___x_342_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_del_object(v___x_327_);
lean_dec_ref_known(v___x_300_, 3);
lean_dec_ref(v___x_282_);
v_a_369_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_339_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_339_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
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
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___boxed(lean_object* v_v_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Doc_instFromDocArgDocScope___private__1(v_v_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___lam__2(lean_object* v___f_399_, lean_object* v___f_400_, lean_object* v_v_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; lean_object* v_toApplicative_410_; lean_object* v_toFunctor_411_; lean_object* v_toSeq_412_; lean_object* v_toSeqLeft_413_; lean_object* v_toSeqRight_414_; lean_object* v___f_415_; lean_object* v___f_416_; lean_object* v___f_417_; lean_object* v___f_418_; lean_object* v___x_419_; lean_object* v___f_420_; lean_object* v___f_421_; lean_object* v___f_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v_toApplicative_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_578_; 
v___x_409_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1);
v_toApplicative_410_ = lean_ctor_get(v___x_409_, 0);
v_toFunctor_411_ = lean_ctor_get(v_toApplicative_410_, 0);
v_toSeq_412_ = lean_ctor_get(v_toApplicative_410_, 2);
v_toSeqLeft_413_ = lean_ctor_get(v_toApplicative_410_, 3);
v_toSeqRight_414_ = lean_ctor_get(v_toApplicative_410_, 4);
v___f_415_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2));
v___f_416_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3));
lean_inc_ref_n(v_toFunctor_411_, 2);
v___f_417_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_417_, 0, v_toFunctor_411_);
v___f_418_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_418_, 0, v_toFunctor_411_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___f_417_);
lean_ctor_set(v___x_419_, 1, v___f_418_);
lean_inc(v_toSeqRight_414_);
v___f_420_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_420_, 0, v_toSeqRight_414_);
lean_inc(v_toSeqLeft_413_);
v___f_421_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_421_, 0, v_toSeqLeft_413_);
lean_inc(v_toSeq_412_);
v___f_422_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_422_, 0, v_toSeq_412_);
v___x_423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_423_, 0, v___x_419_);
lean_ctor_set(v___x_423_, 1, v___f_415_);
lean_ctor_set(v___x_423_, 2, v___f_422_);
lean_ctor_set(v___x_423_, 3, v___f_421_);
lean_ctor_set(v___x_423_, 4, v___f_420_);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v___f_416_);
v___x_425_ = l_StateRefT_x27_instMonad___redArg(v___x_424_);
v_toApplicative_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v___x_425_, 1);
lean_dec(v_unused_579_);
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_578_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_toApplicative_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_578_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_toFunctor_430_; lean_object* v_toSeq_431_; lean_object* v_toSeqLeft_432_; lean_object* v_toSeqRight_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_576_; 
v_toFunctor_430_ = lean_ctor_get(v_toApplicative_426_, 0);
v_toSeq_431_ = lean_ctor_get(v_toApplicative_426_, 2);
v_toSeqLeft_432_ = lean_ctor_get(v_toApplicative_426_, 3);
v_toSeqRight_433_ = lean_ctor_get(v_toApplicative_426_, 4);
v_isSharedCheck_576_ = !lean_is_exclusive(v_toApplicative_426_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v_toApplicative_426_, 1);
lean_dec(v_unused_577_);
v___x_435_ = v_toApplicative_426_;
v_isShared_436_ = v_isSharedCheck_576_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_toSeqRight_433_);
lean_inc(v_toSeqLeft_432_);
lean_inc(v_toSeq_431_);
lean_inc(v_toFunctor_430_);
lean_dec(v_toApplicative_426_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_576_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___f_437_; lean_object* v___f_438_; lean_object* v___f_439_; lean_object* v___f_440_; lean_object* v___x_441_; lean_object* v___f_442_; lean_object* v___f_443_; lean_object* v___f_444_; lean_object* v___x_446_; 
v___f_437_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4));
v___f_438_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5));
lean_inc_ref(v_toFunctor_430_);
v___f_439_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_439_, 0, v_toFunctor_430_);
v___f_440_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_440_, 0, v_toFunctor_430_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___f_439_);
lean_ctor_set(v___x_441_, 1, v___f_440_);
v___f_442_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_442_, 0, v_toSeqRight_433_);
v___f_443_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_443_, 0, v_toSeqLeft_432_);
v___f_444_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_444_, 0, v_toSeq_431_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 4, v___f_442_);
lean_ctor_set(v___x_435_, 3, v___f_443_);
lean_ctor_set(v___x_435_, 2, v___f_444_);
lean_ctor_set(v___x_435_, 1, v___f_437_);
lean_ctor_set(v___x_435_, 0, v___x_441_);
v___x_446_ = v___x_435_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v___f_437_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v___f_444_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v___f_443_);
lean_ctor_set(v_reuseFailAlloc_575_, 4, v___f_442_);
v___x_446_ = v_reuseFailAlloc_575_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_448_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___f_438_);
lean_ctor_set(v___x_428_, 0, v___x_446_);
v___x_448_ = v___x_428_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___f_438_);
v___x_448_ = v_reuseFailAlloc_574_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v_toApplicative_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_572_; 
v___x_449_ = l_StateRefT_x27_instMonad___redArg(v___x_448_);
v_toApplicative_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v___x_449_, 1);
lean_dec(v_unused_573_);
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_572_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_toApplicative_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_572_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_toFunctor_454_; lean_object* v_toSeq_455_; lean_object* v_toSeqLeft_456_; lean_object* v_toSeqRight_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_570_; 
v_toFunctor_454_ = lean_ctor_get(v_toApplicative_450_, 0);
v_toSeq_455_ = lean_ctor_get(v_toApplicative_450_, 2);
v_toSeqLeft_456_ = lean_ctor_get(v_toApplicative_450_, 3);
v_toSeqRight_457_ = lean_ctor_get(v_toApplicative_450_, 4);
v_isSharedCheck_570_ = !lean_is_exclusive(v_toApplicative_450_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; 
v_unused_571_ = lean_ctor_get(v_toApplicative_450_, 1);
lean_dec(v_unused_571_);
v___x_459_ = v_toApplicative_450_;
v_isShared_460_ = v_isSharedCheck_570_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_toSeqRight_457_);
lean_inc(v_toSeqLeft_456_);
lean_inc(v_toSeq_455_);
lean_inc(v_toFunctor_454_);
lean_dec(v_toApplicative_450_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_570_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___f_461_; lean_object* v___f_462_; lean_object* v___f_463_; lean_object* v___f_464_; lean_object* v___x_465_; lean_object* v___f_466_; lean_object* v___f_467_; lean_object* v___f_468_; lean_object* v___x_470_; 
v___f_461_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6));
v___f_462_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7));
lean_inc_ref(v_toFunctor_454_);
v___f_463_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_463_, 0, v_toFunctor_454_);
v___f_464_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_464_, 0, v_toFunctor_454_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___f_463_);
lean_ctor_set(v___x_465_, 1, v___f_464_);
v___f_466_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_466_, 0, v_toSeqRight_457_);
v___f_467_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_467_, 0, v_toSeqLeft_456_);
v___f_468_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_468_, 0, v_toSeq_455_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 4, v___f_466_);
lean_ctor_set(v___x_459_, 3, v___f_467_);
lean_ctor_set(v___x_459_, 2, v___f_468_);
lean_ctor_set(v___x_459_, 1, v___f_461_);
lean_ctor_set(v___x_459_, 0, v___x_465_);
v___x_470_ = v___x_459_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v___f_461_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v___f_468_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v___f_467_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v___f_466_);
v___x_470_ = v_reuseFailAlloc_569_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_472_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___f_462_);
lean_ctor_set(v___x_452_, 0, v___x_470_);
v___x_472_ = v___x_452_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___f_462_);
v___x_472_ = v_reuseFailAlloc_568_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_473_; lean_object* v_toMonadQuotation_474_; lean_object* v_toMonadRef_475_; lean_object* v___f_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v_toMonadFileMap_479_; lean_object* v___x_480_; lean_object* v_getEnv_481_; lean_object* v_modifyEnv_482_; lean_object* v___f_483_; lean_object* v___x_484_; lean_object* v___f_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_473_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
v_toMonadQuotation_474_ = lean_ctor_get(v___x_473_, 0);
v_toMonadRef_475_ = lean_ctor_get(v_toMonadQuotation_474_, 0);
v___f_476_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8));
v___x_477_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9));
v___x_478_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13);
v_toMonadFileMap_479_ = lean_ctor_get(v___x_478_, 0);
v___x_480_ = l_Lean_Meta_instMonadEnvMetaM;
v_getEnv_481_ = lean_ctor_get(v___x_480_, 0);
v_modifyEnv_482_ = lean_ctor_get(v___x_480_, 1);
lean_inc(v_modifyEnv_482_);
v___f_483_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_483_, 0, v_modifyEnv_482_);
lean_closure_set(v___f_483_, 1, v___x_477_);
lean_inc(v_getEnv_481_);
v___x_484_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_484_, 0, lean_box(0));
lean_closure_set(v___x_484_, 1, lean_box(0));
lean_closure_set(v___x_484_, 2, lean_box(0));
lean_closure_set(v___x_484_, 3, lean_box(0));
lean_closure_set(v___x_484_, 4, v_getEnv_481_);
v___f_485_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_485_, 0, v___f_483_);
lean_closure_set(v___f_485_, 1, v___f_476_);
v___x_486_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_486_, 0, lean_box(0));
lean_closure_set(v___x_486_, 1, v___x_484_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___f_485_);
v___x_488_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25);
v___x_489_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
lean_inc_ref(v_toMonadRef_475_);
v___x_490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v_toMonadRef_475_);
lean_ctor_set(v___x_490_, 2, v___x_489_);
switch(lean_obj_tag(v_v_401_))
{
case 0:
{
lean_object* v_val_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_506_; 
lean_dec_ref_known(v___x_487_, 2);
lean_dec_ref(v___f_400_);
lean_dec_ref(v___f_399_);
v_val_491_ = lean_ctor_get(v_v_401_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_v_401_);
if (v_isSharedCheck_506_ == 0)
{
v___x_493_ = v_v_401_;
v_isShared_494_ = v_isSharedCheck_506_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_val_491_);
lean_dec(v_v_401_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_506_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v_y_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_495_ = l_Lean_TSyntax_getId(v_val_491_);
v_y_496_ = l_Lean_Name_eraseMacroScopes(v___x_495_);
lean_dec(v___x_495_);
v___x_497_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27));
v___x_498_ = lean_name_eq(v_y_496_, v___x_497_);
lean_dec(v_y_496_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_295__overap_500_; lean_object* v___x_501_; 
lean_del_object(v___x_493_);
v___x_499_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29);
v___x_295__overap_500_ = l_Lean_throwErrorAt___redArg(v___x_472_, v___x_490_, v_val_491_, v___x_499_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
v___x_501_ = lean_apply_7(v___x_295__overap_500_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, lean_box(0));
return v___x_501_;
}
else
{
lean_object* v___x_502_; lean_object* v___x_504_; 
lean_dec(v_val_491_);
lean_dec_ref_known(v___x_490_, 3);
lean_dec_ref(v___x_472_);
v___x_502_ = lean_box(0);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_502_);
v___x_504_ = v___x_493_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
case 1:
{
lean_object* v_val_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_306__overap_513_; lean_object* v___x_514_; 
lean_dec_ref_known(v___x_487_, 2);
lean_dec_ref(v___f_400_);
lean_dec_ref(v___f_399_);
v_val_507_ = lean_ctor_get(v_v_401_, 0);
lean_inc_n(v_val_507_, 2);
lean_dec_ref_known(v_v_401_, 1);
v___x_508_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31);
v___x_509_ = l_Lean_MessageData_ofSyntax(v_val_507_);
v___x_510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33);
v___x_512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_306__overap_513_ = l_Lean_throwErrorAt___redArg(v___x_472_, v___x_490_, v_val_507_, v___x_512_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
v___x_514_ = lean_apply_7(v___x_306__overap_513_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, lean_box(0));
return v___x_514_;
}
default: 
{
lean_object* v_val_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_567_; 
v_val_515_ = lean_ctor_get(v_v_401_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v_v_401_);
if (v_isSharedCheck_567_ == 0)
{
v___x_517_ = v_v_401_;
v_isShared_518_ = v_isSharedCheck_567_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_val_515_);
lean_dec(v_v_401_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_567_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v_toCold_519_; lean_object* v_currRecDepth_520_; lean_object* v_ref_521_; uint8_t v_diag_522_; uint8_t v_suppressElabErrors_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___f_526_; lean_object* v_ref_527_; lean_object* v___x_528_; lean_object* v___x_316__overap_529_; lean_object* v___x_530_; 
v_toCold_519_ = lean_ctor_get(v___y_406_, 0);
v_currRecDepth_520_ = lean_ctor_get(v___y_406_, 1);
v_ref_521_ = lean_ctor_get(v___y_406_, 2);
v_diag_522_ = lean_ctor_get_uint8(v___y_406_, sizeof(void*)*3);
v_suppressElabErrors_523_ = lean_ctor_get_uint8(v___y_406_, sizeof(void*)*3 + 1);
v___x_524_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39));
v___x_525_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40));
v___f_526_ = lean_alloc_closure((void*)(l_Lean_Doc_instFromDocArgDocScope___private__1___lam__1), 4, 2);
lean_closure_set(v___f_526_, 0, v___x_525_);
lean_closure_set(v___f_526_, 1, v___f_399_);
v_ref_527_ = l_Lean_replaceRef(v_val_515_, v_ref_521_);
lean_inc(v_currRecDepth_520_);
lean_inc_ref(v_toCold_519_);
v___x_528_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_528_, 0, v_toCold_519_);
lean_ctor_set(v___x_528_, 1, v_currRecDepth_520_);
lean_ctor_set(v___x_528_, 2, v_ref_527_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*3, v_diag_522_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*3 + 1, v_suppressElabErrors_523_);
lean_inc_ref(v___x_490_);
lean_inc(v_toMonadFileMap_479_);
lean_inc_ref(v___x_472_);
v___x_316__overap_529_ = l_Lean_Doc_parseQuotedStrLit___redArg(v___x_472_, v_toMonadFileMap_479_, v___x_487_, v___x_490_, v___x_478_, v___x_524_, v___f_526_, v_val_515_);
lean_inc(v___y_407_);
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
v___x_530_ = lean_apply_7(v___x_316__overap_529_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___x_528_, v___y_407_, lean_box(0));
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_558_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_558_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_558_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_558_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
lean_inc(v_a_531_);
v___x_537_ = l_Lean_Syntax_isOfKind(v_a_531_, v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_347__overap_543_; lean_object* v___x_544_; 
lean_del_object(v___x_533_);
lean_del_object(v___x_517_);
lean_dec_ref(v___f_400_);
v___x_538_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43);
lean_inc(v_a_531_);
v___x_539_ = l_Lean_MessageData_ofSyntax(v_a_531_);
v___x_540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_347__overap_543_ = l_Lean_throwErrorAt___redArg(v___x_472_, v___x_490_, v_a_531_, v___x_542_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
v___x_544_ = lean_apply_7(v___x_347__overap_543_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, lean_box(0));
return v___x_544_;
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; size_t v_sz_549_; size_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
lean_dec_ref_known(v___x_490_, 3);
lean_dec_ref(v___x_472_);
v___x_545_ = l_Lean_Syntax_getArg(v_a_531_, v___x_535_);
lean_dec(v_a_531_);
v___x_546_ = l_Lean_Syntax_getArgs(v___x_545_);
lean_dec(v___x_545_);
v___x_547_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_546_);
lean_dec_ref(v___x_546_);
v___x_548_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__54));
v_sz_549_ = lean_array_size(v___x_547_);
v___x_550_ = ((size_t)0ULL);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_548_, v___f_400_, v_sz_549_, v___x_550_, v___x_547_);
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 1);
lean_ctor_set(v___x_517_, 0, v___x_551_);
v___x_553_ = v___x_517_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_557_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_555_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_553_);
v___x_555_ = v___x_533_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_del_object(v___x_517_);
lean_dec_ref_known(v___x_490_, 3);
lean_dec_ref(v___x_472_);
lean_dec_ref(v___f_400_);
v_a_559_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_530_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_530_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
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
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___lam__2___boxed(lean_object* v___f_580_, lean_object* v___f_581_, lean_object* v_v_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Doc_instFromDocArgDocScope___lam__2(v___f_580_, v___f_581_, v_v_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
return v_res_590_;
}
}
lean_object* runtime_initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Scopes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
