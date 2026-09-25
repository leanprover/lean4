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
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_Core_instMonadOptionsCoreM;
lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId___boxed(lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__26;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__28;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29;
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__30 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__30_value;
static const lean_ctor_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(120, 104, 189, 185, 38, 81, 44, 71)}};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31_value;
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "Unexpected identifier, expected `local` or a string of imports"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__32 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__32_value;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33;
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unexpected number `"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__34 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__34_value;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35;
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__36 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__36_value;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instFromDocArgDocScope___private__1___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__38 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__38_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_getId___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_whitespace, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instFromDocArgDocScope___private__1___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__38_value)} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__41 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__41_value;
static const lean_string_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Expected comma-separated imports list, got `"};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__42 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__42_value;
static lean_once_cell_t l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__45 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__45_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__46 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__46_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__47 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__47_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__48 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__48_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__49 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__49_value;
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__50 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__50_value;
static const lean_ctor_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__45_value)}};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__51 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__51_value;
static const lean_ctor_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__51_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__46_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__47_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__48_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__49_value)}};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__52 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__52_value;
static const lean_ctor_object l_Lean_Doc_instFromDocArgDocScope___private__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__52_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__50_value)}};
static const lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___closed__53 = (const lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__53_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instFromDocArgDocScope___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instFromDocArgDocScope___lam__2___boxed, .m_arity = 10, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__38_value),((lean_object*)&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39_value)} };
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
v___x_111_ = l_instMonadEIO___redArg();
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
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__26(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = l_Lean_Core_instMonadOptionsCoreM;
v___x_163_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9));
v___x_164_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___x_163_, v___x_162_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27(void){
_start:
{
lean_object* v___x_165_; lean_object* v___f_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__26, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__26_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__26);
v___f_166_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8));
v___x_167_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___f_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__28(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27);
v___x_169_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9));
v___x_170_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___x_169_, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29(void){
_start:
{
lean_object* v___x_171_; lean_object* v___f_172_; lean_object* v___x_173_; 
v___x_171_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__28, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__28_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__28);
v___f_172_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8));
v___x_173_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___f_172_, v___x_171_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__32));
v___x_179_ = l_Lean_stringToMessageData(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__34));
v___x_182_ = l_Lean_stringToMessageData(v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__36));
v___x_185_ = l_Lean_stringToMessageData(v___x_184_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__42));
v___x_194_ = l_Lean_stringToMessageData(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1(lean_object* v_v_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v___x_222_; lean_object* v_toApplicative_223_; lean_object* v_toFunctor_224_; lean_object* v_toSeq_225_; lean_object* v_toSeqLeft_226_; lean_object* v_toSeqRight_227_; lean_object* v___f_228_; lean_object* v___f_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___x_232_; lean_object* v___f_233_; lean_object* v___f_234_; lean_object* v___f_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v_toApplicative_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_392_; 
v___x_222_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1);
v_toApplicative_223_ = lean_ctor_get(v___x_222_, 0);
v_toFunctor_224_ = lean_ctor_get(v_toApplicative_223_, 0);
v_toSeq_225_ = lean_ctor_get(v_toApplicative_223_, 2);
v_toSeqLeft_226_ = lean_ctor_get(v_toApplicative_223_, 3);
v_toSeqRight_227_ = lean_ctor_get(v_toApplicative_223_, 4);
v___f_228_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2));
v___f_229_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3));
lean_inc_ref_n(v_toFunctor_224_, 2);
v___f_230_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_230_, 0, v_toFunctor_224_);
v___f_231_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_231_, 0, v_toFunctor_224_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v___f_230_);
lean_ctor_set(v___x_232_, 1, v___f_231_);
lean_inc(v_toSeqRight_227_);
v___f_233_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_233_, 0, v_toSeqRight_227_);
lean_inc(v_toSeqLeft_226_);
v___f_234_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_234_, 0, v_toSeqLeft_226_);
lean_inc(v_toSeq_225_);
v___f_235_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_235_, 0, v_toSeq_225_);
v___x_236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_236_, 0, v___x_232_);
lean_ctor_set(v___x_236_, 1, v___f_228_);
lean_ctor_set(v___x_236_, 2, v___f_235_);
lean_ctor_set(v___x_236_, 3, v___f_234_);
lean_ctor_set(v___x_236_, 4, v___f_233_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___f_229_);
v___x_238_ = l_StateRefT_x27_instMonad___redArg(v___x_237_);
v_toApplicative_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; 
v_unused_393_ = lean_ctor_get(v___x_238_, 1);
lean_dec(v_unused_393_);
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_392_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_toApplicative_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_392_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v_toFunctor_243_; lean_object* v_toSeq_244_; lean_object* v_toSeqLeft_245_; lean_object* v_toSeqRight_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_390_; 
v_toFunctor_243_ = lean_ctor_get(v_toApplicative_239_, 0);
v_toSeq_244_ = lean_ctor_get(v_toApplicative_239_, 2);
v_toSeqLeft_245_ = lean_ctor_get(v_toApplicative_239_, 3);
v_toSeqRight_246_ = lean_ctor_get(v_toApplicative_239_, 4);
v_isSharedCheck_390_ = !lean_is_exclusive(v_toApplicative_239_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v_toApplicative_239_, 1);
lean_dec(v_unused_391_);
v___x_248_ = v_toApplicative_239_;
v_isShared_249_ = v_isSharedCheck_390_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_toSeqRight_246_);
lean_inc(v_toSeqLeft_245_);
lean_inc(v_toSeq_244_);
lean_inc(v_toFunctor_243_);
lean_dec(v_toApplicative_239_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_390_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___f_250_; lean_object* v___f_251_; lean_object* v___f_252_; lean_object* v___f_253_; lean_object* v___x_254_; lean_object* v___f_255_; lean_object* v___f_256_; lean_object* v___f_257_; lean_object* v___x_259_; 
v___f_250_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4));
v___f_251_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5));
lean_inc_ref(v_toFunctor_243_);
v___f_252_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_252_, 0, v_toFunctor_243_);
v___f_253_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_253_, 0, v_toFunctor_243_);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v___f_252_);
lean_ctor_set(v___x_254_, 1, v___f_253_);
v___f_255_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_255_, 0, v_toSeqRight_246_);
v___f_256_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_256_, 0, v_toSeqLeft_245_);
v___f_257_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_257_, 0, v_toSeq_244_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 4, v___f_255_);
lean_ctor_set(v___x_248_, 3, v___f_256_);
lean_ctor_set(v___x_248_, 2, v___f_257_);
lean_ctor_set(v___x_248_, 1, v___f_250_);
lean_ctor_set(v___x_248_, 0, v___x_254_);
v___x_259_ = v___x_248_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___f_250_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v___f_257_);
lean_ctor_set(v_reuseFailAlloc_389_, 3, v___f_256_);
lean_ctor_set(v_reuseFailAlloc_389_, 4, v___f_255_);
v___x_259_ = v_reuseFailAlloc_389_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_261_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___f_251_);
lean_ctor_set(v___x_241_, 0, v___x_259_);
v___x_261_ = v___x_241_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v___f_251_);
v___x_261_ = v_reuseFailAlloc_388_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; lean_object* v_toApplicative_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_386_; 
v___x_262_ = l_StateRefT_x27_instMonad___redArg(v___x_261_);
v_toApplicative_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; 
v_unused_387_ = lean_ctor_get(v___x_262_, 1);
lean_dec(v_unused_387_);
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_386_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_toApplicative_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_386_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v_toFunctor_267_; lean_object* v_toSeq_268_; lean_object* v_toSeqLeft_269_; lean_object* v_toSeqRight_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_384_; 
v_toFunctor_267_ = lean_ctor_get(v_toApplicative_263_, 0);
v_toSeq_268_ = lean_ctor_get(v_toApplicative_263_, 2);
v_toSeqLeft_269_ = lean_ctor_get(v_toApplicative_263_, 3);
v_toSeqRight_270_ = lean_ctor_get(v_toApplicative_263_, 4);
v_isSharedCheck_384_ = !lean_is_exclusive(v_toApplicative_263_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v_toApplicative_263_, 1);
lean_dec(v_unused_385_);
v___x_272_ = v_toApplicative_263_;
v_isShared_273_ = v_isSharedCheck_384_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_toSeqRight_270_);
lean_inc(v_toSeqLeft_269_);
lean_inc(v_toSeq_268_);
lean_inc(v_toFunctor_267_);
lean_dec(v_toApplicative_263_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_384_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___f_274_; lean_object* v___f_275_; lean_object* v___f_276_; lean_object* v___f_277_; lean_object* v___x_278_; lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___f_281_; lean_object* v___x_283_; 
v___f_274_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6));
v___f_275_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7));
lean_inc_ref(v_toFunctor_267_);
v___f_276_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_276_, 0, v_toFunctor_267_);
v___f_277_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_277_, 0, v_toFunctor_267_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___f_276_);
lean_ctor_set(v___x_278_, 1, v___f_277_);
v___f_279_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_279_, 0, v_toSeqRight_270_);
v___f_280_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_280_, 0, v_toSeqLeft_269_);
v___f_281_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_281_, 0, v_toSeq_268_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 4, v___f_279_);
lean_ctor_set(v___x_272_, 3, v___f_280_);
lean_ctor_set(v___x_272_, 2, v___f_281_);
lean_ctor_set(v___x_272_, 1, v___f_274_);
lean_ctor_set(v___x_272_, 0, v___x_278_);
v___x_283_ = v___x_272_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___f_274_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v___f_281_);
lean_ctor_set(v_reuseFailAlloc_383_, 3, v___f_280_);
lean_ctor_set(v_reuseFailAlloc_383_, 4, v___f_279_);
v___x_283_ = v_reuseFailAlloc_383_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_285_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v___f_275_);
lean_ctor_set(v___x_265_, 0, v___x_283_);
v___x_285_ = v___x_265_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___f_275_);
v___x_285_ = v_reuseFailAlloc_382_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; lean_object* v_toMonadQuotation_287_; lean_object* v_toMonadRef_288_; lean_object* v___f_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_toMonadFileMap_292_; lean_object* v___x_293_; lean_object* v_getEnv_294_; lean_object* v_modifyEnv_295_; lean_object* v___f_296_; lean_object* v___x_297_; lean_object* v___f_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_286_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
v_toMonadQuotation_287_ = lean_ctor_get(v___x_286_, 0);
v_toMonadRef_288_ = lean_ctor_get(v_toMonadQuotation_287_, 0);
v___f_289_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8));
v___x_290_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9));
v___x_291_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13);
v_toMonadFileMap_292_ = lean_ctor_get(v___x_291_, 0);
v___x_293_ = l_Lean_Meta_instMonadEnvMetaM;
v_getEnv_294_ = lean_ctor_get(v___x_293_, 0);
v_modifyEnv_295_ = lean_ctor_get(v___x_293_, 1);
lean_inc(v_modifyEnv_295_);
v___f_296_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_296_, 0, v_modifyEnv_295_);
lean_closure_set(v___f_296_, 1, v___x_290_);
lean_inc(v_getEnv_294_);
v___x_297_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_297_, 0, lean_box(0));
lean_closure_set(v___x_297_, 1, lean_box(0));
lean_closure_set(v___x_297_, 2, lean_box(0));
lean_closure_set(v___x_297_, 3, lean_box(0));
lean_closure_set(v___x_297_, 4, v_getEnv_294_);
v___f_298_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_298_, 0, v___f_296_);
lean_closure_set(v___f_298_, 1, v___f_289_);
v___x_299_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_299_, 0, lean_box(0));
lean_closure_set(v___x_299_, 1, v___x_297_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___f_298_);
v___x_301_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25);
v___x_302_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
lean_inc_ref(v_toMonadRef_288_);
v___x_303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set(v___x_303_, 1, v_toMonadRef_288_);
lean_ctor_set(v___x_303_, 2, v___x_302_);
v___x_304_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29);
switch(lean_obj_tag(v_v_214_))
{
case 0:
{
lean_object* v_val_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_320_; 
lean_dec_ref_known(v___x_300_, 2);
v_val_305_ = lean_ctor_get(v_v_214_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v_v_214_);
if (v_isSharedCheck_320_ == 0)
{
v___x_307_ = v_v_214_;
v_isShared_308_ = v_isSharedCheck_320_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_val_305_);
lean_dec(v_v_214_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_320_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v_y_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_309_ = l_Lean_TSyntax_getId(v_val_305_);
v_y_310_ = l_Lean_Name_eraseMacroScopes(v___x_309_);
lean_dec(v___x_309_);
v___x_311_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31));
v___x_312_ = lean_name_eq(v_y_310_, v___x_311_);
lean_dec(v_y_310_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_2022__overap_314_; lean_object* v___x_315_; 
lean_del_object(v___x_307_);
v___x_313_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33);
v___x_2022__overap_314_ = l_Lean_throwErrorAt___redArg(v___x_285_, v___x_303_, v_val_305_, v___x_313_);
lean_inc(v_a_220_);
lean_inc_ref(v_a_219_);
lean_inc(v_a_218_);
lean_inc_ref(v_a_217_);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
v___x_315_ = lean_apply_7(v___x_2022__overap_314_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, lean_box(0));
return v___x_315_;
}
else
{
lean_object* v___x_316_; lean_object* v___x_318_; 
lean_dec(v_val_305_);
lean_dec_ref_known(v___x_303_, 3);
lean_dec_ref(v___x_285_);
v___x_316_ = lean_box(0);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_316_);
v___x_318_ = v___x_307_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
case 1:
{
lean_object* v_val_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_2024__overap_327_; lean_object* v___x_328_; 
lean_dec_ref_known(v___x_300_, 2);
v_val_321_ = lean_ctor_get(v_v_214_, 0);
lean_inc_n(v_val_321_, 2);
lean_dec_ref_known(v_v_214_, 1);
v___x_322_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35);
v___x_323_ = l_Lean_MessageData_ofSyntax(v_val_321_);
v___x_324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_322_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37);
v___x_326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_2024__overap_327_ = l_Lean_throwErrorAt___redArg(v___x_285_, v___x_303_, v_val_321_, v___x_326_);
lean_inc(v_a_220_);
lean_inc_ref(v_a_219_);
lean_inc(v_a_218_);
lean_inc_ref(v_a_217_);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
v___x_328_ = lean_apply_7(v___x_2024__overap_327_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, lean_box(0));
return v___x_328_;
}
default: 
{
lean_object* v_val_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_381_; 
v_val_329_ = lean_ctor_get(v_v_214_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v_v_214_);
if (v_isSharedCheck_381_ == 0)
{
v___x_331_ = v_v_214_;
v_isShared_332_ = v_isSharedCheck_381_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_val_329_);
lean_dec(v_v_214_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_381_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v_toCold_333_; lean_object* v_currRecDepth_334_; lean_object* v_ref_335_; uint16_t v_optionFlags_336_; uint8_t v_suppressElabErrors_337_; uint8_t v_isRecordingDeps_338_; lean_object* v___f_339_; lean_object* v___f_340_; lean_object* v_ref_341_; lean_object* v___x_342_; lean_object* v___x_2026__overap_343_; lean_object* v___x_344_; 
v_toCold_333_ = lean_ctor_get(v_a_219_, 0);
v_currRecDepth_334_ = lean_ctor_get(v_a_219_, 1);
v_ref_335_ = lean_ctor_get(v_a_219_, 2);
v_optionFlags_336_ = lean_ctor_get_uint16(v_a_219_, sizeof(void*)*3);
v_suppressElabErrors_337_ = lean_ctor_get_uint8(v_a_219_, sizeof(void*)*3 + 2);
v_isRecordingDeps_338_ = lean_ctor_get_uint8(v_a_219_, sizeof(void*)*3 + 3);
v___f_339_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39));
v___f_340_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__41));
v_ref_341_ = l_Lean_replaceRef(v_val_329_, v_ref_335_);
lean_inc(v_currRecDepth_334_);
lean_inc_ref(v_toCold_333_);
v___x_342_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_342_, 0, v_toCold_333_);
lean_ctor_set(v___x_342_, 1, v_currRecDepth_334_);
lean_ctor_set(v___x_342_, 2, v_ref_341_);
lean_ctor_set_uint16(v___x_342_, sizeof(void*)*3, v_optionFlags_336_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*3 + 2, v_suppressElabErrors_337_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*3 + 3, v_isRecordingDeps_338_);
lean_inc_ref(v___x_303_);
lean_inc(v_toMonadFileMap_292_);
lean_inc_ref(v___x_285_);
v___x_2026__overap_343_ = l_Lean_Doc_parseQuotedStrLit___redArg(v___x_285_, v_toMonadFileMap_292_, v___x_300_, v___x_303_, v___x_291_, v___x_304_, v___f_340_, v_val_329_);
lean_inc(v_a_220_);
lean_inc(v_a_218_);
lean_inc_ref(v_a_217_);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
v___x_344_ = lean_apply_7(v___x_2026__overap_343_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v___x_342_, v_a_220_, lean_box(0));
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_372_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_372_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_372_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_372_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
lean_inc(v_a_345_);
v___x_351_ = l_Lean_Syntax_isOfKind(v_a_345_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_2029__overap_357_; lean_object* v___x_358_; 
lean_del_object(v___x_347_);
lean_del_object(v___x_331_);
v___x_352_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43);
lean_inc(v_a_345_);
v___x_353_ = l_Lean_MessageData_ofSyntax(v_a_345_);
v___x_354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_2029__overap_357_ = l_Lean_throwErrorAt___redArg(v___x_285_, v___x_303_, v_a_345_, v___x_356_);
lean_inc(v_a_220_);
lean_inc_ref(v_a_219_);
lean_inc(v_a_218_);
lean_inc_ref(v_a_217_);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
v___x_358_ = lean_apply_7(v___x_2029__overap_357_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, lean_box(0));
return v___x_358_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; size_t v_sz_363_; size_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
lean_dec_ref_known(v___x_303_, 3);
lean_dec_ref(v___x_285_);
v___x_359_ = l_Lean_Syntax_getArg(v_a_345_, v___x_349_);
lean_dec(v_a_345_);
v___x_360_ = l_Lean_Syntax_getArgs(v___x_359_);
lean_dec(v___x_359_);
v___x_361_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_360_);
lean_dec_ref(v___x_360_);
v___x_362_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__53));
v_sz_363_ = lean_array_size(v___x_361_);
v___x_364_ = ((size_t)0ULL);
v___x_365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_362_, v___f_339_, v_sz_363_, v___x_364_, v___x_361_);
if (v_isShared_332_ == 0)
{
lean_ctor_set_tag(v___x_331_, 1);
lean_ctor_set(v___x_331_, 0, v___x_365_);
v___x_367_ = v___x_331_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_371_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_369_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_367_);
v___x_369_ = v___x_347_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_del_object(v___x_331_);
lean_dec_ref_known(v___x_303_, 3);
lean_dec_ref(v___x_285_);
v_a_373_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_344_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_344_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
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
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___boxed(lean_object* v_v_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Doc_instFromDocArgDocScope___private__1(v_v_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___lam__2(lean_object* v___f_403_, lean_object* v___f_404_, lean_object* v_v_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___x_413_; lean_object* v_toApplicative_414_; lean_object* v_toFunctor_415_; lean_object* v_toSeq_416_; lean_object* v_toSeqLeft_417_; lean_object* v_toSeqRight_418_; lean_object* v___f_419_; lean_object* v___f_420_; lean_object* v___f_421_; lean_object* v___f_422_; lean_object* v___x_423_; lean_object* v___f_424_; lean_object* v___f_425_; lean_object* v___f_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v_toApplicative_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_583_; 
v___x_413_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1);
v_toApplicative_414_ = lean_ctor_get(v___x_413_, 0);
v_toFunctor_415_ = lean_ctor_get(v_toApplicative_414_, 0);
v_toSeq_416_ = lean_ctor_get(v_toApplicative_414_, 2);
v_toSeqLeft_417_ = lean_ctor_get(v_toApplicative_414_, 3);
v_toSeqRight_418_ = lean_ctor_get(v_toApplicative_414_, 4);
v___f_419_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2));
v___f_420_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3));
lean_inc_ref_n(v_toFunctor_415_, 2);
v___f_421_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_421_, 0, v_toFunctor_415_);
v___f_422_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_422_, 0, v_toFunctor_415_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___f_421_);
lean_ctor_set(v___x_423_, 1, v___f_422_);
lean_inc(v_toSeqRight_418_);
v___f_424_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_424_, 0, v_toSeqRight_418_);
lean_inc(v_toSeqLeft_417_);
v___f_425_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_425_, 0, v_toSeqLeft_417_);
lean_inc(v_toSeq_416_);
v___f_426_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_426_, 0, v_toSeq_416_);
v___x_427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_427_, 0, v___x_423_);
lean_ctor_set(v___x_427_, 1, v___f_419_);
lean_ctor_set(v___x_427_, 2, v___f_426_);
lean_ctor_set(v___x_427_, 3, v___f_425_);
lean_ctor_set(v___x_427_, 4, v___f_424_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___f_420_);
v___x_429_ = l_StateRefT_x27_instMonad___redArg(v___x_428_);
v_toApplicative_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; 
v_unused_584_ = lean_ctor_get(v___x_429_, 1);
lean_dec(v_unused_584_);
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_583_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_toApplicative_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_583_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v_toFunctor_434_; lean_object* v_toSeq_435_; lean_object* v_toSeqLeft_436_; lean_object* v_toSeqRight_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_581_; 
v_toFunctor_434_ = lean_ctor_get(v_toApplicative_430_, 0);
v_toSeq_435_ = lean_ctor_get(v_toApplicative_430_, 2);
v_toSeqLeft_436_ = lean_ctor_get(v_toApplicative_430_, 3);
v_toSeqRight_437_ = lean_ctor_get(v_toApplicative_430_, 4);
v_isSharedCheck_581_ = !lean_is_exclusive(v_toApplicative_430_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v_toApplicative_430_, 1);
lean_dec(v_unused_582_);
v___x_439_ = v_toApplicative_430_;
v_isShared_440_ = v_isSharedCheck_581_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_toSeqRight_437_);
lean_inc(v_toSeqLeft_436_);
lean_inc(v_toSeq_435_);
lean_inc(v_toFunctor_434_);
lean_dec(v_toApplicative_430_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_581_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___f_441_; lean_object* v___f_442_; lean_object* v___f_443_; lean_object* v___f_444_; lean_object* v___x_445_; lean_object* v___f_446_; lean_object* v___f_447_; lean_object* v___f_448_; lean_object* v___x_450_; 
v___f_441_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4));
v___f_442_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5));
lean_inc_ref(v_toFunctor_434_);
v___f_443_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_443_, 0, v_toFunctor_434_);
v___f_444_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_444_, 0, v_toFunctor_434_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v___f_443_);
lean_ctor_set(v___x_445_, 1, v___f_444_);
v___f_446_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_446_, 0, v_toSeqRight_437_);
v___f_447_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_447_, 0, v_toSeqLeft_436_);
v___f_448_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_448_, 0, v_toSeq_435_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 4, v___f_446_);
lean_ctor_set(v___x_439_, 3, v___f_447_);
lean_ctor_set(v___x_439_, 2, v___f_448_);
lean_ctor_set(v___x_439_, 1, v___f_441_);
lean_ctor_set(v___x_439_, 0, v___x_445_);
v___x_450_ = v___x_439_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___f_441_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v___f_448_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v___f_447_);
lean_ctor_set(v_reuseFailAlloc_580_, 4, v___f_446_);
v___x_450_ = v_reuseFailAlloc_580_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v___f_442_);
lean_ctor_set(v___x_432_, 0, v___x_450_);
v___x_452_ = v___x_432_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___f_442_);
v___x_452_ = v_reuseFailAlloc_579_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; lean_object* v_toApplicative_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_577_; 
v___x_453_ = l_StateRefT_x27_instMonad___redArg(v___x_452_);
v_toApplicative_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; 
v_unused_578_ = lean_ctor_get(v___x_453_, 1);
lean_dec(v_unused_578_);
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_577_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_toApplicative_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_577_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_toFunctor_458_; lean_object* v_toSeq_459_; lean_object* v_toSeqLeft_460_; lean_object* v_toSeqRight_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_575_; 
v_toFunctor_458_ = lean_ctor_get(v_toApplicative_454_, 0);
v_toSeq_459_ = lean_ctor_get(v_toApplicative_454_, 2);
v_toSeqLeft_460_ = lean_ctor_get(v_toApplicative_454_, 3);
v_toSeqRight_461_ = lean_ctor_get(v_toApplicative_454_, 4);
v_isSharedCheck_575_ = !lean_is_exclusive(v_toApplicative_454_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v_toApplicative_454_, 1);
lean_dec(v_unused_576_);
v___x_463_ = v_toApplicative_454_;
v_isShared_464_ = v_isSharedCheck_575_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_toSeqRight_461_);
lean_inc(v_toSeqLeft_460_);
lean_inc(v_toSeq_459_);
lean_inc(v_toFunctor_458_);
lean_dec(v_toApplicative_454_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_575_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___f_465_; lean_object* v___f_466_; lean_object* v___f_467_; lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___f_470_; lean_object* v___f_471_; lean_object* v___f_472_; lean_object* v___x_474_; 
v___f_465_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6));
v___f_466_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7));
lean_inc_ref(v_toFunctor_458_);
v___f_467_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_467_, 0, v_toFunctor_458_);
v___f_468_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_468_, 0, v_toFunctor_458_);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v___f_467_);
lean_ctor_set(v___x_469_, 1, v___f_468_);
v___f_470_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_470_, 0, v_toSeqRight_461_);
v___f_471_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_471_, 0, v_toSeqLeft_460_);
v___f_472_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_472_, 0, v_toSeq_459_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 4, v___f_470_);
lean_ctor_set(v___x_463_, 3, v___f_471_);
lean_ctor_set(v___x_463_, 2, v___f_472_);
lean_ctor_set(v___x_463_, 1, v___f_465_);
lean_ctor_set(v___x_463_, 0, v___x_469_);
v___x_474_ = v___x_463_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___f_465_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v___f_472_);
lean_ctor_set(v_reuseFailAlloc_574_, 3, v___f_471_);
lean_ctor_set(v_reuseFailAlloc_574_, 4, v___f_470_);
v___x_474_ = v_reuseFailAlloc_574_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_476_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 1, v___f_466_);
lean_ctor_set(v___x_456_, 0, v___x_474_);
v___x_476_ = v___x_456_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___f_466_);
v___x_476_ = v_reuseFailAlloc_573_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; lean_object* v_toMonadQuotation_478_; lean_object* v_toMonadRef_479_; lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v_toMonadFileMap_483_; lean_object* v___x_484_; lean_object* v_getEnv_485_; lean_object* v_modifyEnv_486_; lean_object* v___f_487_; lean_object* v___x_488_; lean_object* v___f_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_477_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
v_toMonadQuotation_478_ = lean_ctor_get(v___x_477_, 0);
v_toMonadRef_479_ = lean_ctor_get(v_toMonadQuotation_478_, 0);
v___f_480_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8));
v___x_481_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9));
v___x_482_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13);
v_toMonadFileMap_483_ = lean_ctor_get(v___x_482_, 0);
v___x_484_ = l_Lean_Meta_instMonadEnvMetaM;
v_getEnv_485_ = lean_ctor_get(v___x_484_, 0);
v_modifyEnv_486_ = lean_ctor_get(v___x_484_, 1);
lean_inc(v_modifyEnv_486_);
v___f_487_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_487_, 0, v_modifyEnv_486_);
lean_closure_set(v___f_487_, 1, v___x_481_);
lean_inc(v_getEnv_485_);
v___x_488_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_488_, 0, lean_box(0));
lean_closure_set(v___x_488_, 1, lean_box(0));
lean_closure_set(v___x_488_, 2, lean_box(0));
lean_closure_set(v___x_488_, 3, lean_box(0));
lean_closure_set(v___x_488_, 4, v_getEnv_485_);
v___f_489_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_489_, 0, v___f_487_);
lean_closure_set(v___f_489_, 1, v___f_480_);
v___x_490_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_490_, 0, lean_box(0));
lean_closure_set(v___x_490_, 1, v___x_488_);
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v___f_489_);
v___x_492_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25);
v___x_493_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
lean_inc_ref(v_toMonadRef_479_);
v___x_494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v_toMonadRef_479_);
lean_ctor_set(v___x_494_, 2, v___x_493_);
v___x_495_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29);
switch(lean_obj_tag(v_v_405_))
{
case 0:
{
lean_object* v_val_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_511_; 
lean_dec_ref_known(v___x_491_, 2);
lean_dec_ref(v___f_404_);
lean_dec_ref(v___f_403_);
v_val_496_ = lean_ctor_get(v_v_405_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v_v_405_);
if (v_isSharedCheck_511_ == 0)
{
v___x_498_ = v_v_405_;
v_isShared_499_ = v_isSharedCheck_511_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_val_496_);
lean_dec(v_v_405_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_511_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v_y_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_500_ = l_Lean_TSyntax_getId(v_val_496_);
v_y_501_ = l_Lean_Name_eraseMacroScopes(v___x_500_);
lean_dec(v___x_500_);
v___x_502_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31));
v___x_503_ = lean_name_eq(v_y_501_, v___x_502_);
lean_dec(v_y_501_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_313__overap_505_; lean_object* v___x_506_; 
lean_del_object(v___x_498_);
v___x_504_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33);
v___x_313__overap_505_ = l_Lean_throwErrorAt___redArg(v___x_476_, v___x_494_, v_val_496_, v___x_504_);
lean_inc(v___y_411_);
lean_inc_ref(v___y_410_);
lean_inc(v___y_409_);
lean_inc_ref(v___y_408_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
v___x_506_ = lean_apply_7(v___x_313__overap_505_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, lean_box(0));
return v___x_506_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_509_; 
lean_dec(v_val_496_);
lean_dec_ref_known(v___x_494_, 3);
lean_dec_ref(v___x_476_);
v___x_507_ = lean_box(0);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_507_);
v___x_509_ = v___x_498_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
case 1:
{
lean_object* v_val_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_324__overap_518_; lean_object* v___x_519_; 
lean_dec_ref_known(v___x_491_, 2);
lean_dec_ref(v___f_404_);
lean_dec_ref(v___f_403_);
v_val_512_ = lean_ctor_get(v_v_405_, 0);
lean_inc_n(v_val_512_, 2);
lean_dec_ref_known(v_v_405_, 1);
v___x_513_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35);
v___x_514_ = l_Lean_MessageData_ofSyntax(v_val_512_);
v___x_515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_324__overap_518_ = l_Lean_throwErrorAt___redArg(v___x_476_, v___x_494_, v_val_512_, v___x_517_);
lean_inc(v___y_411_);
lean_inc_ref(v___y_410_);
lean_inc(v___y_409_);
lean_inc_ref(v___y_408_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
v___x_519_ = lean_apply_7(v___x_324__overap_518_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, lean_box(0));
return v___x_519_;
}
default: 
{
lean_object* v_val_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_572_; 
v_val_520_ = lean_ctor_get(v_v_405_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v_v_405_);
if (v_isSharedCheck_572_ == 0)
{
v___x_522_ = v_v_405_;
v_isShared_523_ = v_isSharedCheck_572_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_val_520_);
lean_dec(v_v_405_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_572_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v_toCold_524_; lean_object* v_currRecDepth_525_; lean_object* v_ref_526_; uint16_t v_optionFlags_527_; uint8_t v_suppressElabErrors_528_; uint8_t v_isRecordingDeps_529_; lean_object* v___x_530_; lean_object* v___f_531_; lean_object* v_ref_532_; lean_object* v___x_533_; lean_object* v___x_329__overap_534_; lean_object* v___x_535_; 
v_toCold_524_ = lean_ctor_get(v___y_410_, 0);
v_currRecDepth_525_ = lean_ctor_get(v___y_410_, 1);
v_ref_526_ = lean_ctor_get(v___y_410_, 2);
v_optionFlags_527_ = lean_ctor_get_uint16(v___y_410_, sizeof(void*)*3);
v_suppressElabErrors_528_ = lean_ctor_get_uint8(v___y_410_, sizeof(void*)*3 + 2);
v_isRecordingDeps_529_ = lean_ctor_get_uint8(v___y_410_, sizeof(void*)*3 + 3);
v___x_530_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40));
v___f_531_ = lean_alloc_closure((void*)(l_Lean_Doc_instFromDocArgDocScope___private__1___lam__1), 4, 2);
lean_closure_set(v___f_531_, 0, v___x_530_);
lean_closure_set(v___f_531_, 1, v___f_403_);
v_ref_532_ = l_Lean_replaceRef(v_val_520_, v_ref_526_);
lean_inc(v_currRecDepth_525_);
lean_inc_ref(v_toCold_524_);
v___x_533_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_533_, 0, v_toCold_524_);
lean_ctor_set(v___x_533_, 1, v_currRecDepth_525_);
lean_ctor_set(v___x_533_, 2, v_ref_532_);
lean_ctor_set_uint16(v___x_533_, sizeof(void*)*3, v_optionFlags_527_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*3 + 2, v_suppressElabErrors_528_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*3 + 3, v_isRecordingDeps_529_);
lean_inc_ref(v___x_494_);
lean_inc(v_toMonadFileMap_483_);
lean_inc_ref(v___x_476_);
v___x_329__overap_534_ = l_Lean_Doc_parseQuotedStrLit___redArg(v___x_476_, v_toMonadFileMap_483_, v___x_491_, v___x_494_, v___x_482_, v___x_495_, v___f_531_, v_val_520_);
lean_inc(v___y_411_);
lean_inc(v___y_409_);
lean_inc_ref(v___y_408_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
v___x_535_ = lean_apply_7(v___x_329__overap_534_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___x_533_, v___y_411_, lean_box(0));
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_563_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_563_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_563_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_563_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
lean_inc(v_a_536_);
v___x_542_ = l_Lean_Syntax_isOfKind(v_a_536_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_360__overap_548_; lean_object* v___x_549_; 
lean_del_object(v___x_538_);
lean_del_object(v___x_522_);
lean_dec_ref(v___f_404_);
v___x_543_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43);
lean_inc(v_a_536_);
v___x_544_ = l_Lean_MessageData_ofSyntax(v_a_536_);
v___x_545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37);
v___x_547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_360__overap_548_ = l_Lean_throwErrorAt___redArg(v___x_476_, v___x_494_, v_a_536_, v___x_547_);
lean_inc(v___y_411_);
lean_inc_ref(v___y_410_);
lean_inc(v___y_409_);
lean_inc_ref(v___y_408_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
v___x_549_ = lean_apply_7(v___x_360__overap_548_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, lean_box(0));
return v___x_549_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; size_t v_sz_554_; size_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
lean_dec_ref_known(v___x_494_, 3);
lean_dec_ref(v___x_476_);
v___x_550_ = l_Lean_Syntax_getArg(v_a_536_, v___x_540_);
lean_dec(v_a_536_);
v___x_551_ = l_Lean_Syntax_getArgs(v___x_550_);
lean_dec(v___x_550_);
v___x_552_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_551_);
lean_dec_ref(v___x_551_);
v___x_553_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__53));
v_sz_554_ = lean_array_size(v___x_552_);
v___x_555_ = ((size_t)0ULL);
v___x_556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_553_, v___f_404_, v_sz_554_, v___x_555_, v___x_552_);
if (v_isShared_523_ == 0)
{
lean_ctor_set_tag(v___x_522_, 1);
lean_ctor_set(v___x_522_, 0, v___x_556_);
v___x_558_ = v___x_522_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_560_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_558_);
v___x_560_ = v___x_538_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_del_object(v___x_522_);
lean_dec_ref_known(v___x_494_, 3);
lean_dec_ref(v___x_476_);
lean_dec_ref(v___f_404_);
v_a_564_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_535_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_535_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
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
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___lam__2___boxed(lean_object* v___f_585_, lean_object* v___f_586_, lean_object* v_v_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Doc_instFromDocArgDocScope___lam__2(v___f_585_, v___f_586_, v_v_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
return v_res_595_;
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
