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
lean_object* v___x_219_; lean_object* v_toApplicative_220_; lean_object* v_toFunctor_221_; lean_object* v_toSeq_222_; lean_object* v_toSeqLeft_223_; lean_object* v_toSeqRight_224_; lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_toApplicative_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_399_; 
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
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; 
v_unused_400_ = lean_ctor_get(v___x_235_, 1);
lean_dec(v_unused_400_);
v___x_238_ = v___x_235_;
v_isShared_239_ = v_isSharedCheck_399_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_toApplicative_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_399_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v_toFunctor_240_; lean_object* v_toSeq_241_; lean_object* v_toSeqLeft_242_; lean_object* v_toSeqRight_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_397_; 
v_toFunctor_240_ = lean_ctor_get(v_toApplicative_236_, 0);
v_toSeq_241_ = lean_ctor_get(v_toApplicative_236_, 2);
v_toSeqLeft_242_ = lean_ctor_get(v_toApplicative_236_, 3);
v_toSeqRight_243_ = lean_ctor_get(v_toApplicative_236_, 4);
v_isSharedCheck_397_ = !lean_is_exclusive(v_toApplicative_236_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v_toApplicative_236_, 1);
lean_dec(v_unused_398_);
v___x_245_ = v_toApplicative_236_;
v_isShared_246_ = v_isSharedCheck_397_;
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
v_isShared_246_ = v_isSharedCheck_397_;
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
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___f_247_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v___f_254_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v___f_253_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v___f_252_);
v___x_256_ = v_reuseFailAlloc_396_;
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
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___f_248_);
v___x_258_ = v_reuseFailAlloc_395_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; lean_object* v_toApplicative_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_393_; 
v___x_259_ = l_StateRefT_x27_instMonad___redArg(v___x_258_);
v_toApplicative_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; 
v_unused_394_ = lean_ctor_get(v___x_259_, 1);
lean_dec(v_unused_394_);
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_393_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_toApplicative_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_393_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_toFunctor_264_; lean_object* v_toSeq_265_; lean_object* v_toSeqLeft_266_; lean_object* v_toSeqRight_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_391_; 
v_toFunctor_264_ = lean_ctor_get(v_toApplicative_260_, 0);
v_toSeq_265_ = lean_ctor_get(v_toApplicative_260_, 2);
v_toSeqLeft_266_ = lean_ctor_get(v_toApplicative_260_, 3);
v_toSeqRight_267_ = lean_ctor_get(v_toApplicative_260_, 4);
v_isSharedCheck_391_ = !lean_is_exclusive(v_toApplicative_260_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v_toApplicative_260_, 1);
lean_dec(v_unused_392_);
v___x_269_ = v_toApplicative_260_;
v_isShared_270_ = v_isSharedCheck_391_;
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
v_isShared_270_ = v_isSharedCheck_391_;
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
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v___f_271_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v___f_278_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v___f_277_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v___f_276_);
v___x_280_ = v_reuseFailAlloc_390_;
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
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___f_272_);
v___x_282_ = v_reuseFailAlloc_389_;
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
lean_dec_ref(v___x_297_);
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
v_y_306_ = lean_erase_macro_scopes(v___x_305_);
v___x_307_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27));
v___x_308_ = lean_name_eq(v_y_306_, v___x_307_);
lean_dec(v_y_306_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_2155__overap_310_; lean_object* v___x_311_; 
lean_del_object(v___x_303_);
v___x_309_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29);
v___x_2155__overap_310_ = l_Lean_throwErrorAt___redArg(v___x_282_, v___x_300_, v_val_301_, v___x_309_);
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
v___x_311_ = lean_apply_7(v___x_2155__overap_310_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, lean_box(0));
return v___x_311_;
}
else
{
lean_object* v___x_312_; lean_object* v___x_314_; 
lean_dec(v_val_301_);
lean_dec_ref(v___x_300_);
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
lean_object* v_val_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_1817__overap_323_; lean_object* v___x_324_; 
lean_dec_ref(v___x_297_);
v_val_317_ = lean_ctor_get(v_v_211_, 0);
lean_inc_n(v_val_317_, 2);
lean_dec_ref(v_v_211_);
v___x_318_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31);
v___x_319_ = l_Lean_MessageData_ofSyntax(v_val_317_);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33);
v___x_322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_1817__overap_323_ = l_Lean_throwErrorAt___redArg(v___x_282_, v___x_300_, v_val_317_, v___x_322_);
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
v___x_324_ = lean_apply_7(v___x_1817__overap_323_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, lean_box(0));
return v___x_324_;
}
default: 
{
lean_object* v_val_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_388_; 
v_val_325_ = lean_ctor_get(v_v_211_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v_v_211_);
if (v_isSharedCheck_388_ == 0)
{
v___x_327_ = v_v_211_;
v_isShared_328_ = v_isSharedCheck_388_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_val_325_);
lean_dec(v_v_211_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_388_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_fileName_329_; lean_object* v_fileMap_330_; lean_object* v_options_331_; lean_object* v_currRecDepth_332_; lean_object* v_maxRecDepth_333_; lean_object* v_ref_334_; lean_object* v_currNamespace_335_; lean_object* v_openDecls_336_; lean_object* v_initHeartbeats_337_; lean_object* v_maxHeartbeats_338_; lean_object* v_quotContext_339_; lean_object* v_currMacroScope_340_; uint8_t v_diag_341_; lean_object* v_cancelTk_x3f_342_; uint8_t v_suppressElabErrors_343_; lean_object* v_inheritedTraceOptions_344_; lean_object* v___x_345_; lean_object* v___f_346_; lean_object* v_ref_347_; lean_object* v___x_348_; lean_object* v___x_2088__overap_349_; lean_object* v___x_350_; 
v_fileName_329_ = lean_ctor_get(v_a_216_, 0);
v_fileMap_330_ = lean_ctor_get(v_a_216_, 1);
v_options_331_ = lean_ctor_get(v_a_216_, 2);
v_currRecDepth_332_ = lean_ctor_get(v_a_216_, 3);
v_maxRecDepth_333_ = lean_ctor_get(v_a_216_, 4);
v_ref_334_ = lean_ctor_get(v_a_216_, 5);
v_currNamespace_335_ = lean_ctor_get(v_a_216_, 6);
v_openDecls_336_ = lean_ctor_get(v_a_216_, 7);
v_initHeartbeats_337_ = lean_ctor_get(v_a_216_, 8);
v_maxHeartbeats_338_ = lean_ctor_get(v_a_216_, 9);
v_quotContext_339_ = lean_ctor_get(v_a_216_, 10);
v_currMacroScope_340_ = lean_ctor_get(v_a_216_, 11);
v_diag_341_ = lean_ctor_get_uint8(v_a_216_, sizeof(void*)*14);
v_cancelTk_x3f_342_ = lean_ctor_get(v_a_216_, 12);
v_suppressElabErrors_343_ = lean_ctor_get_uint8(v_a_216_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_344_ = lean_ctor_get(v_a_216_, 13);
v___x_345_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39));
v___f_346_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__41));
v_ref_347_ = l_Lean_replaceRef(v_val_325_, v_ref_334_);
lean_inc_ref(v_inheritedTraceOptions_344_);
lean_inc(v_cancelTk_x3f_342_);
lean_inc(v_currMacroScope_340_);
lean_inc(v_quotContext_339_);
lean_inc(v_maxHeartbeats_338_);
lean_inc(v_initHeartbeats_337_);
lean_inc(v_openDecls_336_);
lean_inc(v_currNamespace_335_);
lean_inc(v_maxRecDepth_333_);
lean_inc(v_currRecDepth_332_);
lean_inc_ref(v_options_331_);
lean_inc_ref(v_fileMap_330_);
lean_inc_ref(v_fileName_329_);
v___x_348_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_348_, 0, v_fileName_329_);
lean_ctor_set(v___x_348_, 1, v_fileMap_330_);
lean_ctor_set(v___x_348_, 2, v_options_331_);
lean_ctor_set(v___x_348_, 3, v_currRecDepth_332_);
lean_ctor_set(v___x_348_, 4, v_maxRecDepth_333_);
lean_ctor_set(v___x_348_, 5, v_ref_347_);
lean_ctor_set(v___x_348_, 6, v_currNamespace_335_);
lean_ctor_set(v___x_348_, 7, v_openDecls_336_);
lean_ctor_set(v___x_348_, 8, v_initHeartbeats_337_);
lean_ctor_set(v___x_348_, 9, v_maxHeartbeats_338_);
lean_ctor_set(v___x_348_, 10, v_quotContext_339_);
lean_ctor_set(v___x_348_, 11, v_currMacroScope_340_);
lean_ctor_set(v___x_348_, 12, v_cancelTk_x3f_342_);
lean_ctor_set(v___x_348_, 13, v_inheritedTraceOptions_344_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*14, v_diag_341_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*14 + 1, v_suppressElabErrors_343_);
lean_inc_ref(v___x_300_);
lean_inc(v_toMonadFileMap_289_);
lean_inc_ref(v___x_282_);
v___x_2088__overap_349_ = l_Lean_Doc_parseQuotedStrLit___redArg(v___x_282_, v_toMonadFileMap_289_, v___x_297_, v___x_300_, v___x_288_, v___x_345_, v___f_346_, v_val_325_);
lean_inc(v_a_217_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
v___x_350_ = lean_apply_7(v___x_2088__overap_349_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v___x_348_, v_a_217_, lean_box(0));
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_379_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_379_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_379_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_379_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
lean_inc(v_a_351_);
v___x_357_ = l_Lean_Syntax_isOfKind(v_a_351_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_2199__overap_363_; lean_object* v___x_364_; 
lean_del_object(v___x_353_);
lean_del_object(v___x_327_);
v___x_358_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43);
lean_inc(v_a_351_);
v___x_359_ = l_Lean_MessageData_ofSyntax(v_a_351_);
v___x_360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33);
v___x_362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_2199__overap_363_ = l_Lean_throwErrorAt___redArg(v___x_282_, v___x_300_, v_a_351_, v___x_362_);
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
lean_inc(v_a_213_);
lean_inc_ref(v_a_212_);
v___x_364_ = lean_apply_7(v___x_2199__overap_363_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, lean_box(0));
return v___x_364_;
}
else
{
lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; size_t v_sz_370_; size_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
lean_dec_ref(v___x_300_);
lean_dec_ref(v___x_282_);
v___f_365_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44));
v___x_366_ = l_Lean_Syntax_getArg(v_a_351_, v___x_355_);
lean_dec(v_a_351_);
v___x_367_ = l_Lean_Syntax_getArgs(v___x_366_);
lean_dec(v___x_366_);
v___x_368_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_367_);
lean_dec_ref(v___x_367_);
v___x_369_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__54));
v_sz_370_ = lean_array_size(v___x_368_);
v___x_371_ = ((size_t)0ULL);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_369_, v___f_365_, v_sz_370_, v___x_371_, v___x_368_);
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 1);
lean_ctor_set(v___x_327_, 0, v___x_372_);
v___x_374_ = v___x_327_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_378_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_374_);
v___x_376_ = v___x_353_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_del_object(v___x_327_);
lean_dec_ref(v___x_300_);
lean_dec_ref(v___x_282_);
v_a_380_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_350_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_350_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
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
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___private__1___boxed(lean_object* v_v_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Doc_instFromDocArgDocScope___private__1(v_v_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___lam__2(lean_object* v___f_410_, lean_object* v___f_411_, lean_object* v_v_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; lean_object* v_toApplicative_421_; lean_object* v_toFunctor_422_; lean_object* v_toSeq_423_; lean_object* v_toSeqLeft_424_; lean_object* v_toSeqRight_425_; lean_object* v___f_426_; lean_object* v___f_427_; lean_object* v___f_428_; lean_object* v___f_429_; lean_object* v___x_430_; lean_object* v___f_431_; lean_object* v___f_432_; lean_object* v___f_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_toApplicative_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_600_; 
v___x_420_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1);
v_toApplicative_421_ = lean_ctor_get(v___x_420_, 0);
v_toFunctor_422_ = lean_ctor_get(v_toApplicative_421_, 0);
v_toSeq_423_ = lean_ctor_get(v_toApplicative_421_, 2);
v_toSeqLeft_424_ = lean_ctor_get(v_toApplicative_421_, 3);
v_toSeqRight_425_ = lean_ctor_get(v_toApplicative_421_, 4);
v___f_426_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2));
v___f_427_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3));
lean_inc_ref_n(v_toFunctor_422_, 2);
v___f_428_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_428_, 0, v_toFunctor_422_);
v___f_429_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_429_, 0, v_toFunctor_422_);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___f_428_);
lean_ctor_set(v___x_430_, 1, v___f_429_);
lean_inc(v_toSeqRight_425_);
v___f_431_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_431_, 0, v_toSeqRight_425_);
lean_inc(v_toSeqLeft_424_);
v___f_432_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_432_, 0, v_toSeqLeft_424_);
lean_inc(v_toSeq_423_);
v___f_433_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_433_, 0, v_toSeq_423_);
v___x_434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_434_, 0, v___x_430_);
lean_ctor_set(v___x_434_, 1, v___f_426_);
lean_ctor_set(v___x_434_, 2, v___f_433_);
lean_ctor_set(v___x_434_, 3, v___f_432_);
lean_ctor_set(v___x_434_, 4, v___f_431_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___f_427_);
v___x_436_ = l_StateRefT_x27_instMonad___redArg(v___x_435_);
v_toApplicative_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v___x_436_, 1);
lean_dec(v_unused_601_);
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_600_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_toApplicative_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_600_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_toFunctor_441_; lean_object* v_toSeq_442_; lean_object* v_toSeqLeft_443_; lean_object* v_toSeqRight_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_598_; 
v_toFunctor_441_ = lean_ctor_get(v_toApplicative_437_, 0);
v_toSeq_442_ = lean_ctor_get(v_toApplicative_437_, 2);
v_toSeqLeft_443_ = lean_ctor_get(v_toApplicative_437_, 3);
v_toSeqRight_444_ = lean_ctor_get(v_toApplicative_437_, 4);
v_isSharedCheck_598_ = !lean_is_exclusive(v_toApplicative_437_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v_toApplicative_437_, 1);
lean_dec(v_unused_599_);
v___x_446_ = v_toApplicative_437_;
v_isShared_447_ = v_isSharedCheck_598_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_toSeqRight_444_);
lean_inc(v_toSeqLeft_443_);
lean_inc(v_toSeq_442_);
lean_inc(v_toFunctor_441_);
lean_dec(v_toApplicative_437_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_598_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___f_448_; lean_object* v___f_449_; lean_object* v___f_450_; lean_object* v___f_451_; lean_object* v___x_452_; lean_object* v___f_453_; lean_object* v___f_454_; lean_object* v___f_455_; lean_object* v___x_457_; 
v___f_448_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4));
v___f_449_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5));
lean_inc_ref(v_toFunctor_441_);
v___f_450_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_450_, 0, v_toFunctor_441_);
v___f_451_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_451_, 0, v_toFunctor_441_);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v___f_450_);
lean_ctor_set(v___x_452_, 1, v___f_451_);
v___f_453_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_453_, 0, v_toSeqRight_444_);
v___f_454_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_454_, 0, v_toSeqLeft_443_);
v___f_455_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_455_, 0, v_toSeq_442_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 4, v___f_453_);
lean_ctor_set(v___x_446_, 3, v___f_454_);
lean_ctor_set(v___x_446_, 2, v___f_455_);
lean_ctor_set(v___x_446_, 1, v___f_448_);
lean_ctor_set(v___x_446_, 0, v___x_452_);
v___x_457_ = v___x_446_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___f_448_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v___f_455_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v___f_454_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v___f_453_);
v___x_457_ = v_reuseFailAlloc_597_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___f_449_);
lean_ctor_set(v___x_439_, 0, v___x_457_);
v___x_459_ = v___x_439_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v___f_449_);
v___x_459_ = v_reuseFailAlloc_596_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_460_; lean_object* v_toApplicative_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_594_; 
v___x_460_ = l_StateRefT_x27_instMonad___redArg(v___x_459_);
v_toApplicative_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v___x_460_, 1);
lean_dec(v_unused_595_);
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_594_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_toApplicative_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_594_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v_toFunctor_465_; lean_object* v_toSeq_466_; lean_object* v_toSeqLeft_467_; lean_object* v_toSeqRight_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_592_; 
v_toFunctor_465_ = lean_ctor_get(v_toApplicative_461_, 0);
v_toSeq_466_ = lean_ctor_get(v_toApplicative_461_, 2);
v_toSeqLeft_467_ = lean_ctor_get(v_toApplicative_461_, 3);
v_toSeqRight_468_ = lean_ctor_get(v_toApplicative_461_, 4);
v_isSharedCheck_592_ = !lean_is_exclusive(v_toApplicative_461_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v_toApplicative_461_, 1);
lean_dec(v_unused_593_);
v___x_470_ = v_toApplicative_461_;
v_isShared_471_ = v_isSharedCheck_592_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_toSeqRight_468_);
lean_inc(v_toSeqLeft_467_);
lean_inc(v_toSeq_466_);
lean_inc(v_toFunctor_465_);
lean_dec(v_toApplicative_461_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_592_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___f_472_; lean_object* v___f_473_; lean_object* v___f_474_; lean_object* v___f_475_; lean_object* v___x_476_; lean_object* v___f_477_; lean_object* v___f_478_; lean_object* v___f_479_; lean_object* v___x_481_; 
v___f_472_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6));
v___f_473_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7));
lean_inc_ref(v_toFunctor_465_);
v___f_474_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_474_, 0, v_toFunctor_465_);
v___f_475_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_475_, 0, v_toFunctor_465_);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v___f_474_);
lean_ctor_set(v___x_476_, 1, v___f_475_);
v___f_477_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_477_, 0, v_toSeqRight_468_);
v___f_478_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_478_, 0, v_toSeqLeft_467_);
v___f_479_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_479_, 0, v_toSeq_466_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 4, v___f_477_);
lean_ctor_set(v___x_470_, 3, v___f_478_);
lean_ctor_set(v___x_470_, 2, v___f_479_);
lean_ctor_set(v___x_470_, 1, v___f_472_);
lean_ctor_set(v___x_470_, 0, v___x_476_);
v___x_481_ = v___x_470_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___f_472_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v___f_479_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v___f_478_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v___f_477_);
v___x_481_ = v_reuseFailAlloc_591_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_483_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v___f_473_);
lean_ctor_set(v___x_463_, 0, v___x_481_);
v___x_483_ = v___x_463_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___f_473_);
v___x_483_ = v_reuseFailAlloc_590_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; lean_object* v_toMonadQuotation_485_; lean_object* v_toMonadRef_486_; lean_object* v___f_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_toMonadFileMap_490_; lean_object* v___x_491_; lean_object* v_getEnv_492_; lean_object* v_modifyEnv_493_; lean_object* v___f_494_; lean_object* v___x_495_; lean_object* v___f_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_484_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
v_toMonadQuotation_485_ = lean_ctor_get(v___x_484_, 0);
v_toMonadRef_486_ = lean_ctor_get(v_toMonadQuotation_485_, 0);
v___f_487_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8));
v___x_488_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9));
v___x_489_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13);
v_toMonadFileMap_490_ = lean_ctor_get(v___x_489_, 0);
v___x_491_ = l_Lean_Meta_instMonadEnvMetaM;
v_getEnv_492_ = lean_ctor_get(v___x_491_, 0);
v_modifyEnv_493_ = lean_ctor_get(v___x_491_, 1);
lean_inc(v_modifyEnv_493_);
v___f_494_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_494_, 0, v_modifyEnv_493_);
lean_closure_set(v___f_494_, 1, v___x_488_);
lean_inc(v_getEnv_492_);
v___x_495_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_495_, 0, lean_box(0));
lean_closure_set(v___x_495_, 1, lean_box(0));
lean_closure_set(v___x_495_, 2, lean_box(0));
lean_closure_set(v___x_495_, 3, lean_box(0));
lean_closure_set(v___x_495_, 4, v_getEnv_492_);
v___f_496_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_496_, 0, v___f_494_);
lean_closure_set(v___f_496_, 1, v___f_487_);
v___x_497_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_497_, 0, lean_box(0));
lean_closure_set(v___x_497_, 1, v___x_495_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v___f_496_);
v___x_499_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25);
v___x_500_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
lean_inc_ref(v_toMonadRef_486_);
v___x_501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v_toMonadRef_486_);
lean_ctor_set(v___x_501_, 2, v___x_500_);
switch(lean_obj_tag(v_v_412_))
{
case 0:
{
lean_object* v_val_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v___x_498_);
lean_dec_ref(v___f_411_);
lean_dec_ref(v___f_410_);
v_val_502_ = lean_ctor_get(v_v_412_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v_v_412_);
if (v_isSharedCheck_517_ == 0)
{
v___x_504_ = v_v_412_;
v_isShared_505_ = v_isSharedCheck_517_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_val_502_);
lean_dec(v_v_412_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_517_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v_y_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_506_ = l_Lean_TSyntax_getId(v_val_502_);
v_y_507_ = lean_erase_macro_scopes(v___x_506_);
v___x_508_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27));
v___x_509_ = lean_name_eq(v_y_507_, v___x_508_);
lean_dec(v_y_507_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_306__overap_511_; lean_object* v___x_512_; 
lean_del_object(v___x_504_);
v___x_510_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29);
v___x_306__overap_511_ = l_Lean_throwErrorAt___redArg(v___x_483_, v___x_501_, v_val_502_, v___x_510_);
lean_inc(v___y_418_);
lean_inc_ref(v___y_417_);
lean_inc(v___y_416_);
lean_inc_ref(v___y_415_);
lean_inc(v___y_414_);
lean_inc_ref(v___y_413_);
v___x_512_ = lean_apply_7(v___x_306__overap_511_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, lean_box(0));
return v___x_512_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_515_; 
lean_dec(v_val_502_);
lean_dec_ref(v___x_501_);
lean_dec_ref(v___x_483_);
v___x_513_ = lean_box(0);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_513_);
v___x_515_ = v___x_504_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
case 1:
{
lean_object* v_val_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_317__overap_524_; lean_object* v___x_525_; 
lean_dec_ref(v___x_498_);
lean_dec_ref(v___f_411_);
lean_dec_ref(v___f_410_);
v_val_518_ = lean_ctor_get(v_v_412_, 0);
lean_inc_n(v_val_518_, 2);
lean_dec_ref(v_v_412_);
v___x_519_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31);
v___x_520_ = l_Lean_MessageData_ofSyntax(v_val_518_);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_317__overap_524_ = l_Lean_throwErrorAt___redArg(v___x_483_, v___x_501_, v_val_518_, v___x_523_);
lean_inc(v___y_418_);
lean_inc_ref(v___y_417_);
lean_inc(v___y_416_);
lean_inc_ref(v___y_415_);
lean_inc(v___y_414_);
lean_inc_ref(v___y_413_);
v___x_525_ = lean_apply_7(v___x_317__overap_524_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, lean_box(0));
return v___x_525_;
}
default: 
{
lean_object* v_val_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_589_; 
v_val_526_ = lean_ctor_get(v_v_412_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v_v_412_);
if (v_isSharedCheck_589_ == 0)
{
v___x_528_ = v_v_412_;
v_isShared_529_ = v_isSharedCheck_589_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_val_526_);
lean_dec(v_v_412_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_589_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_fileName_530_; lean_object* v_fileMap_531_; lean_object* v_options_532_; lean_object* v_currRecDepth_533_; lean_object* v_maxRecDepth_534_; lean_object* v_ref_535_; lean_object* v_currNamespace_536_; lean_object* v_openDecls_537_; lean_object* v_initHeartbeats_538_; lean_object* v_maxHeartbeats_539_; lean_object* v_quotContext_540_; lean_object* v_currMacroScope_541_; uint8_t v_diag_542_; lean_object* v_cancelTk_x3f_543_; uint8_t v_suppressElabErrors_544_; lean_object* v_inheritedTraceOptions_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___f_548_; lean_object* v_ref_549_; lean_object* v___x_550_; lean_object* v___x_327__overap_551_; lean_object* v___x_552_; 
v_fileName_530_ = lean_ctor_get(v___y_417_, 0);
v_fileMap_531_ = lean_ctor_get(v___y_417_, 1);
v_options_532_ = lean_ctor_get(v___y_417_, 2);
v_currRecDepth_533_ = lean_ctor_get(v___y_417_, 3);
v_maxRecDepth_534_ = lean_ctor_get(v___y_417_, 4);
v_ref_535_ = lean_ctor_get(v___y_417_, 5);
v_currNamespace_536_ = lean_ctor_get(v___y_417_, 6);
v_openDecls_537_ = lean_ctor_get(v___y_417_, 7);
v_initHeartbeats_538_ = lean_ctor_get(v___y_417_, 8);
v_maxHeartbeats_539_ = lean_ctor_get(v___y_417_, 9);
v_quotContext_540_ = lean_ctor_get(v___y_417_, 10);
v_currMacroScope_541_ = lean_ctor_get(v___y_417_, 11);
v_diag_542_ = lean_ctor_get_uint8(v___y_417_, sizeof(void*)*14);
v_cancelTk_x3f_543_ = lean_ctor_get(v___y_417_, 12);
v_suppressElabErrors_544_ = lean_ctor_get_uint8(v___y_417_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_545_ = lean_ctor_get(v___y_417_, 13);
v___x_546_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39));
v___x_547_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40));
v___f_548_ = lean_alloc_closure((void*)(l_Lean_Doc_instFromDocArgDocScope___private__1___lam__1), 4, 2);
lean_closure_set(v___f_548_, 0, v___x_547_);
lean_closure_set(v___f_548_, 1, v___f_410_);
v_ref_549_ = l_Lean_replaceRef(v_val_526_, v_ref_535_);
lean_inc_ref(v_inheritedTraceOptions_545_);
lean_inc(v_cancelTk_x3f_543_);
lean_inc(v_currMacroScope_541_);
lean_inc(v_quotContext_540_);
lean_inc(v_maxHeartbeats_539_);
lean_inc(v_initHeartbeats_538_);
lean_inc(v_openDecls_537_);
lean_inc(v_currNamespace_536_);
lean_inc(v_maxRecDepth_534_);
lean_inc(v_currRecDepth_533_);
lean_inc_ref(v_options_532_);
lean_inc_ref(v_fileMap_531_);
lean_inc_ref(v_fileName_530_);
v___x_550_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_550_, 0, v_fileName_530_);
lean_ctor_set(v___x_550_, 1, v_fileMap_531_);
lean_ctor_set(v___x_550_, 2, v_options_532_);
lean_ctor_set(v___x_550_, 3, v_currRecDepth_533_);
lean_ctor_set(v___x_550_, 4, v_maxRecDepth_534_);
lean_ctor_set(v___x_550_, 5, v_ref_549_);
lean_ctor_set(v___x_550_, 6, v_currNamespace_536_);
lean_ctor_set(v___x_550_, 7, v_openDecls_537_);
lean_ctor_set(v___x_550_, 8, v_initHeartbeats_538_);
lean_ctor_set(v___x_550_, 9, v_maxHeartbeats_539_);
lean_ctor_set(v___x_550_, 10, v_quotContext_540_);
lean_ctor_set(v___x_550_, 11, v_currMacroScope_541_);
lean_ctor_set(v___x_550_, 12, v_cancelTk_x3f_543_);
lean_ctor_set(v___x_550_, 13, v_inheritedTraceOptions_545_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*14, v_diag_542_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*14 + 1, v_suppressElabErrors_544_);
lean_inc_ref(v___x_501_);
lean_inc(v_toMonadFileMap_490_);
lean_inc_ref(v___x_483_);
v___x_327__overap_551_ = l_Lean_Doc_parseQuotedStrLit___redArg(v___x_483_, v_toMonadFileMap_490_, v___x_498_, v___x_501_, v___x_489_, v___x_546_, v___f_548_, v_val_526_);
lean_inc(v___y_418_);
lean_inc(v___y_416_);
lean_inc_ref(v___y_415_);
lean_inc(v___y_414_);
lean_inc_ref(v___y_413_);
v___x_552_ = lean_apply_7(v___x_327__overap_551_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___x_550_, v___y_418_, lean_box(0));
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_580_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_580_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_580_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_580_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17));
lean_inc(v_a_553_);
v___x_559_ = l_Lean_Syntax_isOfKind(v_a_553_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_358__overap_565_; lean_object* v___x_566_; 
lean_del_object(v___x_555_);
lean_del_object(v___x_528_);
lean_dec_ref(v___f_411_);
v___x_560_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43);
lean_inc(v_a_553_);
v___x_561_ = l_Lean_MessageData_ofSyntax(v_a_553_);
v___x_562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_560_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = lean_obj_once(&l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33, &l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once, _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33);
v___x_564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_358__overap_565_ = l_Lean_throwErrorAt___redArg(v___x_483_, v___x_501_, v_a_553_, v___x_564_);
lean_inc(v___y_418_);
lean_inc_ref(v___y_417_);
lean_inc(v___y_416_);
lean_inc_ref(v___y_415_);
lean_inc(v___y_414_);
lean_inc_ref(v___y_413_);
v___x_566_ = lean_apply_7(v___x_358__overap_565_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, lean_box(0));
return v___x_566_;
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; size_t v_sz_571_; size_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
lean_dec_ref(v___x_501_);
lean_dec_ref(v___x_483_);
v___x_567_ = l_Lean_Syntax_getArg(v_a_553_, v___x_557_);
lean_dec(v_a_553_);
v___x_568_ = l_Lean_Syntax_getArgs(v___x_567_);
lean_dec(v___x_567_);
v___x_569_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_568_);
lean_dec_ref(v___x_568_);
v___x_570_ = ((lean_object*)(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__54));
v_sz_571_ = lean_array_size(v___x_569_);
v___x_572_ = ((size_t)0ULL);
v___x_573_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_570_, v___f_411_, v_sz_571_, v___x_572_, v___x_569_);
if (v_isShared_529_ == 0)
{
lean_ctor_set_tag(v___x_528_, 1);
lean_ctor_set(v___x_528_, 0, v___x_573_);
v___x_575_ = v___x_528_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_579_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_577_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_575_);
v___x_577_ = v___x_555_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_del_object(v___x_528_);
lean_dec_ref(v___x_501_);
lean_dec_ref(v___x_483_);
lean_dec_ref(v___f_411_);
v_a_581_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_552_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_552_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
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
LEAN_EXPORT lean_object* l_Lean_Doc_instFromDocArgDocScope___lam__2___boxed(lean_object* v___f_602_, lean_object* v___f_603_, lean_object* v_v_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_Doc_instFromDocArgDocScope___lam__2(v___f_602_, v___f_603_, v_v_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
return v_res_612_;
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
