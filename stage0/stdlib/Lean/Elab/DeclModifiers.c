// Lean compiler output
// Module: Lean.Elab.DeclModifiers
// Imports: public import Lean.DocString.Add public import Lean.Linter.Init meta import Lean.Parser.Command
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t lean_is_reserved_name(lean_object*, lean_object*);
lean_object* l_Lean_withEnv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Elab_elabDeclAttrs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Linter_logLintIf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "redundantVisibility"};
static const lean_object* l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 183, 142, 94, 198, 206, 172, 100)}};
static const lean_object* l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "warn on redundant `private`/`public` visibility modifiers"};
static const lean_object* l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__4_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__4_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__4_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(219, 182, 224, 198, 198, 122, 225, 30)}};
static const lean_ctor_object l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(255, 159, 36, 111, 164, 106, 106, 218)}};
static const lean_object* l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_linter_redundantVisibility;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "a non-private declaration `"};
static const lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1;
static const lean_string_object l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2_value;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "a private declaration `"};
static const lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__0 = (const lean_object*)&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__0 = (const lean_object*)&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1;
static const lean_string_object l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "` is a reserved name"};
static const lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__2 = (const lean_object*)&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__2_value;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "private declaration `"};
static const lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__0 = (const lean_object*)&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedVisibility_default;
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedVisibility;
static const lean_string_object l_Lean_Elab_instToStringVisibility___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l_Lean_Elab_instToStringVisibility___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_instToStringVisibility___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_instToStringVisibility___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l_Lean_Elab_instToStringVisibility___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_instToStringVisibility___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_instToStringVisibility___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l_Lean_Elab_instToStringVisibility___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_instToStringVisibility___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_instToStringVisibility___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instToStringVisibility___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToStringVisibility___closed__0 = (const lean_object*)&l_Lean_Elab_instToStringVisibility___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instToStringVisibility = (const lean_object*)&l_Lean_Elab_instToStringVisibility___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPrivate(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPrivate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPublic(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPublic___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isInferredPublic(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isInferredPublic___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "; the modifier has no effect"};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1;
static const lean_string_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "`public` is the default visibility"};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__2_value;
static lean_once_cell_t l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3;
static const lean_string_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4_value;
static const lean_string_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = " inside a `public section`"};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__5_value;
static const lean_string_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6_value;
static const lean_string_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7_value;
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_instToStringVisibility___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(213, 248, 16, 228, 25, 227, 72, 143)}};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value;
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_instToStringVisibility___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 134, 241, 204, 211, 206, 124, 144)}};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value;
static const lean_string_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unexpected visibility modifier"};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___closed__10 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__10_value;
static lean_once_cell_t l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11;
static const lean_string_object l_Lean_Elab_elabVisibility___redArg___lam__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "`private` has no effect in a `module` file outside `public section`; declarations are already `private` by default"};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___closed__12 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__12_value;
static lean_once_cell_t l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedRecKind_default;
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedRecKind;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedComputeKind_default;
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedComputeKind;
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqComputeKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqComputeKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instBEqComputeKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instBEqComputeKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instBEqComputeKind___closed__0 = (const lean_object*)&l_Lean_Elab_instBEqComputeKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instBEqComputeKind = (const lean_object*)&l_Lean_Elab_instBEqComputeKind___closed__0_value;
static const lean_string_object l_Lean_Elab_instReprComputeKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Elab.ComputeKind.regular"};
static const lean_object* l_Lean_Elab_instReprComputeKind_repr___closed__0 = (const lean_object*)&l_Lean_Elab_instReprComputeKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_Elab_instReprComputeKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instReprComputeKind_repr___closed__0_value)}};
static const lean_object* l_Lean_Elab_instReprComputeKind_repr___closed__1 = (const lean_object*)&l_Lean_Elab_instReprComputeKind_repr___closed__1_value;
static const lean_string_object l_Lean_Elab_instReprComputeKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Elab.ComputeKind.meta"};
static const lean_object* l_Lean_Elab_instReprComputeKind_repr___closed__2 = (const lean_object*)&l_Lean_Elab_instReprComputeKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_Elab_instReprComputeKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instReprComputeKind_repr___closed__2_value)}};
static const lean_object* l_Lean_Elab_instReprComputeKind_repr___closed__3 = (const lean_object*)&l_Lean_Elab_instReprComputeKind_repr___closed__3_value;
static const lean_string_object l_Lean_Elab_instReprComputeKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Elab.ComputeKind.noncomputable"};
static const lean_object* l_Lean_Elab_instReprComputeKind_repr___closed__4 = (const lean_object*)&l_Lean_Elab_instReprComputeKind_repr___closed__4_value;
static const lean_ctor_object l_Lean_Elab_instReprComputeKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instReprComputeKind_repr___closed__4_value)}};
static const lean_object* l_Lean_Elab_instReprComputeKind_repr___closed__5 = (const lean_object*)&l_Lean_Elab_instReprComputeKind_repr___closed__5_value;
static lean_once_cell_t l_Lean_Elab_instReprComputeKind_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instReprComputeKind_repr___closed__6;
static lean_once_cell_t l_Lean_Elab_instReprComputeKind_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instReprComputeKind_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_instReprComputeKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instReprComputeKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instReprComputeKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instReprComputeKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instReprComputeKind___closed__0 = (const lean_object*)&l_Lean_Elab_instReprComputeKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instReprComputeKind = (const lean_object*)&l_Lean_Elab_instReprComputeKind___closed__0_value;
static const lean_array_object l_Lean_Elab_instInhabitedModifiers_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_instInhabitedModifiers_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedModifiers_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_instInhabitedModifiers_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instInhabitedModifiers_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 2, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_instInhabitedModifiers_default___closed__1 = (const lean_object*)&l_Lean_Elab_instInhabitedModifiers_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedModifiers_default = (const lean_object*)&l_Lean_Elab_instInhabitedModifiers_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedModifiers = (const lean_object*)&l_Lean_Elab_instInhabitedModifiers_default___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPrivate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPublic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPublic___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isInferredPublic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isInferredPublic___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPartial___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNonrec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNonrec___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isMeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isMeta___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNoncomputable(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNoncomputable___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addFirstAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_anyAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_anyAttr___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_instToFormatModifiers___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__2;
static lean_once_cell_t l_Lean_Elab_instToFormatModifiers___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__3;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__0___closed__1_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "local "};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__0___closed__6_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "scoped "};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__0(lean_object*);
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__3_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Elab_instToFormatModifiers___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__5;
static lean_once_cell_t l_Lean_Elab_instToFormatModifiers___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__6;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__0_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__4_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__8_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unsafe"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__9_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__9_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__11_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__12_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__12_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__13_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__14 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__14_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "nonrec"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__15 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__15_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__15_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__16 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__16_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__17 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__17_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__18 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__18_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__18_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__19 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__19_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__20 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__20_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "noncomputable"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__21 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__21_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__21_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__22 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__22_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__23 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__23_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "protected"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__24 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__24_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__24_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__25 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__25_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__26 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__26_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToStringVisibility___lam__0___closed__1_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__27 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__27_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__28 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__28_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToStringVisibility___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__29 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__29_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__30 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__30_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "/--"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__31 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__31_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__31_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__32 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__32_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-/"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__33 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__33_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__33_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__34 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__34_value;
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instToFormatModifiers___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instToFormatModifiers___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToFormatModifiers___closed__0 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___closed__0_value;
static const lean_closure_object l_Lean_Elab_instToFormatModifiers___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToFormatFormat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToFormatModifiers___closed__1 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___closed__1_value;
static const lean_closure_object l_Lean_Elab_instToFormatModifiers___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instToFormatModifiers___lam__1, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___closed__0_value),((lean_object*)&l_Lean_Elab_instToFormatModifiers___closed__1_value)} };
static const lean_object* l_Lean_Elab_instToFormatModifiers___closed__2 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instToFormatModifiers = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_instToStringModifiers___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instToStringModifiers___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToStringModifiers___closed__0 = (const lean_object*)&l_Lean_Elab_instToStringModifiers___closed__0_value;
static const lean_closure_object l_Lean_Elab_instToStringModifiers___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instToStringModifiers___closed__0_value),((lean_object*)&l_Lean_Elab_instToFormatModifiers___closed__2_value)} };
static const lean_object* l_Lean_Elab_instToStringModifiers___closed__1 = (const lean_object*)&l_Lean_Elab_instToStringModifiers___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instToStringModifiers = (const lean_object*)&l_Lean_Elab_instToStringModifiers___closed__1_value;
static const lean_string_object l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3___boxed(lean_object**);
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l_Lean_Elab_elabModifiers___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(124, 247, 59, 43, 44, 177, 111, 66)}};
static const lean_object* l_Lean_Elab_elabModifiers___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid declaration name `"};
static const lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1;
static const lean_string_object l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "`, structure `"};
static const lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3;
static const lean_string_object l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "` has field `"};
static const lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4_value;
static lean_once_cell_t l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "protected declarations must be in a namespace"};
static const lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_mkDeclName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l_Lean_Elab_mkDeclName___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_mkDeclName___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_mkDeclName___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_mkDeclName___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 175, 53, 50, 212, 152, 178, 8)}};
static const lean_object* l_Lean_Elab_mkDeclName___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_mkDeclName___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_mkDeclName___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "invalid declaration name `_root_`, `_root_` is a prefix used to refer to the 'root' namespace"};
static const lean_object* l_Lean_Elab_mkDeclName___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_mkDeclName___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_mkDeclName___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkDeclName___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_expandDeclIdCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_expandDeclIdCore___closed__0 = (const lean_object*)&l_Lean_Elab_expandDeclIdCore___closed__0_value;
static const lean_string_object l_Lean_Elab_expandDeclIdCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_expandDeclIdCore___closed__1 = (const lean_object*)&l_Lean_Elab_expandDeclIdCore___closed__1_value;
static const lean_ctor_object l_Lean_Elab_expandDeclIdCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_expandDeclIdCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_expandDeclIdCore___closed__2 = (const lean_object*)&l_Lean_Elab_expandDeclIdCore___closed__2_value;
static const lean_ctor_object l_Lean_Elab_expandDeclIdCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_expandDeclIdCore___closed__2_value),((lean_object*)&l_Lean_Elab_expandDeclIdCore___closed__0_value)}};
static const lean_object* l_Lean_Elab_expandDeclIdCore___closed__3 = (const lean_object*)&l_Lean_Elab_expandDeclIdCore___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0___boxed, .m_arity = 9, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0 = (const lean_object*)&l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_expandDeclId_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "a universe level named `"};
static const lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "deprecated"};
static const lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 182, 79, 155, 204, 118, 39, 140)}};
static const lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__1(lean_object*);
static const lean_closure_object l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__1_value;
static const lean_closure_object l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__2_value;
static const lean_closure_object l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__4_value;
static const lean_closure_object l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__5_value;
static const lean_closure_object l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__0_value),((lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__1_value)}};
static const lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__7_value),((lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__2_value),((lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__3_value),((lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__4_value),((lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__5_value)}};
static const lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__8_value),((lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__6_value)}};
static const lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9_value;
static const lean_closure_object l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10_value;
static const lean_closure_object l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = ((lean_object*)(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_));
v___x_52_ = ((lean_object*)(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__4_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_));
v___x_53_ = ((lean_object*)(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_));
v___x_54_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0(v___x_51_, v___x_52_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4____boxed(lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_();
return v_res_56_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_57_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_unsigned_to_nat(32u);
v___x_61_ = lean_mk_empty_array_with_capacity(v___x_60_);
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3(void){
_start:
{
size_t v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_63_ = ((size_t)5ULL);
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_unsigned_to_nat(32u);
v___x_66_ = lean_mk_empty_array_with_capacity(v___x_65_);
v___x_67_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2);
v___x_68_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v___x_66_);
lean_ctor_set(v___x_68_, 2, v___x_64_);
lean_ctor_set(v___x_68_, 3, v___x_64_);
lean_ctor_set_usize(v___x_68_, 4, v___x_63_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_69_ = lean_box(1);
v___x_70_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3);
v___x_71_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1);
v___x_72_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
lean_ctor_set(v___x_72_, 2, v___x_69_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(lean_object* v_____do__lift_73_, uint8_t v___x_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_____do__lift_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_78_ = lean_box(0);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v_____do__lift_73_);
v___x_80_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4);
v___x_81_ = lean_box(0);
v___x_82_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_82_, 0, v___x_79_);
lean_ctor_set(v___x_82_, 1, v___x_80_);
lean_ctor_set(v___x_82_, 2, v___x_81_);
lean_ctor_set(v___x_82_, 3, v_____do__lift_77_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*4, v___x_74_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*4 + 1, v___x_74_);
v___x_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
v___x_84_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_75_, v_inst_76_, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___boxed(lean_object* v_____do__lift_85_, lean_object* v___x_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_____do__lift_89_){
_start:
{
uint8_t v___x_678__boxed_90_; lean_object* v_res_91_; 
v___x_678__boxed_90_ = lean_unbox(v___x_86_);
v_res_91_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(v_____do__lift_85_, v___x_678__boxed_90_, v_inst_87_, v_inst_88_, v_____do__lift_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(uint8_t v___x_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_declName_97_, lean_object* v_toBind_98_, lean_object* v_____do__lift_99_){
_start:
{
lean_object* v___x_100_; lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = lean_box(v___x_92_);
lean_inc_ref(v_inst_93_);
v___f_101_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_101_, 0, v_____do__lift_99_);
lean_closure_set(v___f_101_, 1, v___x_100_);
lean_closure_set(v___f_101_, 2, v_inst_93_);
lean_closure_set(v___f_101_, 3, v_inst_94_);
v___x_102_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_93_, v_inst_95_, v_inst_96_, v_declName_97_);
v___x_103_ = lean_apply_4(v_toBind_98_, lean_box(0), lean_box(0), v___x_102_, v___f_101_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1___boxed(lean_object* v___x_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_declName_109_, lean_object* v_toBind_110_, lean_object* v_____do__lift_111_){
_start:
{
uint8_t v___x_722__boxed_112_; lean_object* v_res_113_; 
v___x_722__boxed_112_ = lean_unbox(v___x_104_);
v_res_113_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(v___x_722__boxed_112_, v_inst_105_, v_inst_106_, v_inst_107_, v_inst_108_, v_declName_109_, v_toBind_110_, v_____do__lift_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(lean_object* v_toMonadRef_114_, uint8_t v___x_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_toBind_120_, lean_object* v_declName_121_){
_start:
{
lean_object* v_getRef_122_; lean_object* v___x_123_; lean_object* v___f_124_; lean_object* v___x_125_; 
v_getRef_122_ = lean_ctor_get(v_toMonadRef_114_, 0);
lean_inc(v_getRef_122_);
lean_dec_ref(v_toMonadRef_114_);
v___x_123_ = lean_box(v___x_115_);
lean_inc(v_toBind_120_);
v___f_124_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_124_, 0, v___x_123_);
lean_closure_set(v___f_124_, 1, v_inst_116_);
lean_closure_set(v___f_124_, 2, v_inst_117_);
lean_closure_set(v___f_124_, 3, v_inst_118_);
lean_closure_set(v___f_124_, 4, v_inst_119_);
lean_closure_set(v___f_124_, 5, v_declName_121_);
lean_closure_set(v___f_124_, 6, v_toBind_120_);
v___x_125_ = lean_apply_4(v_toBind_120_, lean_box(0), lean_box(0), v_getRef_122_, v___f_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2___boxed(lean_object* v_toMonadRef_126_, lean_object* v___x_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_toBind_132_, lean_object* v_declName_133_){
_start:
{
uint8_t v___x_748__boxed_134_; lean_object* v_res_135_; 
v___x_748__boxed_134_ = lean_unbox(v___x_127_);
v_res_135_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(v_toMonadRef_126_, v___x_748__boxed_134_, v_inst_128_, v_inst_129_, v_inst_130_, v_inst_131_, v_toBind_132_, v_declName_133_);
return v_res_135_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0));
v___x_138_ = l_Lean_stringToMessageData(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2));
v___x_141_ = l_Lean_stringToMessageData(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(lean_object* v_val_142_, uint8_t v___x_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_____r_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_147_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
v___x_148_ = l_Lean_MessageData_ofConstName(v_val_142_, v___x_143_);
v___x_149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = l_Lean_throwError___redArg(v_inst_144_, v_inst_145_, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___boxed(lean_object* v_val_153_, lean_object* v___x_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_____r_157_){
_start:
{
uint8_t v___x_782__boxed_158_; lean_object* v_res_159_; 
v___x_782__boxed_158_ = lean_unbox(v___x_154_);
v_res_159_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(v_val_153_, v___x_782__boxed_158_, v_inst_155_, v_inst_156_, v_____r_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__4(lean_object* v_declName_160_, lean_object* v_toPure_161_, lean_object* v_env_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_addInfo_165_, lean_object* v_toBind_166_, lean_object* v_____r_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_privateToUserName_x3f(v_declName_160_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec(v_toBind_166_);
lean_dec(v_addInfo_165_);
lean_dec_ref(v_inst_164_);
lean_dec_ref(v_inst_163_);
lean_dec_ref(v_env_162_);
v___x_169_ = lean_box(0);
v___x_170_ = lean_apply_2(v_toPure_161_, lean_box(0), v___x_169_);
return v___x_170_;
}
else
{
lean_object* v_val_171_; uint8_t v___x_172_; uint8_t v___x_173_; 
v_val_171_ = lean_ctor_get(v___x_168_, 0);
lean_inc_n(v_val_171_, 2);
lean_dec_ref_known(v___x_168_, 1);
v___x_172_ = 1;
v___x_173_ = l_Lean_Environment_contains(v_env_162_, v_val_171_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v_val_171_);
lean_dec(v_toBind_166_);
lean_dec(v_addInfo_165_);
lean_dec_ref(v_inst_164_);
lean_dec_ref(v_inst_163_);
v___x_174_ = lean_box(0);
v___x_175_ = lean_apply_2(v_toPure_161_, lean_box(0), v___x_174_);
return v___x_175_;
}
else
{
lean_object* v___x_176_; lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_toPure_161_);
v___x_176_ = lean_box(v___x_172_);
lean_inc(v_val_171_);
v___f_177_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_177_, 0, v_val_171_);
lean_closure_set(v___f_177_, 1, v___x_176_);
lean_closure_set(v___f_177_, 2, v_inst_163_);
lean_closure_set(v___f_177_, 3, v_inst_164_);
v___x_178_ = lean_apply_1(v_addInfo_165_, v_val_171_);
v___x_179_ = lean_apply_4(v_toBind_166_, lean_box(0), lean_box(0), v___x_178_, v___f_177_);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5(lean_object* v___f_180_, lean_object* v_____r_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_apply_1(v___f_180_, v_____r_181_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__0));
v___x_185_ = l_Lean_stringToMessageData(v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(lean_object* v_declName_186_, uint8_t v___x_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_toBind_190_, lean_object* v___f_191_, lean_object* v_____r_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_193_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1);
v___x_194_ = l_Lean_MessageData_ofConstName(v_declName_186_, v___x_187_);
v___x_195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = l_Lean_throwError___redArg(v_inst_188_, v_inst_189_, v___x_197_);
v___x_199_ = lean_apply_4(v_toBind_190_, lean_box(0), lean_box(0), v___x_198_, v___f_191_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___boxed(lean_object* v_declName_200_, lean_object* v___x_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_toBind_204_, lean_object* v___f_205_, lean_object* v_____r_206_){
_start:
{
uint8_t v___x_859__boxed_207_; lean_object* v_res_208_; 
v___x_859__boxed_207_ = lean_unbox(v___x_201_);
v_res_208_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(v_declName_200_, v___x_859__boxed_207_, v_inst_202_, v_inst_203_, v_toBind_204_, v___f_205_, v_____r_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7(lean_object* v_env_209_, lean_object* v_declName_210_, lean_object* v___f_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_toBind_214_, lean_object* v___f_215_, lean_object* v_addInfo_216_, lean_object* v_____r_217_){
_start:
{
lean_object* v___x_218_; uint8_t v___x_219_; uint8_t v___x_220_; 
lean_inc(v_declName_210_);
v___x_218_ = l_Lean_mkPrivateName(v_env_209_, v_declName_210_);
v___x_219_ = 1;
lean_inc(v___x_218_);
v___x_220_ = l_Lean_Environment_contains(v_env_209_, v___x_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v___x_218_);
lean_dec(v_addInfo_216_);
lean_dec(v___f_215_);
lean_dec(v_toBind_214_);
lean_dec_ref(v_inst_213_);
lean_dec_ref(v_inst_212_);
lean_dec(v_declName_210_);
v___x_221_ = lean_box(0);
v___x_222_ = lean_apply_1(v___f_211_, v___x_221_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec(v___f_211_);
v___x_223_ = lean_box(v___x_219_);
lean_inc(v_toBind_214_);
v___f_224_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___boxed), 7, 6);
lean_closure_set(v___f_224_, 0, v_declName_210_);
lean_closure_set(v___f_224_, 1, v___x_223_);
lean_closure_set(v___f_224_, 2, v_inst_212_);
lean_closure_set(v___f_224_, 3, v_inst_213_);
lean_closure_set(v___f_224_, 4, v_toBind_214_);
lean_closure_set(v___f_224_, 5, v___f_215_);
v___x_225_ = lean_apply_1(v_addInfo_216_, v___x_218_);
v___x_226_ = lean_apply_4(v_toBind_214_, lean_box(0), lean_box(0), v___x_225_, v___f_224_);
return v___x_226_;
}
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__0));
v___x_229_ = l_Lean_stringToMessageData(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__2));
v___x_232_ = l_Lean_stringToMessageData(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(lean_object* v___f_233_, lean_object* v_declName_234_, uint8_t v___x_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_toBind_238_, lean_object* v___f_239_, lean_object* v_env_240_, lean_object* v_____do__lift_241_){
_start:
{
uint8_t v___y_243_; lean_object* v___x_253_; uint8_t v___x_254_; 
lean_inc(v_declName_234_);
v___x_253_ = l_Lean_privateToUserName(v_declName_234_);
lean_inc_ref(v_env_240_);
v___x_254_ = lean_is_reserved_name(v_env_240_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; uint8_t v___x_256_; 
lean_inc(v_declName_234_);
v___x_255_ = l_Lean_mkPrivateName(v_____do__lift_241_, v_declName_234_);
v___x_256_ = lean_is_reserved_name(v_env_240_, v___x_255_);
v___y_243_ = v___x_256_;
goto v___jp_242_;
}
else
{
lean_dec_ref(v_env_240_);
v___y_243_ = v___x_254_;
goto v___jp_242_;
}
v___jp_242_:
{
if (v___y_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v___f_239_);
lean_dec(v_toBind_238_);
lean_dec_ref(v_inst_237_);
lean_dec_ref(v_inst_236_);
lean_dec(v_declName_234_);
v___x_244_ = lean_box(0);
v___x_245_ = lean_apply_1(v___f_233_, v___x_244_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v___f_233_);
v___x_246_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_247_ = l_Lean_MessageData_ofConstName(v_declName_234_, v___x_235_);
v___x_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3);
v___x_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = l_Lean_throwError___redArg(v_inst_236_, v_inst_237_, v___x_250_);
v___x_252_ = lean_apply_4(v_toBind_238_, lean_box(0), lean_box(0), v___x_251_, v___f_239_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___boxed(lean_object* v___f_257_, lean_object* v_declName_258_, lean_object* v___x_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_toBind_262_, lean_object* v___f_263_, lean_object* v_env_264_, lean_object* v_____do__lift_265_){
_start:
{
uint8_t v___x_932__boxed_266_; lean_object* v_res_267_; 
v___x_932__boxed_266_ = lean_unbox(v___x_259_);
v_res_267_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(v___f_257_, v_declName_258_, v___x_932__boxed_266_, v_inst_260_, v_inst_261_, v_toBind_262_, v___f_263_, v_env_264_, v_____do__lift_265_);
lean_dec_ref(v_____do__lift_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8(lean_object* v_toBind_268_, lean_object* v_getEnv_269_, lean_object* v___f_270_, lean_object* v_____r_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_apply_4(v_toBind_268_, lean_box(0), lean_box(0), v_getEnv_269_, v___f_270_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__0));
v___x_275_ = l_Lean_stringToMessageData(v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(lean_object* v_declName_276_, uint8_t v___x_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_toBind_280_, lean_object* v___f_281_, lean_object* v___f_282_, lean_object* v_____r_283_){
_start:
{
lean_object* v___x_284_; 
lean_inc(v_declName_276_);
v___x_284_ = l_Lean_privateToUserName_x3f(v_declName_276_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec(v___f_282_);
v___x_285_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_286_ = l_Lean_MessageData_ofConstName(v_declName_276_, v___x_277_);
v___x_287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = l_Lean_throwError___redArg(v_inst_278_, v_inst_279_, v___x_289_);
v___x_291_ = lean_apply_4(v_toBind_280_, lean_box(0), lean_box(0), v___x_290_, v___f_281_);
return v___x_291_;
}
else
{
lean_object* v_val_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v___f_281_);
lean_dec(v_declName_276_);
v_val_292_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_292_);
lean_dec_ref_known(v___x_284_, 1);
v___x_293_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1);
v___x_294_ = l_Lean_MessageData_ofConstName(v_val_292_, v___x_277_);
v___x_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = l_Lean_throwError___redArg(v_inst_278_, v_inst_279_, v___x_297_);
v___x_299_ = lean_apply_4(v_toBind_280_, lean_box(0), lean_box(0), v___x_298_, v___f_282_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___boxed(lean_object* v_declName_300_, lean_object* v___x_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_toBind_304_, lean_object* v___f_305_, lean_object* v___f_306_, lean_object* v_____r_307_){
_start:
{
uint8_t v___x_1006__boxed_308_; lean_object* v_res_309_; 
v___x_1006__boxed_308_ = lean_unbox(v___x_301_);
v_res_309_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(v_declName_300_, v___x_1006__boxed_308_, v_inst_302_, v_inst_303_, v_toBind_304_, v___f_305_, v___f_306_, v_____r_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10(lean_object* v_toMonadRef_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_toBind_315_, lean_object* v_declName_316_, lean_object* v_toPure_317_, lean_object* v_getEnv_318_, lean_object* v_inst_319_, lean_object* v_env_320_){
_start:
{
uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v_addInfo_323_; lean_object* v_env_324_; lean_object* v___f_325_; lean_object* v___f_326_; lean_object* v___f_327_; lean_object* v___f_328_; lean_object* v___x_329_; lean_object* v___f_330_; uint8_t v___x_331_; uint8_t v___x_332_; 
v___x_321_ = 0;
v___x_322_ = lean_box(v___x_321_);
lean_inc_n(v_toBind_315_, 4);
lean_inc_ref_n(v_inst_314_, 4);
lean_inc_ref(v_inst_313_);
lean_inc_ref(v_inst_312_);
lean_inc_ref_n(v_inst_311_, 4);
lean_inc_ref(v_toMonadRef_310_);
v_addInfo_323_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v_addInfo_323_, 0, v_toMonadRef_310_);
lean_closure_set(v_addInfo_323_, 1, v___x_322_);
lean_closure_set(v_addInfo_323_, 2, v_inst_311_);
lean_closure_set(v_addInfo_323_, 3, v_inst_312_);
lean_closure_set(v_addInfo_323_, 4, v_inst_313_);
lean_closure_set(v_addInfo_323_, 5, v_inst_314_);
lean_closure_set(v_addInfo_323_, 6, v_toBind_315_);
v_env_324_ = l_Lean_Environment_setExporting(v_env_320_, v___x_321_);
lean_inc_ref(v_addInfo_323_);
lean_inc_ref_n(v_env_324_, 4);
lean_inc_n(v_declName_316_, 4);
v___f_325_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__4), 8, 7);
lean_closure_set(v___f_325_, 0, v_declName_316_);
lean_closure_set(v___f_325_, 1, v_toPure_317_);
lean_closure_set(v___f_325_, 2, v_env_324_);
lean_closure_set(v___f_325_, 3, v_inst_311_);
lean_closure_set(v___f_325_, 4, v_inst_314_);
lean_closure_set(v___f_325_, 5, v_addInfo_323_);
lean_closure_set(v___f_325_, 6, v_toBind_315_);
lean_inc_ref(v___f_325_);
v___f_326_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_326_, 0, v___f_325_);
v___f_327_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7), 9, 8);
lean_closure_set(v___f_327_, 0, v_env_324_);
lean_closure_set(v___f_327_, 1, v_declName_316_);
lean_closure_set(v___f_327_, 2, v___f_325_);
lean_closure_set(v___f_327_, 3, v_inst_311_);
lean_closure_set(v___f_327_, 4, v_inst_314_);
lean_closure_set(v___f_327_, 5, v_toBind_315_);
lean_closure_set(v___f_327_, 6, v___f_326_);
lean_closure_set(v___f_327_, 7, v_addInfo_323_);
lean_inc_ref(v___f_327_);
v___f_328_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_328_, 0, v___f_327_);
v___x_329_ = lean_box(v___x_321_);
v___f_330_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___boxed), 9, 8);
lean_closure_set(v___f_330_, 0, v___f_327_);
lean_closure_set(v___f_330_, 1, v_declName_316_);
lean_closure_set(v___f_330_, 2, v___x_329_);
lean_closure_set(v___f_330_, 3, v_inst_311_);
lean_closure_set(v___f_330_, 4, v_inst_314_);
lean_closure_set(v___f_330_, 5, v_toBind_315_);
lean_closure_set(v___f_330_, 6, v___f_328_);
lean_closure_set(v___f_330_, 7, v_env_324_);
v___x_331_ = 1;
v___x_332_ = l_Lean_Environment_contains(v_env_324_, v_declName_316_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v_declName_316_);
lean_dec_ref(v_inst_314_);
lean_dec_ref(v_inst_312_);
lean_dec_ref(v_toMonadRef_310_);
v___x_333_ = lean_apply_4(v_toBind_315_, lean_box(0), lean_box(0), v_getEnv_318_, v___f_330_);
v___x_334_ = l_Lean_withEnv___redArg(v_inst_311_, v_inst_319_, v_inst_313_, v_env_324_, v___x_333_);
return v___x_334_;
}
else
{
lean_object* v___f_335_; lean_object* v___x_336_; lean_object* v___f_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
lean_inc_n(v_toBind_315_, 3);
v___f_335_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8), 4, 3);
lean_closure_set(v___f_335_, 0, v_toBind_315_);
lean_closure_set(v___f_335_, 1, v_getEnv_318_);
lean_closure_set(v___f_335_, 2, v___f_330_);
v___x_336_ = lean_box(v___x_331_);
lean_inc_ref(v___f_335_);
lean_inc_ref(v_inst_314_);
lean_inc_ref_n(v_inst_311_, 2);
lean_inc(v_declName_316_);
v___f_337_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_337_, 0, v_declName_316_);
lean_closure_set(v___f_337_, 1, v___x_336_);
lean_closure_set(v___f_337_, 2, v_inst_311_);
lean_closure_set(v___f_337_, 3, v_inst_314_);
lean_closure_set(v___f_337_, 4, v_toBind_315_);
lean_closure_set(v___f_337_, 5, v___f_335_);
lean_closure_set(v___f_337_, 6, v___f_335_);
lean_inc_ref(v_inst_313_);
v___x_338_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(v_toMonadRef_310_, v___x_321_, v_inst_311_, v_inst_312_, v_inst_313_, v_inst_314_, v_toBind_315_, v_declName_316_);
v___x_339_ = lean_apply_4(v_toBind_315_, lean_box(0), lean_box(0), v___x_338_, v___f_337_);
v___x_340_ = l_Lean_withEnv___redArg(v_inst_311_, v_inst_319_, v_inst_313_, v_env_324_, v___x_339_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg(lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_declName_346_){
_start:
{
lean_object* v_toApplicative_347_; lean_object* v_toBind_348_; lean_object* v_getEnv_349_; lean_object* v_toMonadRef_350_; lean_object* v_toPure_351_; lean_object* v___f_352_; lean_object* v___x_353_; 
v_toApplicative_347_ = lean_ctor_get(v_inst_341_, 0);
v_toBind_348_ = lean_ctor_get(v_inst_341_, 1);
lean_inc_n(v_toBind_348_, 2);
v_getEnv_349_ = lean_ctor_get(v_inst_342_, 0);
lean_inc_n(v_getEnv_349_, 2);
v_toMonadRef_350_ = lean_ctor_get(v_inst_343_, 1);
lean_inc_ref(v_toMonadRef_350_);
v_toPure_351_ = lean_ctor_get(v_toApplicative_347_, 1);
lean_inc(v_toPure_351_);
v___f_352_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10), 11, 10);
lean_closure_set(v___f_352_, 0, v_toMonadRef_350_);
lean_closure_set(v___f_352_, 1, v_inst_341_);
lean_closure_set(v___f_352_, 2, v_inst_345_);
lean_closure_set(v___f_352_, 3, v_inst_342_);
lean_closure_set(v___f_352_, 4, v_inst_343_);
lean_closure_set(v___f_352_, 5, v_toBind_348_);
lean_closure_set(v___f_352_, 6, v_declName_346_);
lean_closure_set(v___f_352_, 7, v_toPure_351_);
lean_closure_set(v___f_352_, 8, v_getEnv_349_);
lean_closure_set(v___f_352_, 9, v_inst_344_);
v___x_353_ = lean_apply_4(v_toBind_348_, lean_box(0), lean_box(0), v_getEnv_349_, v___f_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared(lean_object* v_m_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_declName_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(v_inst_355_, v_inst_356_, v_inst_357_, v_inst_358_, v_inst_359_, v_declName_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx(uint8_t v_x_362_){
_start:
{
switch(v_x_362_)
{
case 0:
{
lean_object* v___x_363_; 
v___x_363_ = lean_unsigned_to_nat(0u);
return v___x_363_;
}
case 1:
{
lean_object* v___x_364_; 
v___x_364_ = lean_unsigned_to_nat(1u);
return v___x_364_;
}
default: 
{
lean_object* v___x_365_; 
v___x_365_ = lean_unsigned_to_nat(2u);
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx___boxed(lean_object* v_x_366_){
_start:
{
uint8_t v_x_boxed_367_; lean_object* v_res_368_; 
v_x_boxed_367_ = lean_unbox(v_x_366_);
v_res_368_ = l_Lean_Elab_Visibility_ctorIdx(v_x_boxed_367_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___redArg(lean_object* v_k_369_){
_start:
{
lean_inc(v_k_369_);
return v_k_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___redArg___boxed(lean_object* v_k_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Elab_Visibility_ctorElim___redArg(v_k_370_);
lean_dec(v_k_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim(lean_object* v_motive_372_, lean_object* v_ctorIdx_373_, uint8_t v_t_374_, lean_object* v_h_375_, lean_object* v_k_376_){
_start:
{
lean_inc(v_k_376_);
return v_k_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___boxed(lean_object* v_motive_377_, lean_object* v_ctorIdx_378_, lean_object* v_t_379_, lean_object* v_h_380_, lean_object* v_k_381_){
_start:
{
uint8_t v_t_boxed_382_; lean_object* v_res_383_; 
v_t_boxed_382_ = lean_unbox(v_t_379_);
v_res_383_ = l_Lean_Elab_Visibility_ctorElim(v_motive_377_, v_ctorIdx_378_, v_t_boxed_382_, v_h_380_, v_k_381_);
lean_dec(v_k_381_);
lean_dec(v_ctorIdx_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___redArg(lean_object* v_regular_384_){
_start:
{
lean_inc(v_regular_384_);
return v_regular_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___redArg___boxed(lean_object* v_regular_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Elab_Visibility_regular_elim___redArg(v_regular_385_);
lean_dec(v_regular_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim(lean_object* v_motive_387_, uint8_t v_t_388_, lean_object* v_h_389_, lean_object* v_regular_390_){
_start:
{
lean_inc(v_regular_390_);
return v_regular_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___boxed(lean_object* v_motive_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_regular_394_){
_start:
{
uint8_t v_t_boxed_395_; lean_object* v_res_396_; 
v_t_boxed_395_ = lean_unbox(v_t_392_);
v_res_396_ = l_Lean_Elab_Visibility_regular_elim(v_motive_391_, v_t_boxed_395_, v_h_393_, v_regular_394_);
lean_dec(v_regular_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___redArg(lean_object* v_private_397_){
_start:
{
lean_inc(v_private_397_);
return v_private_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___redArg___boxed(lean_object* v_private_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Elab_Visibility_private_elim___redArg(v_private_398_);
lean_dec(v_private_398_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim(lean_object* v_motive_400_, uint8_t v_t_401_, lean_object* v_h_402_, lean_object* v_private_403_){
_start:
{
lean_inc(v_private_403_);
return v_private_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___boxed(lean_object* v_motive_404_, lean_object* v_t_405_, lean_object* v_h_406_, lean_object* v_private_407_){
_start:
{
uint8_t v_t_boxed_408_; lean_object* v_res_409_; 
v_t_boxed_408_ = lean_unbox(v_t_405_);
v_res_409_ = l_Lean_Elab_Visibility_private_elim(v_motive_404_, v_t_boxed_408_, v_h_406_, v_private_407_);
lean_dec(v_private_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___redArg(lean_object* v_public_410_){
_start:
{
lean_inc(v_public_410_);
return v_public_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___redArg___boxed(lean_object* v_public_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Elab_Visibility_public_elim___redArg(v_public_411_);
lean_dec(v_public_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim(lean_object* v_motive_413_, uint8_t v_t_414_, lean_object* v_h_415_, lean_object* v_public_416_){
_start:
{
lean_inc(v_public_416_);
return v_public_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___boxed(lean_object* v_motive_417_, lean_object* v_t_418_, lean_object* v_h_419_, lean_object* v_public_420_){
_start:
{
uint8_t v_t_boxed_421_; lean_object* v_res_422_; 
v_t_boxed_421_ = lean_unbox(v_t_418_);
v_res_422_ = l_Lean_Elab_Visibility_public_elim(v_motive_417_, v_t_boxed_421_, v_h_419_, v_public_420_);
lean_dec(v_public_420_);
return v_res_422_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedVisibility_default(void){
_start:
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedVisibility(void){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = 0;
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0(uint8_t v_x_428_){
_start:
{
switch(v_x_428_)
{
case 0:
{
lean_object* v___x_429_; 
v___x_429_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__0));
return v___x_429_;
}
case 1:
{
lean_object* v___x_430_; 
v___x_430_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__1));
return v___x_430_;
}
default: 
{
lean_object* v___x_431_; 
v___x_431_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__2));
return v___x_431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0___boxed(lean_object* v_x_432_){
_start:
{
uint8_t v_x_36__boxed_433_; lean_object* v_res_434_; 
v_x_36__boxed_433_ = lean_unbox(v_x_432_);
v_res_434_ = l_Lean_Elab_instToStringVisibility___lam__0(v_x_36__boxed_433_);
return v_res_434_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPrivate(uint8_t v_x_437_){
_start:
{
if (v_x_437_ == 1)
{
uint8_t v___x_438_; 
v___x_438_ = 1;
return v___x_438_;
}
else
{
uint8_t v___x_439_; 
v___x_439_ = 0;
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPrivate___boxed(lean_object* v_x_440_){
_start:
{
uint8_t v_x_17__boxed_441_; uint8_t v_res_442_; lean_object* v_r_443_; 
v_x_17__boxed_441_ = lean_unbox(v_x_440_);
v_res_442_ = l_Lean_Elab_Visibility_isPrivate(v_x_17__boxed_441_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPublic(uint8_t v_x_444_){
_start:
{
if (v_x_444_ == 2)
{
uint8_t v___x_445_; 
v___x_445_ = 1;
return v___x_445_;
}
else
{
uint8_t v___x_446_; 
v___x_446_ = 0;
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPublic___boxed(lean_object* v_x_447_){
_start:
{
uint8_t v_x_17__boxed_448_; uint8_t v_res_449_; lean_object* v_r_450_; 
v_x_17__boxed_448_ = lean_unbox(v_x_447_);
v_res_449_ = l_Lean_Elab_Visibility_isPublic(v_x_17__boxed_448_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isInferredPublic(lean_object* v_env_451_, uint8_t v_v_452_){
_start:
{
uint8_t v___y_454_; uint8_t v_isExporting_457_; 
v_isExporting_457_ = lean_ctor_get_uint8(v_env_451_, sizeof(void*)*8);
if (v_isExporting_457_ == 0)
{
lean_object* v___x_458_; uint8_t v_isModule_459_; 
v___x_458_ = l_Lean_Environment_header(v_env_451_);
v_isModule_459_ = lean_ctor_get_uint8(v___x_458_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_458_);
if (v_isModule_459_ == 0)
{
uint8_t v___x_460_; 
v___x_460_ = 1;
v___y_454_ = v___x_460_;
goto v___jp_453_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = l_Lean_Elab_Visibility_isPublic(v_v_452_);
return v___x_461_;
}
}
else
{
v___y_454_ = v_isExporting_457_;
goto v___jp_453_;
}
v___jp_453_:
{
uint8_t v___x_455_; 
v___x_455_ = l_Lean_Elab_Visibility_isPrivate(v_v_452_);
if (v___x_455_ == 0)
{
return v___y_454_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = 0;
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isInferredPublic___boxed(lean_object* v_env_462_, lean_object* v_v_463_){
_start:
{
uint8_t v_v_boxed_464_; uint8_t v_res_465_; lean_object* v_r_466_; 
v_v_boxed_464_ = lean_unbox(v_v_463_);
v_res_465_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_462_, v_v_boxed_464_);
lean_dec_ref(v_env_462_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__0(lean_object* v_toPure_467_, lean_object* v_____r_468_){
_start:
{
uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = 2;
v___x_470_ = lean_box(v___x_469_);
v___x_471_ = lean_apply_2(v_toPure_467_, lean_box(0), v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__2(lean_object* v_toPure_472_, lean_object* v_____r_473_){
_start:
{
uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = 1;
v___x_475_ = lean_box(v___x_474_);
v___x_476_ = lean_apply_2(v_toPure_472_, lean_box(0), v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__0));
v___x_479_ = l_Lean_stringToMessageData(v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__2));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__10));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__12));
v___x_502_ = l_Lean_stringToMessageData(v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3(lean_object* v_vis_x3f_503_, lean_object* v_toPure_504_, lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_toBind_511_, lean_object* v___f_512_, lean_object* v___f_513_, lean_object* v___f_514_, lean_object* v___f_515_, lean_object* v_env_516_){
_start:
{
if (lean_obj_tag(v_vis_x3f_503_) == 0)
{
uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v___f_515_);
lean_dec(v___f_514_);
lean_dec(v___f_513_);
lean_dec(v___f_512_);
lean_dec(v_toBind_511_);
lean_dec_ref(v_inst_510_);
lean_dec(v_inst_509_);
lean_dec(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec_ref(v_inst_506_);
lean_dec_ref(v_inst_505_);
v___x_520_ = 0;
v___x_521_ = lean_box(v___x_520_);
v___x_522_ = lean_apply_2(v_toPure_504_, lean_box(0), v___x_521_);
return v___x_522_;
}
else
{
lean_object* v_val_523_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; uint8_t v___y_542_; lean_object* v___x_545_; uint8_t v___x_546_; uint8_t v___y_548_; 
lean_dec(v_toPure_504_);
v_val_523_ = lean_ctor_get(v_vis_x3f_503_, 0);
lean_inc_n(v_val_523_, 2);
lean_dec_ref_known(v_vis_x3f_503_, 1);
v___x_545_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8));
v___x_546_ = l_Lean_Syntax_isOfKind(v_val_523_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_552_; uint8_t v___x_553_; 
lean_dec(v___f_515_);
lean_dec(v___f_514_);
v___x_552_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9));
lean_inc(v_val_523_);
v___x_553_ = l_Lean_Syntax_isOfKind(v_val_523_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec(v___f_513_);
lean_dec(v___f_512_);
lean_dec(v_toBind_511_);
lean_dec_ref(v_inst_510_);
lean_dec(v_inst_509_);
lean_dec(v_inst_508_);
lean_dec_ref(v_inst_507_);
v___x_554_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11);
v___x_555_ = l_Lean_throwErrorAt___redArg(v_inst_505_, v_inst_506_, v_val_523_, v___x_554_);
return v___x_555_;
}
else
{
lean_object* v___x_556_; 
lean_dec_ref(v_inst_506_);
v___x_556_ = l_Lean_Syntax_getHeadInfo(v_val_523_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_dec_ref_known(v___x_556_, 4);
v___y_548_ = v___x_553_;
goto v___jp_547_;
}
else
{
lean_dec(v___x_556_);
if (v___x_546_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v_val_523_);
lean_dec(v___f_512_);
lean_dec(v_toBind_511_);
lean_dec_ref(v_inst_510_);
lean_dec(v_inst_509_);
lean_dec(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec_ref(v_inst_505_);
v___x_557_ = lean_box(0);
v___x_558_ = lean_apply_1(v___f_513_, v___x_557_);
return v___x_558_;
}
else
{
v___y_548_ = v___x_546_;
goto v___jp_547_;
}
}
}
}
else
{
lean_object* v___x_559_; 
lean_dec(v___f_513_);
lean_dec(v___f_512_);
lean_dec_ref(v_inst_506_);
v___x_559_ = l_Lean_Syntax_getHeadInfo(v_val_523_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v___x_560_; uint8_t v_isModule_561_; 
lean_dec_ref_known(v___x_559_, 4);
v___x_560_ = l_Lean_Environment_header(v_env_516_);
v_isModule_561_ = lean_ctor_get_uint8(v___x_560_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_560_);
if (v_isModule_561_ == 0)
{
lean_dec(v_val_523_);
lean_dec(v___f_515_);
lean_dec(v_toBind_511_);
lean_dec_ref(v_inst_510_);
lean_dec(v_inst_509_);
lean_dec(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec_ref(v_inst_505_);
goto v___jp_517_;
}
else
{
uint8_t v_isExporting_562_; 
v_isExporting_562_ = lean_ctor_get_uint8(v_env_516_, sizeof(void*)*8);
if (v_isExporting_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v___f_514_);
v___x_563_ = l_Lean_linter_redundantVisibility;
v___x_564_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13);
v___x_565_ = l_Lean_Linter_logLintIf___redArg(v_inst_505_, v_inst_507_, v_inst_508_, v_inst_509_, v_inst_510_, v___x_563_, v_val_523_, v___x_564_);
v___x_566_ = lean_apply_4(v_toBind_511_, lean_box(0), lean_box(0), v___x_565_, v___f_515_);
return v___x_566_;
}
else
{
lean_dec(v_val_523_);
lean_dec(v___f_515_);
lean_dec(v_toBind_511_);
lean_dec_ref(v_inst_510_);
lean_dec(v_inst_509_);
lean_dec(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec_ref(v_inst_505_);
goto v___jp_517_;
}
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v___x_559_);
lean_dec(v_val_523_);
lean_dec(v___f_515_);
lean_dec(v_toBind_511_);
lean_dec_ref(v_inst_510_);
lean_dec(v_inst_509_);
lean_dec(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec_ref(v_inst_505_);
v___x_567_ = lean_box(0);
v___x_568_ = lean_apply_1(v___f_514_, v___x_567_);
return v___x_568_;
}
}
v___jp_524_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
lean_inc_ref(v___y_527_);
v___x_528_ = l_Lean_stringToMessageData(v___y_527_);
lean_inc_ref(v___y_526_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___y_526_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
lean_inc_ref(v___y_525_);
v___x_532_ = l_Lean_Linter_logLintIf___redArg(v_inst_505_, v_inst_507_, v_inst_508_, v_inst_509_, v_inst_510_, v___y_525_, v_val_523_, v___x_531_);
v___x_533_ = lean_apply_4(v_toBind_511_, lean_box(0), lean_box(0), v___x_532_, v___f_512_);
return v___x_533_;
}
v___jp_534_:
{
lean_object* v___x_535_; uint8_t v_isModule_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_535_ = l_Lean_Environment_header(v_env_516_);
v_isModule_536_ = lean_ctor_get_uint8(v___x_535_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_535_);
v___x_537_ = l_Lean_linter_redundantVisibility;
v___x_538_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3);
if (v_isModule_536_ == 0)
{
lean_object* v___x_539_; 
v___x_539_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4));
v___y_525_ = v___x_537_;
v___y_526_ = v___x_538_;
v___y_527_ = v___x_539_;
goto v___jp_524_;
}
else
{
lean_object* v___x_540_; 
v___x_540_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__5));
v___y_525_ = v___x_537_;
v___y_526_ = v___x_538_;
v___y_527_ = v___x_540_;
goto v___jp_524_;
}
}
v___jp_541_:
{
if (v___y_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec(v_val_523_);
lean_dec(v___f_512_);
lean_dec(v_toBind_511_);
lean_dec_ref(v_inst_510_);
lean_dec(v_inst_509_);
lean_dec(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec_ref(v_inst_505_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_apply_1(v___f_513_, v___x_543_);
return v___x_544_;
}
else
{
lean_dec(v___f_513_);
goto v___jp_534_;
}
}
v___jp_547_:
{
uint8_t v_isExporting_549_; 
v_isExporting_549_ = lean_ctor_get_uint8(v_env_516_, sizeof(void*)*8);
if (v_isExporting_549_ == 0)
{
lean_object* v___x_550_; uint8_t v_isModule_551_; 
v___x_550_ = l_Lean_Environment_header(v_env_516_);
v_isModule_551_ = lean_ctor_get_uint8(v___x_550_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_550_);
if (v_isModule_551_ == 0)
{
v___y_542_ = v___y_548_;
goto v___jp_541_;
}
else
{
v___y_542_ = v___x_546_;
goto v___jp_541_;
}
}
else
{
lean_dec(v___f_513_);
goto v___jp_534_;
}
}
}
v___jp_517_:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_box(0);
v___x_519_ = lean_apply_1(v___f_514_, v___x_518_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___boxed(lean_object* v_vis_x3f_569_, lean_object* v_toPure_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_toBind_577_, lean_object* v___f_578_, lean_object* v___f_579_, lean_object* v___f_580_, lean_object* v___f_581_, lean_object* v_env_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Elab_elabVisibility___redArg___lam__3(v_vis_x3f_569_, v_toPure_570_, v_inst_571_, v_inst_572_, v_inst_573_, v_inst_574_, v_inst_575_, v_inst_576_, v_toBind_577_, v___f_578_, v___f_579_, v___f_580_, v___f_581_, v_env_582_);
lean_dec_ref(v_env_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg(lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_vis_x3f_590_){
_start:
{
lean_object* v_toApplicative_591_; lean_object* v_toBind_592_; lean_object* v_getEnv_593_; lean_object* v_toPure_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___x_600_; 
v_toApplicative_591_ = lean_ctor_get(v_inst_584_, 0);
v_toBind_592_ = lean_ctor_get(v_inst_584_, 1);
lean_inc_n(v_toBind_592_, 2);
v_getEnv_593_ = lean_ctor_get(v_inst_586_, 0);
lean_inc(v_getEnv_593_);
v_toPure_594_ = lean_ctor_get(v_toApplicative_591_, 1);
lean_inc_n(v_toPure_594_, 3);
v___f_595_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__0), 2, 1);
lean_closure_set(v___f_595_, 0, v_toPure_594_);
lean_inc_ref(v___f_595_);
v___f_596_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_596_, 0, v___f_595_);
v___f_597_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__2), 2, 1);
lean_closure_set(v___f_597_, 0, v_toPure_594_);
lean_inc_ref(v___f_597_);
v___f_598_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_598_, 0, v___f_597_);
v___f_599_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__3___boxed), 14, 13);
lean_closure_set(v___f_599_, 0, v_vis_x3f_590_);
lean_closure_set(v___f_599_, 1, v_toPure_594_);
lean_closure_set(v___f_599_, 2, v_inst_584_);
lean_closure_set(v___f_599_, 3, v_inst_585_);
lean_closure_set(v___f_599_, 4, v_inst_588_);
lean_closure_set(v___f_599_, 5, v_inst_589_);
lean_closure_set(v___f_599_, 6, v_inst_587_);
lean_closure_set(v___f_599_, 7, v_inst_586_);
lean_closure_set(v___f_599_, 8, v_toBind_592_);
lean_closure_set(v___f_599_, 9, v___f_596_);
lean_closure_set(v___f_599_, 10, v___f_595_);
lean_closure_set(v___f_599_, 11, v___f_597_);
lean_closure_set(v___f_599_, 12, v___f_598_);
v___x_600_ = lean_apply_4(v_toBind_592_, lean_box(0), lean_box(0), v_getEnv_593_, v___f_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility(lean_object* v_m_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_vis_x3f_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_Elab_elabVisibility___redArg(v_inst_602_, v_inst_603_, v_inst_604_, v_inst_605_, v_inst_606_, v_inst_607_, v_vis_x3f_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx(uint8_t v_x_610_){
_start:
{
switch(v_x_610_)
{
case 0:
{
lean_object* v___x_611_; 
v___x_611_ = lean_unsigned_to_nat(0u);
return v___x_611_;
}
case 1:
{
lean_object* v___x_612_; 
v___x_612_ = lean_unsigned_to_nat(1u);
return v___x_612_;
}
default: 
{
lean_object* v___x_613_; 
v___x_613_ = lean_unsigned_to_nat(2u);
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___boxed(lean_object* v_x_614_){
_start:
{
uint8_t v_x_boxed_615_; lean_object* v_res_616_; 
v_x_boxed_615_ = lean_unbox(v_x_614_);
v_res_616_ = l_Lean_Elab_RecKind_ctorIdx(v_x_boxed_615_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg(lean_object* v_k_617_){
_start:
{
lean_inc(v_k_617_);
return v_k_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg___boxed(lean_object* v_k_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_Elab_RecKind_ctorElim___redArg(v_k_618_);
lean_dec(v_k_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim(lean_object* v_motive_620_, lean_object* v_ctorIdx_621_, uint8_t v_t_622_, lean_object* v_h_623_, lean_object* v_k_624_){
_start:
{
lean_inc(v_k_624_);
return v_k_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___boxed(lean_object* v_motive_625_, lean_object* v_ctorIdx_626_, lean_object* v_t_627_, lean_object* v_h_628_, lean_object* v_k_629_){
_start:
{
uint8_t v_t_boxed_630_; lean_object* v_res_631_; 
v_t_boxed_630_ = lean_unbox(v_t_627_);
v_res_631_ = l_Lean_Elab_RecKind_ctorElim(v_motive_625_, v_ctorIdx_626_, v_t_boxed_630_, v_h_628_, v_k_629_);
lean_dec(v_k_629_);
lean_dec(v_ctorIdx_626_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg(lean_object* v_partial_632_){
_start:
{
lean_inc(v_partial_632_);
return v_partial_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg___boxed(lean_object* v_partial_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Elab_RecKind_partial_elim___redArg(v_partial_633_);
lean_dec(v_partial_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim(lean_object* v_motive_635_, uint8_t v_t_636_, lean_object* v_h_637_, lean_object* v_partial_638_){
_start:
{
lean_inc(v_partial_638_);
return v_partial_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___boxed(lean_object* v_motive_639_, lean_object* v_t_640_, lean_object* v_h_641_, lean_object* v_partial_642_){
_start:
{
uint8_t v_t_boxed_643_; lean_object* v_res_644_; 
v_t_boxed_643_ = lean_unbox(v_t_640_);
v_res_644_ = l_Lean_Elab_RecKind_partial_elim(v_motive_639_, v_t_boxed_643_, v_h_641_, v_partial_642_);
lean_dec(v_partial_642_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg(lean_object* v_nonrec_645_){
_start:
{
lean_inc(v_nonrec_645_);
return v_nonrec_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg___boxed(lean_object* v_nonrec_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Elab_RecKind_nonrec_elim___redArg(v_nonrec_646_);
lean_dec(v_nonrec_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim(lean_object* v_motive_648_, uint8_t v_t_649_, lean_object* v_h_650_, lean_object* v_nonrec_651_){
_start:
{
lean_inc(v_nonrec_651_);
return v_nonrec_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___boxed(lean_object* v_motive_652_, lean_object* v_t_653_, lean_object* v_h_654_, lean_object* v_nonrec_655_){
_start:
{
uint8_t v_t_boxed_656_; lean_object* v_res_657_; 
v_t_boxed_656_ = lean_unbox(v_t_653_);
v_res_657_ = l_Lean_Elab_RecKind_nonrec_elim(v_motive_652_, v_t_boxed_656_, v_h_654_, v_nonrec_655_);
lean_dec(v_nonrec_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg(lean_object* v_default_658_){
_start:
{
lean_inc(v_default_658_);
return v_default_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg___boxed(lean_object* v_default_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_Elab_RecKind_default_elim___redArg(v_default_659_);
lean_dec(v_default_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim(lean_object* v_motive_661_, uint8_t v_t_662_, lean_object* v_h_663_, lean_object* v_default_664_){
_start:
{
lean_inc(v_default_664_);
return v_default_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___boxed(lean_object* v_motive_665_, lean_object* v_t_666_, lean_object* v_h_667_, lean_object* v_default_668_){
_start:
{
uint8_t v_t_boxed_669_; lean_object* v_res_670_; 
v_t_boxed_669_ = lean_unbox(v_t_666_);
v_res_670_ = l_Lean_Elab_RecKind_default_elim(v_motive_665_, v_t_boxed_669_, v_h_667_, v_default_668_);
lean_dec(v_default_668_);
return v_res_670_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind_default(void){
_start:
{
uint8_t v___x_671_; 
v___x_671_ = 0;
return v___x_671_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind(void){
_start:
{
uint8_t v___x_672_; 
v___x_672_ = 0;
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx(uint8_t v_x_673_){
_start:
{
switch(v_x_673_)
{
case 0:
{
lean_object* v___x_674_; 
v___x_674_ = lean_unsigned_to_nat(0u);
return v___x_674_;
}
case 1:
{
lean_object* v___x_675_; 
v___x_675_ = lean_unsigned_to_nat(1u);
return v___x_675_;
}
default: 
{
lean_object* v___x_676_; 
v___x_676_ = lean_unsigned_to_nat(2u);
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___boxed(lean_object* v_x_677_){
_start:
{
uint8_t v_x_boxed_678_; lean_object* v_res_679_; 
v_x_boxed_678_ = lean_unbox(v_x_677_);
v_res_679_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_boxed_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg(lean_object* v_k_680_){
_start:
{
lean_inc(v_k_680_);
return v_k_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg___boxed(lean_object* v_k_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Elab_ComputeKind_ctorElim___redArg(v_k_681_);
lean_dec(v_k_681_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim(lean_object* v_motive_683_, lean_object* v_ctorIdx_684_, uint8_t v_t_685_, lean_object* v_h_686_, lean_object* v_k_687_){
_start:
{
lean_inc(v_k_687_);
return v_k_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___boxed(lean_object* v_motive_688_, lean_object* v_ctorIdx_689_, lean_object* v_t_690_, lean_object* v_h_691_, lean_object* v_k_692_){
_start:
{
uint8_t v_t_boxed_693_; lean_object* v_res_694_; 
v_t_boxed_693_ = lean_unbox(v_t_690_);
v_res_694_ = l_Lean_Elab_ComputeKind_ctorElim(v_motive_688_, v_ctorIdx_689_, v_t_boxed_693_, v_h_691_, v_k_692_);
lean_dec(v_k_692_);
lean_dec(v_ctorIdx_689_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg(lean_object* v_regular_695_){
_start:
{
lean_inc(v_regular_695_);
return v_regular_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg___boxed(lean_object* v_regular_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Elab_ComputeKind_regular_elim___redArg(v_regular_696_);
lean_dec(v_regular_696_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim(lean_object* v_motive_698_, uint8_t v_t_699_, lean_object* v_h_700_, lean_object* v_regular_701_){
_start:
{
lean_inc(v_regular_701_);
return v_regular_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___boxed(lean_object* v_motive_702_, lean_object* v_t_703_, lean_object* v_h_704_, lean_object* v_regular_705_){
_start:
{
uint8_t v_t_boxed_706_; lean_object* v_res_707_; 
v_t_boxed_706_ = lean_unbox(v_t_703_);
v_res_707_ = l_Lean_Elab_ComputeKind_regular_elim(v_motive_702_, v_t_boxed_706_, v_h_704_, v_regular_705_);
lean_dec(v_regular_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg(lean_object* v_meta_708_){
_start:
{
lean_inc(v_meta_708_);
return v_meta_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg___boxed(lean_object* v_meta_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Elab_ComputeKind_meta_elim___redArg(v_meta_709_);
lean_dec(v_meta_709_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim(lean_object* v_motive_711_, uint8_t v_t_712_, lean_object* v_h_713_, lean_object* v_meta_714_){
_start:
{
lean_inc(v_meta_714_);
return v_meta_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___boxed(lean_object* v_motive_715_, lean_object* v_t_716_, lean_object* v_h_717_, lean_object* v_meta_718_){
_start:
{
uint8_t v_t_boxed_719_; lean_object* v_res_720_; 
v_t_boxed_719_ = lean_unbox(v_t_716_);
v_res_720_ = l_Lean_Elab_ComputeKind_meta_elim(v_motive_715_, v_t_boxed_719_, v_h_717_, v_meta_718_);
lean_dec(v_meta_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(lean_object* v_noncomputable_721_){
_start:
{
lean_inc(v_noncomputable_721_);
return v_noncomputable_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg___boxed(lean_object* v_noncomputable_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(v_noncomputable_722_);
lean_dec(v_noncomputable_722_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim(lean_object* v_motive_724_, uint8_t v_t_725_, lean_object* v_h_726_, lean_object* v_noncomputable_727_){
_start:
{
lean_inc(v_noncomputable_727_);
return v_noncomputable_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___boxed(lean_object* v_motive_728_, lean_object* v_t_729_, lean_object* v_h_730_, lean_object* v_noncomputable_731_){
_start:
{
uint8_t v_t_boxed_732_; lean_object* v_res_733_; 
v_t_boxed_732_ = lean_unbox(v_t_729_);
v_res_733_ = l_Lean_Elab_ComputeKind_noncomputable_elim(v_motive_728_, v_t_boxed_732_, v_h_730_, v_noncomputable_731_);
lean_dec(v_noncomputable_731_);
return v_res_733_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind_default(void){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = 0;
return v___x_734_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind(void){
_start:
{
uint8_t v___x_735_; 
v___x_735_ = 0;
return v___x_735_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqComputeKind_beq(uint8_t v_x_736_, uint8_t v_y_737_){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_738_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_736_);
v___x_739_ = l_Lean_Elab_ComputeKind_ctorIdx(v_y_737_);
v___x_740_ = lean_nat_dec_eq(v___x_738_, v___x_739_);
lean_dec(v___x_739_);
lean_dec(v___x_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqComputeKind_beq___boxed(lean_object* v_x_741_, lean_object* v_y_742_){
_start:
{
uint8_t v_x_21__boxed_743_; uint8_t v_y_22__boxed_744_; uint8_t v_res_745_; lean_object* v_r_746_; 
v_x_21__boxed_743_ = lean_unbox(v_x_741_);
v_y_22__boxed_744_ = lean_unbox(v_y_742_);
v_res_745_ = l_Lean_Elab_instBEqComputeKind_beq(v_x_21__boxed_743_, v_y_22__boxed_744_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
static lean_object* _init_l_Lean_Elab_instReprComputeKind_repr___closed__6(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_unsigned_to_nat(2u);
v___x_759_ = lean_nat_to_int(v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_Elab_instReprComputeKind_repr___closed__7(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_nat_to_int(v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprComputeKind_repr(uint8_t v_x_762_, lean_object* v_prec_763_){
_start:
{
lean_object* v___y_765_; lean_object* v___y_772_; lean_object* v___y_779_; 
switch(v_x_762_)
{
case 0:
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = lean_unsigned_to_nat(1024u);
v___x_786_ = lean_nat_dec_le(v___x_785_, v_prec_763_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
v___x_787_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_765_ = v___x_787_;
goto v___jp_764_;
}
else
{
lean_object* v___x_788_; 
v___x_788_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_765_ = v___x_788_;
goto v___jp_764_;
}
}
case 1:
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = lean_unsigned_to_nat(1024u);
v___x_790_ = lean_nat_dec_le(v___x_789_, v_prec_763_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
v___x_791_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_772_ = v___x_791_;
goto v___jp_771_;
}
else
{
lean_object* v___x_792_; 
v___x_792_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_772_ = v___x_792_;
goto v___jp_771_;
}
}
default: 
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_unsigned_to_nat(1024u);
v___x_794_ = lean_nat_dec_le(v___x_793_, v_prec_763_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
v___x_795_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_779_ = v___x_795_;
goto v___jp_778_;
}
else
{
lean_object* v___x_796_; 
v___x_796_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_779_ = v___x_796_;
goto v___jp_778_;
}
}
}
v___jp_764_:
{
lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_766_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__1));
lean_inc(v___y_765_);
v___x_767_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_767_, 0, v___y_765_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = 0;
v___x_769_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*1, v___x_768_);
v___x_770_ = l_Repr_addAppParen(v___x_769_, v_prec_763_);
return v___x_770_;
}
v___jp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_773_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__3));
lean_inc(v___y_772_);
v___x_774_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_774_, 0, v___y_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = 0;
v___x_776_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set_uint8(v___x_776_, sizeof(void*)*1, v___x_775_);
v___x_777_ = l_Repr_addAppParen(v___x_776_, v_prec_763_);
return v___x_777_;
}
v___jp_778_:
{
lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_780_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__5));
lean_inc(v___y_779_);
v___x_781_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_781_, 0, v___y_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = 0;
v___x_783_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*1, v___x_782_);
v___x_784_ = l_Repr_addAppParen(v___x_783_, v_prec_763_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprComputeKind_repr___boxed(lean_object* v_x_797_, lean_object* v_prec_798_){
_start:
{
uint8_t v_x_171__boxed_799_; lean_object* v_res_800_; 
v_x_171__boxed_799_ = lean_unbox(v_x_797_);
v_res_800_ = l_Lean_Elab_instReprComputeKind_repr(v_x_171__boxed_799_, v_prec_798_);
lean_dec(v_prec_798_);
return v_res_800_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object* v_m_815_){
_start:
{
uint8_t v_visibility_816_; uint8_t v___x_817_; 
v_visibility_816_ = lean_ctor_get_uint8(v_m_815_, sizeof(void*)*3);
v___x_817_ = l_Lean_Elab_Visibility_isPrivate(v_visibility_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPrivate___boxed(lean_object* v_m_818_){
_start:
{
uint8_t v_res_819_; lean_object* v_r_820_; 
v_res_819_ = l_Lean_Elab_Modifiers_isPrivate(v_m_818_);
lean_dec_ref(v_m_818_);
v_r_820_ = lean_box(v_res_819_);
return v_r_820_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPublic(lean_object* v_m_821_){
_start:
{
uint8_t v_visibility_822_; uint8_t v___x_823_; 
v_visibility_822_ = lean_ctor_get_uint8(v_m_821_, sizeof(void*)*3);
v___x_823_ = l_Lean_Elab_Visibility_isPublic(v_visibility_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPublic___boxed(lean_object* v_m_824_){
_start:
{
uint8_t v_res_825_; lean_object* v_r_826_; 
v_res_825_ = l_Lean_Elab_Modifiers_isPublic(v_m_824_);
lean_dec_ref(v_m_824_);
v_r_826_ = lean_box(v_res_825_);
return v_r_826_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isInferredPublic(lean_object* v_env_827_, lean_object* v_m_828_){
_start:
{
uint8_t v_visibility_829_; uint8_t v___x_830_; 
v_visibility_829_ = lean_ctor_get_uint8(v_m_828_, sizeof(void*)*3);
v___x_830_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_827_, v_visibility_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isInferredPublic___boxed(lean_object* v_env_831_, lean_object* v_m_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_Lean_Elab_Modifiers_isInferredPublic(v_env_831_, v_m_832_);
lean_dec_ref(v_m_832_);
lean_dec_ref(v_env_831_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object* v_x_835_){
_start:
{
uint8_t v_recKind_836_; 
v_recKind_836_ = lean_ctor_get_uint8(v_x_835_, sizeof(void*)*3 + 3);
if (v_recKind_836_ == 0)
{
uint8_t v___x_837_; 
v___x_837_ = 1;
return v___x_837_;
}
else
{
uint8_t v___x_838_; 
v___x_838_ = 0;
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPartial___boxed(lean_object* v_x_839_){
_start:
{
uint8_t v_res_840_; lean_object* v_r_841_; 
v_res_840_ = l_Lean_Elab_Modifiers_isPartial(v_x_839_);
lean_dec_ref(v_x_839_);
v_r_841_ = lean_box(v_res_840_);
return v_r_841_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNonrec(lean_object* v_x_842_){
_start:
{
uint8_t v_recKind_843_; 
v_recKind_843_ = lean_ctor_get_uint8(v_x_842_, sizeof(void*)*3 + 3);
if (v_recKind_843_ == 1)
{
uint8_t v___x_844_; 
v___x_844_ = 1;
return v___x_844_;
}
else
{
uint8_t v___x_845_; 
v___x_845_ = 0;
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNonrec___boxed(lean_object* v_x_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l_Lean_Elab_Modifiers_isNonrec(v_x_846_);
lean_dec_ref(v_x_846_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isMeta(lean_object* v_m_849_){
_start:
{
uint8_t v_computeKind_850_; 
v_computeKind_850_ = lean_ctor_get_uint8(v_m_849_, sizeof(void*)*3 + 2);
if (v_computeKind_850_ == 1)
{
uint8_t v___x_851_; 
v___x_851_ = 1;
return v___x_851_;
}
else
{
uint8_t v___x_852_; 
v___x_852_ = 0;
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isMeta___boxed(lean_object* v_m_853_){
_start:
{
uint8_t v_res_854_; lean_object* v_r_855_; 
v_res_854_ = l_Lean_Elab_Modifiers_isMeta(v_m_853_);
lean_dec_ref(v_m_853_);
v_r_855_ = lean_box(v_res_854_);
return v_r_855_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNoncomputable(lean_object* v_m_856_){
_start:
{
uint8_t v_computeKind_857_; 
v_computeKind_857_ = lean_ctor_get_uint8(v_m_856_, sizeof(void*)*3 + 2);
if (v_computeKind_857_ == 2)
{
uint8_t v___x_858_; 
v___x_858_ = 1;
return v___x_858_;
}
else
{
uint8_t v___x_859_; 
v___x_859_ = 0;
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNoncomputable___boxed(lean_object* v_m_860_){
_start:
{
uint8_t v_res_861_; lean_object* v_r_862_; 
v_res_861_ = l_Lean_Elab_Modifiers_isNoncomputable(v_m_860_);
lean_dec_ref(v_m_860_);
v_r_862_ = lean_box(v_res_861_);
return v_r_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addAttr(lean_object* v_modifiers_863_, lean_object* v_attr_864_){
_start:
{
lean_object* v_stx_865_; lean_object* v_docString_x3f_866_; uint8_t v_visibility_867_; uint8_t v_isProtected_868_; uint8_t v_computeKind_869_; uint8_t v_recKind_870_; uint8_t v_isUnsafe_871_; lean_object* v_attrs_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_880_; 
v_stx_865_ = lean_ctor_get(v_modifiers_863_, 0);
v_docString_x3f_866_ = lean_ctor_get(v_modifiers_863_, 1);
v_visibility_867_ = lean_ctor_get_uint8(v_modifiers_863_, sizeof(void*)*3);
v_isProtected_868_ = lean_ctor_get_uint8(v_modifiers_863_, sizeof(void*)*3 + 1);
v_computeKind_869_ = lean_ctor_get_uint8(v_modifiers_863_, sizeof(void*)*3 + 2);
v_recKind_870_ = lean_ctor_get_uint8(v_modifiers_863_, sizeof(void*)*3 + 3);
v_isUnsafe_871_ = lean_ctor_get_uint8(v_modifiers_863_, sizeof(void*)*3 + 4);
v_attrs_872_ = lean_ctor_get(v_modifiers_863_, 2);
v_isSharedCheck_880_ = !lean_is_exclusive(v_modifiers_863_);
if (v_isSharedCheck_880_ == 0)
{
v___x_874_ = v_modifiers_863_;
v_isShared_875_ = v_isSharedCheck_880_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_attrs_872_);
lean_inc(v_docString_x3f_866_);
lean_inc(v_stx_865_);
lean_dec(v_modifiers_863_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_880_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = lean_array_push(v_attrs_872_, v_attr_864_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 2, v___x_876_);
v___x_878_ = v___x_874_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_stx_865_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_docString_x3f_866_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v___x_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_879_, sizeof(void*)*3, v_visibility_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_879_, sizeof(void*)*3 + 1, v_isProtected_868_);
lean_ctor_set_uint8(v_reuseFailAlloc_879_, sizeof(void*)*3 + 2, v_computeKind_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_879_, sizeof(void*)*3 + 3, v_recKind_870_);
lean_ctor_set_uint8(v_reuseFailAlloc_879_, sizeof(void*)*3 + 4, v_isUnsafe_871_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addFirstAttr(lean_object* v_modifiers_881_, lean_object* v_attr_882_){
_start:
{
lean_object* v_stx_883_; lean_object* v_docString_x3f_884_; uint8_t v_visibility_885_; uint8_t v_isProtected_886_; uint8_t v_computeKind_887_; uint8_t v_recKind_888_; uint8_t v_isUnsafe_889_; lean_object* v_attrs_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_901_; 
v_stx_883_ = lean_ctor_get(v_modifiers_881_, 0);
v_docString_x3f_884_ = lean_ctor_get(v_modifiers_881_, 1);
v_visibility_885_ = lean_ctor_get_uint8(v_modifiers_881_, sizeof(void*)*3);
v_isProtected_886_ = lean_ctor_get_uint8(v_modifiers_881_, sizeof(void*)*3 + 1);
v_computeKind_887_ = lean_ctor_get_uint8(v_modifiers_881_, sizeof(void*)*3 + 2);
v_recKind_888_ = lean_ctor_get_uint8(v_modifiers_881_, sizeof(void*)*3 + 3);
v_isUnsafe_889_ = lean_ctor_get_uint8(v_modifiers_881_, sizeof(void*)*3 + 4);
v_attrs_890_ = lean_ctor_get(v_modifiers_881_, 2);
v_isSharedCheck_901_ = !lean_is_exclusive(v_modifiers_881_);
if (v_isSharedCheck_901_ == 0)
{
v___x_892_ = v_modifiers_881_;
v_isShared_893_ = v_isSharedCheck_901_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_attrs_890_);
lean_inc(v_docString_x3f_884_);
lean_inc(v_stx_883_);
lean_dec(v_modifiers_881_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_901_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_894_ = lean_unsigned_to_nat(1u);
v___x_895_ = lean_mk_empty_array_with_capacity(v___x_894_);
v___x_896_ = lean_array_push(v___x_895_, v_attr_882_);
v___x_897_ = l_Array_append___redArg(v___x_896_, v_attrs_890_);
lean_dec_ref(v_attrs_890_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 2, v___x_897_);
v___x_899_ = v___x_892_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_stx_883_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_docString_x3f_884_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v___x_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_900_, sizeof(void*)*3, v_visibility_885_);
lean_ctor_set_uint8(v_reuseFailAlloc_900_, sizeof(void*)*3 + 1, v_isProtected_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_900_, sizeof(void*)*3 + 2, v_computeKind_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_900_, sizeof(void*)*3 + 3, v_recKind_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_900_, sizeof(void*)*3 + 4, v_isUnsafe_889_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(lean_object* v_p_902_, lean_object* v_as_903_, size_t v_i_904_, size_t v_stop_905_, lean_object* v_b_906_){
_start:
{
lean_object* v___y_908_; uint8_t v___x_912_; 
v___x_912_ = lean_usize_dec_eq(v_i_904_, v_stop_905_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_913_ = lean_array_uget_borrowed(v_as_903_, v_i_904_);
lean_inc_ref(v_p_902_);
lean_inc(v___x_913_);
v___x_914_ = lean_apply_1(v_p_902_, v___x_913_);
v___x_915_ = lean_unbox(v___x_914_);
if (v___x_915_ == 0)
{
v___y_908_ = v_b_906_;
goto v___jp_907_;
}
else
{
lean_object* v___x_916_; 
lean_inc(v___x_913_);
v___x_916_ = lean_array_push(v_b_906_, v___x_913_);
v___y_908_ = v___x_916_;
goto v___jp_907_;
}
}
else
{
lean_dec_ref(v_p_902_);
return v_b_906_;
}
v___jp_907_:
{
size_t v___x_909_; size_t v___x_910_; 
v___x_909_ = ((size_t)1ULL);
v___x_910_ = lean_usize_add(v_i_904_, v___x_909_);
v_i_904_ = v___x_910_;
v_b_906_ = v___y_908_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0___boxed(lean_object* v_p_917_, lean_object* v_as_918_, lean_object* v_i_919_, lean_object* v_stop_920_, lean_object* v_b_921_){
_start:
{
size_t v_i_boxed_922_; size_t v_stop_boxed_923_; lean_object* v_res_924_; 
v_i_boxed_922_ = lean_unbox_usize(v_i_919_);
lean_dec(v_i_919_);
v_stop_boxed_923_ = lean_unbox_usize(v_stop_920_);
lean_dec(v_stop_920_);
v_res_924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_917_, v_as_918_, v_i_boxed_922_, v_stop_boxed_923_, v_b_921_);
lean_dec_ref(v_as_918_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object* v_modifiers_925_, lean_object* v_p_926_){
_start:
{
lean_object* v_stx_927_; lean_object* v_docString_x3f_928_; uint8_t v_visibility_929_; uint8_t v_isProtected_930_; uint8_t v_computeKind_931_; uint8_t v_recKind_932_; uint8_t v_isUnsafe_933_; lean_object* v_attrs_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_961_; 
v_stx_927_ = lean_ctor_get(v_modifiers_925_, 0);
v_docString_x3f_928_ = lean_ctor_get(v_modifiers_925_, 1);
v_visibility_929_ = lean_ctor_get_uint8(v_modifiers_925_, sizeof(void*)*3);
v_isProtected_930_ = lean_ctor_get_uint8(v_modifiers_925_, sizeof(void*)*3 + 1);
v_computeKind_931_ = lean_ctor_get_uint8(v_modifiers_925_, sizeof(void*)*3 + 2);
v_recKind_932_ = lean_ctor_get_uint8(v_modifiers_925_, sizeof(void*)*3 + 3);
v_isUnsafe_933_ = lean_ctor_get_uint8(v_modifiers_925_, sizeof(void*)*3 + 4);
v_attrs_934_ = lean_ctor_get(v_modifiers_925_, 2);
v_isSharedCheck_961_ = !lean_is_exclusive(v_modifiers_925_);
if (v_isSharedCheck_961_ == 0)
{
v___x_936_ = v_modifiers_925_;
v_isShared_937_ = v_isSharedCheck_961_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_attrs_934_);
lean_inc(v_docString_x3f_928_);
lean_inc(v_stx_927_);
lean_dec(v_modifiers_925_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_961_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_938_ = lean_unsigned_to_nat(0u);
v___x_939_ = lean_array_get_size(v_attrs_934_);
v___x_940_ = ((lean_object*)(l_Lean_Elab_instInhabitedModifiers_default___closed__0));
v___x_941_ = lean_nat_dec_lt(v___x_938_, v___x_939_);
if (v___x_941_ == 0)
{
lean_object* v___x_943_; 
lean_dec_ref(v_attrs_934_);
lean_dec_ref(v_p_926_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 2, v___x_940_);
v___x_943_ = v___x_936_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_stx_927_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_docString_x3f_928_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v___x_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*3, v_visibility_929_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*3 + 1, v_isProtected_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*3 + 2, v_computeKind_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*3 + 3, v_recKind_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*3 + 4, v_isUnsafe_933_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
else
{
uint8_t v___x_945_; 
v___x_945_ = lean_nat_dec_le(v___x_939_, v___x_939_);
if (v___x_945_ == 0)
{
if (v___x_941_ == 0)
{
lean_object* v___x_947_; 
lean_dec_ref(v_attrs_934_);
lean_dec_ref(v_p_926_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 2, v___x_940_);
v___x_947_ = v___x_936_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_stx_927_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_docString_x3f_928_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v___x_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*3, v_visibility_929_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*3 + 1, v_isProtected_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*3 + 2, v_computeKind_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*3 + 3, v_recKind_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*3 + 4, v_isUnsafe_933_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
else
{
size_t v___x_949_; size_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_949_ = ((size_t)0ULL);
v___x_950_ = lean_usize_of_nat(v___x_939_);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_926_, v_attrs_934_, v___x_949_, v___x_950_, v___x_940_);
lean_dec_ref(v_attrs_934_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 2, v___x_951_);
v___x_953_ = v___x_936_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_stx_927_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_docString_x3f_928_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v___x_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*3, v_visibility_929_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*3 + 1, v_isProtected_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*3 + 2, v_computeKind_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*3 + 3, v_recKind_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*3 + 4, v_isUnsafe_933_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
else
{
size_t v___x_955_; size_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_955_ = ((size_t)0ULL);
v___x_956_ = lean_usize_of_nat(v___x_939_);
v___x_957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_926_, v_attrs_934_, v___x_955_, v___x_956_, v___x_940_);
lean_dec_ref(v_attrs_934_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 2, v___x_957_);
v___x_959_ = v___x_936_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_stx_927_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_docString_x3f_928_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v___x_957_);
lean_ctor_set_uint8(v_reuseFailAlloc_960_, sizeof(void*)*3, v_visibility_929_);
lean_ctor_set_uint8(v_reuseFailAlloc_960_, sizeof(void*)*3 + 1, v_isProtected_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_960_, sizeof(void*)*3 + 2, v_computeKind_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_960_, sizeof(void*)*3 + 3, v_recKind_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_960_, sizeof(void*)*3 + 4, v_isUnsafe_933_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(lean_object* v_p_962_, lean_object* v_as_963_, size_t v_i_964_, size_t v_stop_965_){
_start:
{
uint8_t v___x_966_; 
v___x_966_ = lean_usize_dec_eq(v_i_964_, v_stop_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_967_ = lean_array_uget_borrowed(v_as_963_, v_i_964_);
lean_inc_ref(v_p_962_);
lean_inc(v___x_967_);
v___x_968_ = lean_apply_1(v_p_962_, v___x_967_);
v___x_969_ = lean_unbox(v___x_968_);
if (v___x_969_ == 0)
{
size_t v___x_970_; size_t v___x_971_; 
v___x_970_ = ((size_t)1ULL);
v___x_971_ = lean_usize_add(v_i_964_, v___x_970_);
v_i_964_ = v___x_971_;
goto _start;
}
else
{
uint8_t v___x_973_; 
lean_dec_ref(v_p_962_);
v___x_973_ = lean_unbox(v___x_968_);
return v___x_973_;
}
}
else
{
uint8_t v___x_974_; 
lean_dec_ref(v_p_962_);
v___x_974_ = 0;
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0___boxed(lean_object* v_p_975_, lean_object* v_as_976_, lean_object* v_i_977_, lean_object* v_stop_978_){
_start:
{
size_t v_i_boxed_979_; size_t v_stop_boxed_980_; uint8_t v_res_981_; lean_object* v_r_982_; 
v_i_boxed_979_ = lean_unbox_usize(v_i_977_);
lean_dec(v_i_977_);
v_stop_boxed_980_ = lean_unbox_usize(v_stop_978_);
lean_dec(v_stop_978_);
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_975_, v_as_976_, v_i_boxed_979_, v_stop_boxed_980_);
lean_dec_ref(v_as_976_);
v_r_982_ = lean_box(v_res_981_);
return v_r_982_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_anyAttr(lean_object* v_modifiers_983_, lean_object* v_p_984_){
_start:
{
lean_object* v_attrs_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v_attrs_985_ = lean_ctor_get(v_modifiers_983_, 2);
v___x_986_ = lean_unsigned_to_nat(0u);
v___x_987_ = lean_array_get_size(v_attrs_985_);
v___x_988_ = lean_nat_dec_lt(v___x_986_, v___x_987_);
if (v___x_988_ == 0)
{
lean_dec_ref(v_p_984_);
return v___x_988_;
}
else
{
if (v___x_988_ == 0)
{
lean_dec_ref(v_p_984_);
return v___x_988_;
}
else
{
size_t v___x_989_; size_t v___x_990_; uint8_t v___x_991_; 
v___x_989_ = ((size_t)0ULL);
v___x_990_ = lean_usize_of_nat(v___x_987_);
v___x_991_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_984_, v_attrs_985_, v___x_989_, v___x_990_);
return v___x_991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_anyAttr___boxed(lean_object* v_modifiers_992_, lean_object* v_p_993_){
_start:
{
uint8_t v_res_994_; lean_object* v_r_995_; 
v_res_994_ = l_Lean_Elab_Modifiers_anyAttr(v_modifiers_992_, v_p_993_);
lean_dec_ref(v_modifiers_992_);
v_r_995_ = lean_box(v_res_994_);
return v_r_995_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__0));
v___x_999_ = lean_string_length(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__2, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__2_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2);
v___x_1001_ = lean_nat_to_int(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__0(lean_object* v_attr_1008_){
_start:
{
uint8_t v_kind_1009_; lean_object* v_name_1010_; lean_object* v_stx_1011_; lean_object* v___y_1013_; 
v_kind_1009_ = lean_ctor_get_uint8(v_attr_1008_, sizeof(void*)*2);
v_name_1010_ = lean_ctor_get(v_attr_1008_, 0);
lean_inc(v_name_1010_);
v_stx_1011_ = lean_ctor_get(v_attr_1008_, 1);
lean_inc(v_stx_1011_);
lean_dec_ref(v_attr_1008_);
switch(v_kind_1009_)
{
case 0:
{
lean_object* v___x_1035_; 
v___x_1035_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4));
v___y_1013_ = v___x_1035_;
goto v___jp_1012_;
}
case 1:
{
lean_object* v___x_1036_; 
v___x_1036_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__6));
v___y_1013_ = v___x_1036_;
goto v___jp_1012_;
}
default: 
{
lean_object* v___x_1037_; 
v___x_1037_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__7));
v___y_1013_ = v___x_1037_;
goto v___jp_1012_;
}
}
v___jp_1012_:
{
lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; 
lean_inc_ref(v___y_1013_);
v___x_1014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___y_1013_);
v___x_1015_ = 1;
v___x_1016_ = l_Lean_Name_toString(v_name_1010_, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1014_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_box(0);
v___x_1020_ = 0;
v___x_1021_ = l_Lean_Syntax_formatStx(v_stx_1011_, v___x_1019_, v___x_1020_);
v___x_1022_ = l_Std_Format_defWidth;
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = l_Std_Format_pretty(v___x_1021_, v___x_1022_, v___x_1023_, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1018_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__3, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__3_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3);
v___x_1028_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__4));
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_1026_);
v___x_1030_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__5));
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1027_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = 0;
v___x_1034_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1034_, 0, v___x_1032_);
lean_ctor_set_uint8(v___x_1034_, sizeof(void*)*1, v___x_1033_);
return v___x_1034_;
}
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__0));
v___x_1047_ = lean_string_length(v___x_1046_);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__5, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__5_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5);
v___x_1049_ = lean_nat_to_int(v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__1(lean_object* v___f_1106_, lean_object* v___f_1107_, lean_object* v_m_1108_){
_start:
{
lean_object* v_docString_x3f_1109_; uint8_t v_visibility_1110_; uint8_t v_isProtected_1111_; uint8_t v_computeKind_1112_; uint8_t v_recKind_1113_; uint8_t v_isUnsafe_1114_; lean_object* v_attrs_1115_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1161_; 
v_docString_x3f_1109_ = lean_ctor_get(v_m_1108_, 1);
lean_inc(v_docString_x3f_1109_);
v_visibility_1110_ = lean_ctor_get_uint8(v_m_1108_, sizeof(void*)*3);
v_isProtected_1111_ = lean_ctor_get_uint8(v_m_1108_, sizeof(void*)*3 + 1);
v_computeKind_1112_ = lean_ctor_get_uint8(v_m_1108_, sizeof(void*)*3 + 2);
v_recKind_1113_ = lean_ctor_get_uint8(v_m_1108_, sizeof(void*)*3 + 3);
v_isUnsafe_1114_ = lean_ctor_get_uint8(v_m_1108_, sizeof(void*)*3 + 4);
v_attrs_1115_ = lean_ctor_get(v_m_1108_, 2);
lean_inc_ref(v_attrs_1115_);
lean_dec_ref(v_m_1108_);
if (lean_obj_tag(v_docString_x3f_1109_) == 0)
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_box(0);
v___y_1161_ = v___x_1165_;
goto v___jp_1160_;
}
else
{
lean_object* v_val_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v_val_1166_ = lean_ctor_get(v_docString_x3f_1109_, 0);
lean_inc(v_val_1166_);
lean_dec_ref_known(v_docString_x3f_1109_, 1);
v___x_1167_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__32));
v___x_1168_ = lean_box(0);
v___x_1169_ = 0;
v___x_1170_ = l_Lean_Syntax_formatStx(v_val_1166_, v___x_1168_, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1167_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__34));
v___x_1173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_box(0);
v___x_1175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___y_1161_ = v___x_1175_;
goto v___jp_1160_;
}
v___jp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_components_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; lean_object* v___x_1133_; 
lean_inc(v___y_1118_);
v___x_1119_ = l_List_appendTR___redArg(v___y_1117_, v___y_1118_);
v___x_1120_ = lean_array_to_list(v_attrs_1115_);
v___x_1121_ = lean_box(0);
v___x_1122_ = l_List_mapTR_loop___redArg(v___f_1106_, v___x_1120_, v___x_1121_);
v_components_1123_ = l_List_appendTR___redArg(v___x_1119_, v___x_1122_);
v___x_1124_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__3));
v___x_1125_ = l_Std_Format_joinSep___redArg(v___f_1107_, v_components_1123_, v___x_1124_);
v___x_1126_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__6, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__6_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6);
v___x_1127_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__7));
v___x_1128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v___x_1125_);
v___x_1129_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__8));
v___x_1130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1126_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = 0;
v___x_1133_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set_uint8(v___x_1133_, sizeof(void*)*1, v___x_1132_);
return v___x_1133_;
}
v___jp_1134_:
{
lean_object* v___x_1137_; 
lean_inc(v___y_1136_);
v___x_1137_ = l_List_appendTR___redArg(v___y_1135_, v___y_1136_);
if (v_isUnsafe_1114_ == 0)
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_box(0);
v___y_1117_ = v___x_1137_;
v___y_1118_ = v___x_1138_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1139_; 
v___x_1139_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__11));
v___y_1117_ = v___x_1137_;
v___y_1118_ = v___x_1139_;
goto v___jp_1116_;
}
}
v___jp_1140_:
{
lean_object* v___x_1143_; 
lean_inc(v___y_1142_);
v___x_1143_ = l_List_appendTR___redArg(v___y_1141_, v___y_1142_);
switch(v_recKind_1113_)
{
case 0:
{
lean_object* v___x_1144_; 
v___x_1144_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__14));
v___y_1135_ = v___x_1143_;
v___y_1136_ = v___x_1144_;
goto v___jp_1134_;
}
case 1:
{
lean_object* v___x_1145_; 
v___x_1145_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__17));
v___y_1135_ = v___x_1143_;
v___y_1136_ = v___x_1145_;
goto v___jp_1134_;
}
default: 
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_box(0);
v___y_1135_ = v___x_1143_;
v___y_1136_ = v___x_1146_;
goto v___jp_1134_;
}
}
}
v___jp_1147_:
{
lean_object* v___x_1150_; 
lean_inc(v___y_1149_);
v___x_1150_ = l_List_appendTR___redArg(v___y_1148_, v___y_1149_);
switch(v_computeKind_1112_)
{
case 0:
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_box(0);
v___y_1141_ = v___x_1150_;
v___y_1142_ = v___x_1151_;
goto v___jp_1140_;
}
case 1:
{
lean_object* v___x_1152_; 
v___x_1152_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__20));
v___y_1141_ = v___x_1150_;
v___y_1142_ = v___x_1152_;
goto v___jp_1140_;
}
default: 
{
lean_object* v___x_1153_; 
v___x_1153_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__23));
v___y_1141_ = v___x_1150_;
v___y_1142_ = v___x_1153_;
goto v___jp_1140_;
}
}
}
v___jp_1154_:
{
lean_object* v___x_1157_; 
lean_inc(v___y_1156_);
v___x_1157_ = l_List_appendTR___redArg(v___y_1155_, v___y_1156_);
if (v_isProtected_1111_ == 0)
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_box(0);
v___y_1148_ = v___x_1157_;
v___y_1149_ = v___x_1158_;
goto v___jp_1147_;
}
else
{
lean_object* v___x_1159_; 
v___x_1159_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__26));
v___y_1148_ = v___x_1157_;
v___y_1149_ = v___x_1159_;
goto v___jp_1147_;
}
}
v___jp_1160_:
{
switch(v_visibility_1110_)
{
case 0:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_box(0);
v___y_1155_ = v___y_1161_;
v___y_1156_ = v___x_1162_;
goto v___jp_1154_;
}
case 1:
{
lean_object* v___x_1163_; 
v___x_1163_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__28));
v___y_1155_ = v___y_1161_;
v___y_1156_ = v___x_1163_;
goto v___jp_1154_;
}
default: 
{
lean_object* v___x_1164_; 
v___x_1164_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__30));
v___y_1155_ = v___y_1161_;
v___y_1156_ = v___x_1164_;
goto v___jp_1154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lam__0(lean_object* v_f_1182_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1183_ = l_Std_Format_defWidth;
v___x_1184_ = lean_unsigned_to_nat(0u);
v___x_1185_ = l_Std_Format_pretty(v_f_1182_, v___x_1183_, v___x_1184_, v___x_1184_);
return v___x_1185_;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = ((lean_object*)(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0));
v___x_1193_ = l_Lean_stringToMessageData(v___x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg(lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_optDocComment_1196_){
_start:
{
lean_object* v_toApplicative_1197_; lean_object* v_toPure_1198_; lean_object* v___x_1199_; 
v_toApplicative_1197_ = lean_ctor_get(v_inst_1194_, 0);
v_toPure_1198_ = lean_ctor_get(v_toApplicative_1197_, 1);
v___x_1199_ = l_Lean_Syntax_getOptional_x3f(v_optDocComment_1196_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_inc(v_toPure_1198_);
lean_dec_ref(v_inst_1195_);
lean_dec_ref(v_inst_1194_);
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_apply_2(v_toPure_1198_, lean_box(0), v___x_1200_);
return v___x_1201_;
}
else
{
lean_object* v_val_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1223_; 
v_val_1202_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1204_ = v___x_1199_;
v_isShared_1205_ = v_isSharedCheck_1223_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_val_1202_);
lean_dec(v___x_1199_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1223_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = l_Lean_Syntax_getArg(v_val_1202_, v___x_1206_);
if (lean_obj_tag(v___x_1207_) == 2)
{
lean_object* v_val_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
lean_inc(v_toPure_1198_);
lean_dec(v_val_1202_);
lean_dec_ref(v_inst_1195_);
lean_dec_ref(v_inst_1194_);
v_val_1208_ = lean_ctor_get(v___x_1207_, 1);
lean_inc_ref(v_val_1208_);
lean_dec_ref_known(v___x_1207_, 2);
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = lean_string_utf8_byte_size(v_val_1208_);
v___x_1211_ = lean_unsigned_to_nat(2u);
v___x_1212_ = lean_nat_sub(v___x_1210_, v___x_1211_);
v___x_1213_ = lean_string_utf8_extract(v_val_1208_, v___x_1209_, v___x_1212_);
lean_dec(v___x_1212_);
lean_dec_ref(v_val_1208_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1213_);
v___x_1215_ = v___x_1204_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_apply_2(v_toPure_1198_, lean_box(0), v___x_1215_);
return v___x_1216_;
}
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_del_object(v___x_1204_);
v___x_1218_ = lean_obj_once(&l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1, &l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1_once, _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1);
v___x_1219_ = l_Lean_MessageData_ofSyntax(v___x_1207_);
v___x_1220_ = l_Lean_indentD(v___x_1219_);
v___x_1221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1218_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = l_Lean_throwErrorAt___redArg(v_inst_1194_, v_inst_1195_, v_val_1202_, v___x_1221_);
return v___x_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___boxed(lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_optDocComment_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1224_, v_inst_1225_, v_optDocComment_1226_);
lean_dec(v_optDocComment_1226_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f(lean_object* v_m_1228_, lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_optDocComment_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1229_, v_inst_1230_, v_optDocComment_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___boxed(lean_object* v_m_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_optDocComment_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_Elab_expandOptDocComment_x3f(v_m_1233_, v_inst_1234_, v_inst_1235_, v_optDocComment_1236_);
lean_dec(v_optDocComment_1236_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0(lean_object* v_stx_1238_, lean_object* v___y_1239_, uint8_t v_visibility_1240_, uint8_t v___y_1241_, uint8_t v___y_1242_, uint8_t v___y_1243_, lean_object* v_toPure_1244_, lean_object* v_unsafeStx_1245_, lean_object* v_attrs_1246_){
_start:
{
uint8_t v___y_1248_; uint8_t v___x_1251_; 
v___x_1251_ = l_Lean_Syntax_isNone(v_unsafeStx_1245_);
if (v___x_1251_ == 0)
{
uint8_t v___x_1252_; 
v___x_1252_ = 1;
v___y_1248_ = v___x_1252_;
goto v___jp_1247_;
}
else
{
uint8_t v___x_1253_; 
v___x_1253_ = 0;
v___y_1248_ = v___x_1253_;
goto v___jp_1247_;
}
v___jp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1249_, 0, v_stx_1238_);
lean_ctor_set(v___x_1249_, 1, v___y_1239_);
lean_ctor_set(v___x_1249_, 2, v_attrs_1246_);
lean_ctor_set_uint8(v___x_1249_, sizeof(void*)*3, v_visibility_1240_);
lean_ctor_set_uint8(v___x_1249_, sizeof(void*)*3 + 1, v___y_1241_);
lean_ctor_set_uint8(v___x_1249_, sizeof(void*)*3 + 2, v___y_1242_);
lean_ctor_set_uint8(v___x_1249_, sizeof(void*)*3 + 3, v___y_1243_);
lean_ctor_set_uint8(v___x_1249_, sizeof(void*)*3 + 4, v___y_1248_);
v___x_1250_ = lean_apply_2(v_toPure_1244_, lean_box(0), v___x_1249_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0___boxed(lean_object* v_stx_1254_, lean_object* v___y_1255_, lean_object* v_visibility_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v_toPure_1260_, lean_object* v_unsafeStx_1261_, lean_object* v_attrs_1262_){
_start:
{
uint8_t v_visibility_boxed_1263_; uint8_t v___y_303__boxed_1264_; uint8_t v___y_304__boxed_1265_; uint8_t v___y_305__boxed_1266_; lean_object* v_res_1267_; 
v_visibility_boxed_1263_ = lean_unbox(v_visibility_1256_);
v___y_303__boxed_1264_ = lean_unbox(v___y_1257_);
v___y_304__boxed_1265_ = lean_unbox(v___y_1258_);
v___y_305__boxed_1266_ = lean_unbox(v___y_1259_);
v_res_1267_ = l_Lean_Elab_elabModifiers___redArg___lam__0(v_stx_1254_, v___y_1255_, v_visibility_boxed_1263_, v___y_303__boxed_1264_, v___y_304__boxed_1265_, v___y_305__boxed_1266_, v_toPure_1260_, v_unsafeStx_1261_, v_attrs_1262_);
lean_dec(v_unsafeStx_1261_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__1(lean_object* v___f_1268_, lean_object* v_attrs_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_apply_1(v___f_1268_, v_attrs_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3(lean_object* v_stx_1271_, lean_object* v___y_1272_, uint8_t v___y_1273_, uint8_t v___y_1274_, lean_object* v_toPure_1275_, lean_object* v_unsafeStx_1276_, lean_object* v_attrsStx_1277_, lean_object* v___x_1278_, lean_object* v_toBind_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_protectedStx_1292_, uint8_t v_visibility_1293_){
_start:
{
uint8_t v___y_1295_; uint8_t v___x_1310_; 
v___x_1310_ = l_Lean_Syntax_isNone(v_protectedStx_1292_);
if (v___x_1310_ == 0)
{
uint8_t v___x_1311_; 
v___x_1311_ = 1;
v___y_1295_ = v___x_1311_;
goto v___jp_1294_;
}
else
{
uint8_t v___x_1312_; 
v___x_1312_ = 0;
v___y_1295_ = v___x_1312_;
goto v___jp_1294_;
}
v___jp_1294_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___f_1300_; lean_object* v___x_1301_; 
v___x_1296_ = lean_box(v_visibility_1293_);
v___x_1297_ = lean_box(v___y_1295_);
v___x_1298_ = lean_box(v___y_1273_);
v___x_1299_ = lean_box(v___y_1274_);
lean_inc(v_toPure_1275_);
v___f_1300_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_1300_, 0, v_stx_1271_);
lean_closure_set(v___f_1300_, 1, v___y_1272_);
lean_closure_set(v___f_1300_, 2, v___x_1296_);
lean_closure_set(v___f_1300_, 3, v___x_1297_);
lean_closure_set(v___f_1300_, 4, v___x_1298_);
lean_closure_set(v___f_1300_, 5, v___x_1299_);
lean_closure_set(v___f_1300_, 6, v_toPure_1275_);
lean_closure_set(v___f_1300_, 7, v_unsafeStx_1276_);
v___x_1301_ = l_Lean_Syntax_getOptional_x3f(v_attrsStx_1277_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v___f_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec(v_inst_1291_);
lean_dec(v_inst_1290_);
lean_dec_ref(v_inst_1289_);
lean_dec(v_inst_1288_);
lean_dec(v_inst_1287_);
lean_dec_ref(v_inst_1286_);
lean_dec_ref(v_inst_1285_);
lean_dec_ref(v_inst_1284_);
lean_dec_ref(v_inst_1283_);
lean_dec_ref(v_inst_1282_);
lean_dec_ref(v_inst_1281_);
lean_dec_ref(v_inst_1280_);
v___f_1302_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1302_, 0, v___f_1300_);
v___x_1303_ = lean_mk_empty_array_with_capacity(v___x_1278_);
v___x_1304_ = lean_apply_2(v_toPure_1275_, lean_box(0), v___x_1303_);
v___x_1305_ = lean_apply_4(v_toBind_1279_, lean_box(0), lean_box(0), v___x_1304_, v___f_1302_);
return v___x_1305_;
}
else
{
lean_object* v_val_1306_; lean_object* v___f_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_dec(v_toPure_1275_);
v_val_1306_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_val_1306_);
lean_dec_ref_known(v___x_1301_, 1);
v___f_1307_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1307_, 0, v___f_1300_);
v___x_1308_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_1280_, v_inst_1281_, v_inst_1282_, v_inst_1283_, v_inst_1284_, v_inst_1285_, v_inst_1286_, v_inst_1287_, v_inst_1288_, v_inst_1289_, v_inst_1290_, v_inst_1291_, v_val_1306_);
lean_dec(v_val_1306_);
v___x_1309_ = lean_apply_4(v_toBind_1279_, lean_box(0), lean_box(0), v___x_1308_, v___f_1307_);
return v___x_1309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_stx_1313_ = _args[0];
lean_object* v___y_1314_ = _args[1];
lean_object* v___y_1315_ = _args[2];
lean_object* v___y_1316_ = _args[3];
lean_object* v_toPure_1317_ = _args[4];
lean_object* v_unsafeStx_1318_ = _args[5];
lean_object* v_attrsStx_1319_ = _args[6];
lean_object* v___x_1320_ = _args[7];
lean_object* v_toBind_1321_ = _args[8];
lean_object* v_inst_1322_ = _args[9];
lean_object* v_inst_1323_ = _args[10];
lean_object* v_inst_1324_ = _args[11];
lean_object* v_inst_1325_ = _args[12];
lean_object* v_inst_1326_ = _args[13];
lean_object* v_inst_1327_ = _args[14];
lean_object* v_inst_1328_ = _args[15];
lean_object* v_inst_1329_ = _args[16];
lean_object* v_inst_1330_ = _args[17];
lean_object* v_inst_1331_ = _args[18];
lean_object* v_inst_1332_ = _args[19];
lean_object* v_inst_1333_ = _args[20];
lean_object* v_protectedStx_1334_ = _args[21];
lean_object* v_visibility_1335_ = _args[22];
_start:
{
uint8_t v___y_333__boxed_1336_; uint8_t v___y_334__boxed_1337_; uint8_t v_visibility_boxed_1338_; lean_object* v_res_1339_; 
v___y_333__boxed_1336_ = lean_unbox(v___y_1315_);
v___y_334__boxed_1337_ = lean_unbox(v___y_1316_);
v_visibility_boxed_1338_ = lean_unbox(v_visibility_1335_);
v_res_1339_ = l_Lean_Elab_elabModifiers___redArg___lam__3(v_stx_1313_, v___y_1314_, v___y_333__boxed_1336_, v___y_334__boxed_1337_, v_toPure_1317_, v_unsafeStx_1318_, v_attrsStx_1319_, v___x_1320_, v_toBind_1321_, v_inst_1322_, v_inst_1323_, v_inst_1324_, v_inst_1325_, v_inst_1326_, v_inst_1327_, v_inst_1328_, v_inst_1329_, v_inst_1330_, v_inst_1331_, v_inst_1332_, v_inst_1333_, v_protectedStx_1334_, v_visibility_boxed_1338_);
lean_dec(v_protectedStx_1334_);
lean_dec(v___x_1320_);
lean_dec(v_attrsStx_1319_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg(lean_object* v_inst_1350_, lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_inst_1361_, lean_object* v_stx_1362_){
_start:
{
lean_object* v_toApplicative_1363_; lean_object* v_toBind_1364_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v_toPure_1370_; lean_object* v___x_1371_; lean_object* v_docCommentStx_1372_; lean_object* v___x_1373_; lean_object* v_attrsStx_1374_; lean_object* v___x_1375_; lean_object* v_visibilityStx_1376_; lean_object* v___x_1377_; lean_object* v_protectedStx_1378_; uint8_t v___y_1380_; lean_object* v___y_1381_; uint8_t v___y_1382_; lean_object* v___y_1383_; uint8_t v___y_1398_; lean_object* v___y_1399_; uint8_t v___y_1400_; uint8_t v___y_1412_; lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v_toApplicative_1363_ = lean_ctor_get(v_inst_1350_, 0);
v_toBind_1364_ = lean_ctor_get(v_inst_1350_, 1);
lean_inc(v_toBind_1364_);
v_toPure_1370_ = lean_ctor_get(v_toApplicative_1363_, 1);
v___x_1371_ = lean_unsigned_to_nat(0u);
v_docCommentStx_1372_ = l_Lean_Syntax_getArg(v_stx_1362_, v___x_1371_);
v___x_1373_ = lean_unsigned_to_nat(1u);
v_attrsStx_1374_ = l_Lean_Syntax_getArg(v_stx_1362_, v___x_1373_);
v___x_1375_ = lean_unsigned_to_nat(2u);
v_visibilityStx_1376_ = l_Lean_Syntax_getArg(v_stx_1362_, v___x_1375_);
v___x_1377_ = lean_unsigned_to_nat(3u);
v_protectedStx_1378_ = l_Lean_Syntax_getArg(v_stx_1362_, v___x_1377_);
v___x_1425_ = lean_unsigned_to_nat(4u);
v___x_1426_ = l_Lean_Syntax_getArg(v_stx_1362_, v___x_1425_);
v___x_1427_ = l_Lean_Syntax_isNone(v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1428_ = l_Lean_Syntax_getArg(v___x_1426_, v___x_1371_);
lean_dec(v___x_1426_);
v___x_1429_ = l_Lean_Syntax_getKind(v___x_1428_);
v___x_1430_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__1));
v___x_1431_ = lean_name_eq(v___x_1429_, v___x_1430_);
lean_dec(v___x_1429_);
if (v___x_1431_ == 0)
{
uint8_t v___x_1432_; 
v___x_1432_ = 2;
v___y_1412_ = v___x_1432_;
goto v___jp_1411_;
}
else
{
uint8_t v___x_1433_; 
v___x_1433_ = 1;
v___y_1412_ = v___x_1433_;
goto v___jp_1411_;
}
}
else
{
uint8_t v___x_1434_; 
lean_dec(v___x_1426_);
v___x_1434_ = 0;
v___y_1412_ = v___x_1434_;
goto v___jp_1411_;
}
v___jp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = l_Lean_Elab_elabVisibility___redArg(v_inst_1350_, v_inst_1353_, v_inst_1351_, v_inst_1358_, v_inst_1360_, v_inst_1359_, v___y_1367_);
v___x_1369_ = lean_apply_4(v_toBind_1364_, lean_box(0), lean_box(0), v___x_1368_, v___y_1366_);
return v___x_1369_;
}
v___jp_1379_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___f_1386_; lean_object* v___x_1387_; 
v___x_1384_ = lean_box(v___y_1382_);
v___x_1385_ = lean_box(v___y_1380_);
lean_inc_ref(v_inst_1360_);
lean_inc(v_inst_1359_);
lean_inc(v_inst_1358_);
lean_inc_ref(v_inst_1353_);
lean_inc_ref(v_inst_1351_);
lean_inc_ref(v_inst_1350_);
lean_inc(v_toBind_1364_);
lean_inc(v_toPure_1370_);
v___f_1386_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__3___boxed), 23, 22);
lean_closure_set(v___f_1386_, 0, v_stx_1362_);
lean_closure_set(v___f_1386_, 1, v___y_1383_);
lean_closure_set(v___f_1386_, 2, v___x_1384_);
lean_closure_set(v___f_1386_, 3, v___x_1385_);
lean_closure_set(v___f_1386_, 4, v_toPure_1370_);
lean_closure_set(v___f_1386_, 5, v___y_1381_);
lean_closure_set(v___f_1386_, 6, v_attrsStx_1374_);
lean_closure_set(v___f_1386_, 7, v___x_1371_);
lean_closure_set(v___f_1386_, 8, v_toBind_1364_);
lean_closure_set(v___f_1386_, 9, v_inst_1350_);
lean_closure_set(v___f_1386_, 10, v_inst_1351_);
lean_closure_set(v___f_1386_, 11, v_inst_1352_);
lean_closure_set(v___f_1386_, 12, v_inst_1353_);
lean_closure_set(v___f_1386_, 13, v_inst_1355_);
lean_closure_set(v___f_1386_, 14, v_inst_1356_);
lean_closure_set(v___f_1386_, 15, v_inst_1357_);
lean_closure_set(v___f_1386_, 16, v_inst_1358_);
lean_closure_set(v___f_1386_, 17, v_inst_1359_);
lean_closure_set(v___f_1386_, 18, v_inst_1360_);
lean_closure_set(v___f_1386_, 19, v_inst_1361_);
lean_closure_set(v___f_1386_, 20, v_inst_1354_);
lean_closure_set(v___f_1386_, 21, v_protectedStx_1378_);
v___x_1387_ = l_Lean_Syntax_getOptional_x3f(v_visibilityStx_1376_);
lean_dec(v_visibilityStx_1376_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_box(0);
v___y_1366_ = v___f_1386_;
v___y_1367_ = v___x_1388_;
goto v___jp_1365_;
}
else
{
lean_object* v_val_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
v_val_1389_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1387_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_val_1389_);
lean_dec(v___x_1387_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_val_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
v___y_1366_ = v___f_1386_;
v___y_1367_ = v___x_1394_;
goto v___jp_1365_;
}
}
}
}
v___jp_1397_:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_Syntax_getOptional_x3f(v_docCommentStx_1372_);
lean_dec(v_docCommentStx_1372_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_box(0);
v___y_1380_ = v___y_1400_;
v___y_1381_ = v___y_1399_;
v___y_1382_ = v___y_1398_;
v___y_1383_ = v___x_1402_;
goto v___jp_1379_;
}
else
{
lean_object* v_val_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_val_1403_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1401_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_val_1403_);
lean_dec(v___x_1401_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_val_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
v___y_1380_ = v___y_1400_;
v___y_1381_ = v___y_1399_;
v___y_1382_ = v___y_1398_;
v___y_1383_ = v___x_1408_;
goto v___jp_1379_;
}
}
}
}
v___jp_1411_:
{
lean_object* v___x_1413_; lean_object* v_unsafeStx_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1413_ = lean_unsigned_to_nat(5u);
v_unsafeStx_1414_ = l_Lean_Syntax_getArg(v_stx_1362_, v___x_1413_);
v___x_1415_ = lean_unsigned_to_nat(6u);
v___x_1416_ = l_Lean_Syntax_getArg(v_stx_1362_, v___x_1415_);
v___x_1417_ = l_Lean_Syntax_isNone(v___x_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1418_ = l_Lean_Syntax_getArg(v___x_1416_, v___x_1371_);
lean_dec(v___x_1416_);
v___x_1419_ = l_Lean_Syntax_getKind(v___x_1418_);
v___x_1420_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__0));
v___x_1421_ = lean_name_eq(v___x_1419_, v___x_1420_);
lean_dec(v___x_1419_);
if (v___x_1421_ == 0)
{
uint8_t v___x_1422_; 
v___x_1422_ = 1;
v___y_1398_ = v___y_1412_;
v___y_1399_ = v_unsafeStx_1414_;
v___y_1400_ = v___x_1422_;
goto v___jp_1397_;
}
else
{
uint8_t v___x_1423_; 
v___x_1423_ = 0;
v___y_1398_ = v___y_1412_;
v___y_1399_ = v_unsafeStx_1414_;
v___y_1400_ = v___x_1423_;
goto v___jp_1397_;
}
}
else
{
uint8_t v___x_1424_; 
lean_dec(v___x_1416_);
v___x_1424_ = 2;
v___y_1398_ = v___y_1412_;
v___y_1399_ = v_unsafeStx_1414_;
v___y_1400_ = v___x_1424_;
goto v___jp_1397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object* v_m_1435_, lean_object* v_inst_1436_, lean_object* v_inst_1437_, lean_object* v_inst_1438_, lean_object* v_inst_1439_, lean_object* v_inst_1440_, lean_object* v_inst_1441_, lean_object* v_inst_1442_, lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_inst_1445_, lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_stx_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_Elab_elabModifiers___redArg(v_inst_1436_, v_inst_1437_, v_inst_1438_, v_inst_1439_, v_inst_1440_, v_inst_1441_, v_inst_1442_, v_inst_1443_, v_inst_1444_, v_inst_1445_, v_inst_1446_, v_inst_1447_, v_stx_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__0(lean_object* v_toPure_1450_, lean_object* v_declName_1451_, lean_object* v_____r_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_apply_2(v_toPure_1450_, lean_box(0), v_declName_1451_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__1(lean_object* v_declName_1454_, lean_object* v_env_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_addProtected(v_env_1455_, v_declName_1454_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2(lean_object* v_modifiers_1457_, lean_object* v_toPure_1458_, lean_object* v_declName_1459_, lean_object* v_modifyEnv_1460_, lean_object* v___f_1461_, lean_object* v_toBind_1462_, lean_object* v___f_1463_, lean_object* v_____r_1464_){
_start:
{
uint8_t v_isProtected_1465_; 
v_isProtected_1465_ = lean_ctor_get_uint8(v_modifiers_1457_, sizeof(void*)*3 + 1);
if (v_isProtected_1465_ == 0)
{
lean_object* v___x_1466_; 
lean_dec(v___f_1463_);
lean_dec(v_toBind_1462_);
lean_dec_ref(v___f_1461_);
lean_dec(v_modifyEnv_1460_);
v___x_1466_ = lean_apply_2(v_toPure_1458_, lean_box(0), v_declName_1459_);
return v___x_1466_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_dec(v_declName_1459_);
lean_dec(v_toPure_1458_);
v___x_1467_ = lean_apply_1(v_modifyEnv_1460_, v___f_1461_);
v___x_1468_ = lean_apply_4(v_toBind_1462_, lean_box(0), lean_box(0), v___x_1467_, v___f_1463_);
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2___boxed(lean_object* v_modifiers_1469_, lean_object* v_toPure_1470_, lean_object* v_declName_1471_, lean_object* v_modifyEnv_1472_, lean_object* v___f_1473_, lean_object* v_toBind_1474_, lean_object* v___f_1475_, lean_object* v_____r_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Elab_applyVisibility___redArg___lam__2(v_modifiers_1469_, v_toPure_1470_, v_declName_1471_, v_modifyEnv_1472_, v___f_1473_, v_toBind_1474_, v___f_1475_, v_____r_1476_);
lean_dec_ref(v_modifiers_1469_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__3(lean_object* v_toPure_1478_, lean_object* v_modifiers_1479_, lean_object* v_modifyEnv_1480_, lean_object* v_toBind_1481_, lean_object* v_inst_1482_, lean_object* v_inst_1483_, lean_object* v_inst_1484_, lean_object* v_inst_1485_, lean_object* v_inst_1486_, lean_object* v_____r_1487_, lean_object* v_declName_1488_){
_start:
{
lean_object* v___f_1489_; lean_object* v___f_1490_; lean_object* v___f_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_inc_n(v_declName_1488_, 3);
lean_inc(v_toPure_1478_);
v___f_1489_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1489_, 0, v_toPure_1478_);
lean_closure_set(v___f_1489_, 1, v_declName_1488_);
v___f_1490_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1490_, 0, v_declName_1488_);
lean_inc(v_toBind_1481_);
v___f_1491_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1491_, 0, v_modifiers_1479_);
lean_closure_set(v___f_1491_, 1, v_toPure_1478_);
lean_closure_set(v___f_1491_, 2, v_declName_1488_);
lean_closure_set(v___f_1491_, 3, v_modifyEnv_1480_);
lean_closure_set(v___f_1491_, 4, v___f_1490_);
lean_closure_set(v___f_1491_, 5, v_toBind_1481_);
lean_closure_set(v___f_1491_, 6, v___f_1489_);
v___x_1492_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(v_inst_1482_, v_inst_1483_, v_inst_1484_, v_inst_1485_, v_inst_1486_, v_declName_1488_);
v___x_1493_ = lean_apply_4(v_toBind_1481_, lean_box(0), lean_box(0), v___x_1492_, v___f_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4(lean_object* v_declName_1494_, lean_object* v___f_1495_, lean_object* v_____do__lift_1496_){
_start:
{
lean_object* v_declName_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_declName_1497_ = l_Lean_mkPrivateName(v_____do__lift_1496_, v_declName_1494_);
v___x_1498_ = lean_box(0);
v___x_1499_ = lean_apply_2(v___f_1495_, v___x_1498_, v_declName_1497_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4___boxed(lean_object* v_declName_1500_, lean_object* v___f_1501_, lean_object* v_____do__lift_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Elab_applyVisibility___redArg___lam__4(v_declName_1500_, v___f_1501_, v_____do__lift_1502_);
lean_dec_ref(v_____do__lift_1502_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5(lean_object* v_modifiers_1504_, lean_object* v_toBind_1505_, lean_object* v_getEnv_1506_, lean_object* v___f_1507_, lean_object* v___f_1508_, lean_object* v_declName_1509_, lean_object* v_____do__lift_1510_){
_start:
{
uint8_t v_visibility_1511_; uint8_t v___x_1512_; 
v_visibility_1511_ = lean_ctor_get_uint8(v_modifiers_1504_, sizeof(void*)*3);
v___x_1512_ = l_Lean_Elab_Visibility_isInferredPublic(v_____do__lift_1510_, v_visibility_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; 
lean_dec(v_declName_1509_);
lean_dec(v___f_1508_);
v___x_1513_ = lean_apply_4(v_toBind_1505_, lean_box(0), lean_box(0), v_getEnv_1506_, v___f_1507_);
return v___x_1513_;
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec(v___f_1507_);
lean_dec(v_getEnv_1506_);
lean_dec(v_toBind_1505_);
v___x_1514_ = lean_box(0);
v___x_1515_ = lean_apply_2(v___f_1508_, v___x_1514_, v_declName_1509_);
return v___x_1515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5___boxed(lean_object* v_modifiers_1516_, lean_object* v_toBind_1517_, lean_object* v_getEnv_1518_, lean_object* v___f_1519_, lean_object* v___f_1520_, lean_object* v_declName_1521_, lean_object* v_____do__lift_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Elab_applyVisibility___redArg___lam__5(v_modifiers_1516_, v_toBind_1517_, v_getEnv_1518_, v___f_1519_, v___f_1520_, v_declName_1521_, v_____do__lift_1522_);
lean_dec_ref(v_____do__lift_1522_);
lean_dec_ref(v_modifiers_1516_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg(lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_modifiers_1529_, lean_object* v_declName_1530_){
_start:
{
lean_object* v_toApplicative_1531_; lean_object* v_toBind_1532_; lean_object* v_getEnv_1533_; lean_object* v_modifyEnv_1534_; lean_object* v_toPure_1535_; lean_object* v___f_1536_; lean_object* v___f_1537_; lean_object* v___f_1538_; lean_object* v___x_1539_; 
v_toApplicative_1531_ = lean_ctor_get(v_inst_1524_, 0);
v_toBind_1532_ = lean_ctor_get(v_inst_1524_, 1);
lean_inc_n(v_toBind_1532_, 3);
v_getEnv_1533_ = lean_ctor_get(v_inst_1525_, 0);
lean_inc_n(v_getEnv_1533_, 2);
v_modifyEnv_1534_ = lean_ctor_get(v_inst_1525_, 1);
lean_inc(v_modifyEnv_1534_);
v_toPure_1535_ = lean_ctor_get(v_toApplicative_1531_, 1);
lean_inc(v_toPure_1535_);
lean_inc_ref(v_modifiers_1529_);
v___f_1536_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__3), 11, 9);
lean_closure_set(v___f_1536_, 0, v_toPure_1535_);
lean_closure_set(v___f_1536_, 1, v_modifiers_1529_);
lean_closure_set(v___f_1536_, 2, v_modifyEnv_1534_);
lean_closure_set(v___f_1536_, 3, v_toBind_1532_);
lean_closure_set(v___f_1536_, 4, v_inst_1524_);
lean_closure_set(v___f_1536_, 5, v_inst_1525_);
lean_closure_set(v___f_1536_, 6, v_inst_1526_);
lean_closure_set(v___f_1536_, 7, v_inst_1527_);
lean_closure_set(v___f_1536_, 8, v_inst_1528_);
lean_inc_ref(v___f_1536_);
lean_inc(v_declName_1530_);
v___f_1537_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_1537_, 0, v_declName_1530_);
lean_closure_set(v___f_1537_, 1, v___f_1536_);
v___f_1538_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1538_, 0, v_modifiers_1529_);
lean_closure_set(v___f_1538_, 1, v_toBind_1532_);
lean_closure_set(v___f_1538_, 2, v_getEnv_1533_);
lean_closure_set(v___f_1538_, 3, v___f_1537_);
lean_closure_set(v___f_1538_, 4, v___f_1536_);
lean_closure_set(v___f_1538_, 5, v_declName_1530_);
v___x_1539_ = lean_apply_4(v_toBind_1532_, lean_box(0), lean_box(0), v_getEnv_1533_, v___f_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility(lean_object* v_m_1540_, lean_object* v_inst_1541_, lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_inst_1544_, lean_object* v_inst_1545_, lean_object* v_modifiers_1546_, lean_object* v_declName_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1541_, v_inst_1542_, v_inst_1543_, v_inst_1544_, v_inst_1545_, v_modifiers_1546_, v_declName_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0(lean_object* v_toPure_1549_, lean_object* v_____s_1550_){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_box(0);
v___x_1552_ = lean_apply_2(v_toPure_1549_, lean_box(0), v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1(lean_object* v___x_1553_, lean_object* v_toPure_1554_, lean_object* v_r_1555_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1553_);
v___x_1557_ = lean_apply_2(v_toPure_1554_, lean_box(0), v___x_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0));
v___x_1560_ = l_Lean_stringToMessageData(v___x_1559_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2));
v___x_1563_ = l_Lean_stringToMessageData(v___x_1562_);
return v___x_1563_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4));
v___x_1566_ = l_Lean_stringToMessageData(v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2(lean_object* v_pre_1567_, lean_object* v_declName_1568_, lean_object* v___x_1569_, lean_object* v_toPure_1570_, lean_object* v_inst_1571_, lean_object* v_inst_1572_, lean_object* v_toBind_1573_, lean_object* v___f_1574_, lean_object* v_a_1575_, lean_object* v_x_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1578_; uint8_t v___x_1579_; 
lean_inc(v_a_1575_);
lean_inc(v_pre_1567_);
v___x_1578_ = l_Lean_Name_append(v_pre_1567_, v_a_1575_);
v___x_1579_ = lean_name_eq(v___x_1578_, v_declName_1568_);
lean_dec(v___x_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_dec(v_a_1575_);
lean_dec(v___f_1574_);
lean_dec(v_toBind_1573_);
lean_dec_ref(v_inst_1572_);
lean_dec_ref(v_inst_1571_);
lean_dec(v_declName_1568_);
lean_dec(v_pre_1567_);
v___x_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1569_);
v___x_1581_ = lean_apply_2(v_toPure_1570_, lean_box(0), v___x_1580_);
return v___x_1581_;
}
else
{
lean_object* v___x_1582_; uint8_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec(v_toPure_1570_);
v___x_1582_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1583_ = 0;
v___x_1584_ = l_Lean_MessageData_ofConstName(v_declName_1568_, v___x_1583_);
v___x_1585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1582_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = l_Lean_MessageData_ofName(v_pre_1567_);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = l_Lean_MessageData_ofName(v_a_1575_);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = l_Lean_throwError___redArg(v_inst_1571_, v_inst_1572_, v___x_1595_);
v___x_1597_ = lean_apply_4(v_toBind_1573_, lean_box(0), lean_box(0), v___x_1596_, v___f_1574_);
return v___x_1597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(lean_object* v_pre_1598_, uint8_t v___x_1599_, lean_object* v_toPure_1600_, lean_object* v_declName_1601_, lean_object* v_inst_1602_, lean_object* v_inst_1603_, lean_object* v_toBind_1604_, lean_object* v___f_1605_, lean_object* v_____do__lift_1606_){
_start:
{
lean_object* v_fieldNames_1607_; lean_object* v___x_1608_; lean_object* v___f_1609_; lean_object* v___f_1610_; size_t v_sz_1611_; size_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_inc(v_pre_1598_);
v_fieldNames_1607_ = l_Lean_getStructureFieldsFlattened(v_____do__lift_1606_, v_pre_1598_, v___x_1599_);
v___x_1608_ = lean_box(0);
lean_inc(v_toPure_1600_);
v___f_1609_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1609_, 0, v___x_1608_);
lean_closure_set(v___f_1609_, 1, v_toPure_1600_);
lean_inc(v_toBind_1604_);
lean_inc_ref(v_inst_1602_);
v___f_1610_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2), 11, 8);
lean_closure_set(v___f_1610_, 0, v_pre_1598_);
lean_closure_set(v___f_1610_, 1, v_declName_1601_);
lean_closure_set(v___f_1610_, 2, v___x_1608_);
lean_closure_set(v___f_1610_, 3, v_toPure_1600_);
lean_closure_set(v___f_1610_, 4, v_inst_1602_);
lean_closure_set(v___f_1610_, 5, v_inst_1603_);
lean_closure_set(v___f_1610_, 6, v_toBind_1604_);
lean_closure_set(v___f_1610_, 7, v___f_1609_);
v_sz_1611_ = lean_array_size(v_fieldNames_1607_);
v___x_1612_ = ((size_t)0ULL);
v___x_1613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1602_, v_fieldNames_1607_, v___f_1610_, v_sz_1611_, v___x_1612_, v___x_1608_);
v___x_1614_ = lean_apply_4(v_toBind_1604_, lean_box(0), lean_box(0), v___x_1613_, v___f_1605_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed(lean_object* v_pre_1615_, lean_object* v___x_1616_, lean_object* v_toPure_1617_, lean_object* v_declName_1618_, lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v_toBind_1621_, lean_object* v___f_1622_, lean_object* v_____do__lift_1623_){
_start:
{
uint8_t v___x_468__boxed_1624_; lean_object* v_res_1625_; 
v___x_468__boxed_1624_ = lean_unbox(v___x_1616_);
v_res_1625_ = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(v_pre_1615_, v___x_468__boxed_1624_, v_toPure_1617_, v_declName_1618_, v_inst_1619_, v_inst_1620_, v_toBind_1621_, v___f_1622_, v_____do__lift_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4(lean_object* v_pre_1626_, lean_object* v_toPure_1627_, lean_object* v_declName_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v_toBind_1631_, lean_object* v___f_1632_, lean_object* v_getEnv_1633_, lean_object* v_____do__lift_1634_){
_start:
{
uint8_t v___x_1635_; 
lean_inc(v_pre_1626_);
v___x_1635_ = l_Lean_isStructure(v_____do__lift_1634_, v_pre_1626_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec(v_getEnv_1633_);
lean_dec(v___f_1632_);
lean_dec(v_toBind_1631_);
lean_dec_ref(v_inst_1630_);
lean_dec_ref(v_inst_1629_);
lean_dec(v_declName_1628_);
lean_dec(v_pre_1626_);
v___x_1636_ = lean_box(0);
v___x_1637_ = lean_apply_2(v_toPure_1627_, lean_box(0), v___x_1636_);
return v___x_1637_;
}
else
{
lean_object* v___x_1638_; lean_object* v___f_1639_; lean_object* v___x_1640_; 
v___x_1638_ = lean_box(v___x_1635_);
lean_inc(v_toBind_1631_);
v___f_1639_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1639_, 0, v_pre_1626_);
lean_closure_set(v___f_1639_, 1, v___x_1638_);
lean_closure_set(v___f_1639_, 2, v_toPure_1627_);
lean_closure_set(v___f_1639_, 3, v_declName_1628_);
lean_closure_set(v___f_1639_, 4, v_inst_1629_);
lean_closure_set(v___f_1639_, 5, v_inst_1630_);
lean_closure_set(v___f_1639_, 6, v_toBind_1631_);
lean_closure_set(v___f_1639_, 7, v___f_1632_);
v___x_1640_ = lean_apply_4(v_toBind_1631_, lean_box(0), lean_box(0), v_getEnv_1633_, v___f_1639_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg(lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_declName_1644_){
_start:
{
if (lean_obj_tag(v_declName_1644_) == 1)
{
lean_object* v_toApplicative_1645_; lean_object* v_toBind_1646_; lean_object* v_toPure_1647_; lean_object* v_pre_1648_; lean_object* v_getEnv_1649_; lean_object* v___f_1650_; lean_object* v___f_1651_; lean_object* v___x_1652_; 
v_toApplicative_1645_ = lean_ctor_get(v_inst_1641_, 0);
v_toBind_1646_ = lean_ctor_get(v_inst_1641_, 1);
lean_inc_n(v_toBind_1646_, 2);
v_toPure_1647_ = lean_ctor_get(v_toApplicative_1645_, 1);
lean_inc_n(v_toPure_1647_, 2);
v_pre_1648_ = lean_ctor_get(v_declName_1644_, 0);
lean_inc(v_pre_1648_);
v_getEnv_1649_ = lean_ctor_get(v_inst_1642_, 0);
lean_inc_n(v_getEnv_1649_, 2);
lean_dec_ref(v_inst_1642_);
v___f_1650_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1650_, 0, v_toPure_1647_);
v___f_1651_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1651_, 0, v_pre_1648_);
lean_closure_set(v___f_1651_, 1, v_toPure_1647_);
lean_closure_set(v___f_1651_, 2, v_declName_1644_);
lean_closure_set(v___f_1651_, 3, v_inst_1641_);
lean_closure_set(v___f_1651_, 4, v_inst_1643_);
lean_closure_set(v___f_1651_, 5, v_toBind_1646_);
lean_closure_set(v___f_1651_, 6, v___f_1650_);
lean_closure_set(v___f_1651_, 7, v_getEnv_1649_);
v___x_1652_ = lean_apply_4(v_toBind_1646_, lean_box(0), lean_box(0), v_getEnv_1649_, v___f_1651_);
return v___x_1652_;
}
else
{
lean_object* v_toApplicative_1653_; lean_object* v_toPure_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_toApplicative_1653_ = lean_ctor_get(v_inst_1641_, 0);
lean_inc_ref(v_toApplicative_1653_);
lean_dec(v_declName_1644_);
lean_dec_ref(v_inst_1643_);
lean_dec_ref(v_inst_1642_);
lean_dec_ref(v_inst_1641_);
v_toPure_1654_ = lean_ctor_get(v_toApplicative_1653_, 1);
lean_inc(v_toPure_1654_);
lean_dec_ref(v_toApplicative_1653_);
v___x_1655_ = lean_box(0);
v___x_1656_ = lean_apply_2(v_toPure_1654_, lean_box(0), v___x_1655_);
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField(lean_object* v_m_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_declName_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1658_, v_inst_1659_, v_inst_1660_, v_declName_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__0(lean_object* v_declName_1663_, lean_object* v_shortName_1664_, lean_object* v_toPure_1665_, lean_object* v_____r_1666_){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v_declName_1663_);
lean_ctor_set(v___x_1667_, 1, v_shortName_1664_);
v___x_1668_ = lean_apply_2(v_toPure_1665_, lean_box(0), v___x_1667_);
return v___x_1668_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0));
v___x_1671_ = l_Lean_stringToMessageData(v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2(lean_object* v_modifiers_1672_, lean_object* v_shortName_1673_, lean_object* v_toPure_1674_, lean_object* v_currNamespace_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_toBind_1678_, lean_object* v_declName_1679_){
_start:
{
uint8_t v_isProtected_1680_; 
v_isProtected_1680_ = lean_ctor_get_uint8(v_modifiers_1672_, sizeof(void*)*3 + 1);
if (v_isProtected_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_dec(v_toBind_1678_);
lean_dec_ref(v_inst_1677_);
lean_dec_ref(v_inst_1676_);
lean_dec(v_currNamespace_1675_);
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v_declName_1679_);
lean_ctor_set(v___x_1681_, 1, v_shortName_1673_);
v___x_1682_ = lean_apply_2(v_toPure_1674_, lean_box(0), v___x_1681_);
return v___x_1682_;
}
else
{
if (lean_obj_tag(v_currNamespace_1675_) == 1)
{
lean_object* v_str_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec(v_toBind_1678_);
lean_dec_ref(v_inst_1677_);
lean_dec_ref(v_inst_1676_);
v_str_1683_ = lean_ctor_get(v_currNamespace_1675_, 1);
lean_inc_ref(v_str_1683_);
lean_dec_ref_known(v_currNamespace_1675_, 2);
v___x_1684_ = lean_box(0);
v___x_1685_ = l_Lean_Name_str___override(v___x_1684_, v_str_1683_);
v___x_1686_ = l_Lean_Name_append(v___x_1685_, v_shortName_1673_);
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v_declName_1679_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = lean_apply_2(v_toPure_1674_, lean_box(0), v___x_1687_);
return v___x_1688_;
}
else
{
lean_object* v___f_1689_; uint8_t v___x_1690_; 
lean_dec(v_currNamespace_1675_);
lean_inc(v_toPure_1674_);
lean_inc(v_shortName_1673_);
lean_inc(v_declName_1679_);
v___f_1689_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1689_, 0, v_declName_1679_);
lean_closure_set(v___f_1689_, 1, v_shortName_1673_);
lean_closure_set(v___f_1689_, 2, v_toPure_1674_);
v___x_1690_ = l_Lean_Name_isAtomic(v_shortName_1673_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec_ref(v___f_1689_);
lean_dec(v_toBind_1678_);
lean_dec_ref(v_inst_1677_);
lean_dec_ref(v_inst_1676_);
v___x_1691_ = lean_box(0);
v___x_1692_ = l_Lean_Elab_mkDeclName___redArg___lam__0(v_declName_1679_, v_shortName_1673_, v_toPure_1674_, v___x_1691_);
return v___x_1692_;
}
else
{
lean_object* v___f_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec(v_declName_1679_);
lean_dec(v_toPure_1674_);
lean_dec(v_shortName_1673_);
v___f_1693_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1693_, 0, v___f_1689_);
v___x_1694_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_1695_ = l_Lean_throwError___redArg(v_inst_1676_, v_inst_1677_, v___x_1694_);
v___x_1696_ = lean_apply_4(v_toBind_1678_, lean_box(0), lean_box(0), v___x_1695_, v___f_1693_);
return v___x_1696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2___boxed(lean_object* v_modifiers_1697_, lean_object* v_shortName_1698_, lean_object* v_toPure_1699_, lean_object* v_currNamespace_1700_, lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_toBind_1703_, lean_object* v_declName_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_Elab_mkDeclName___redArg___lam__2(v_modifiers_1697_, v_shortName_1698_, v_toPure_1699_, v_currNamespace_1700_, v_inst_1701_, v_inst_1702_, v_toBind_1703_, v_declName_1704_);
lean_dec_ref(v_modifiers_1697_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__1(lean_object* v_inst_1706_, lean_object* v_inst_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_modifiers_1711_, lean_object* v___y_1712_, lean_object* v_toBind_1713_, lean_object* v___f_1714_, lean_object* v_____r_1715_){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1706_, v_inst_1707_, v_inst_1708_, v_inst_1709_, v_inst_1710_, v_modifiers_1711_, v___y_1712_);
v___x_1717_ = lean_apply_4(v_toBind_1713_, lean_box(0), lean_box(0), v___x_1716_, v___f_1714_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3(lean_object* v_modifiers_1718_, lean_object* v_toPure_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_toBind_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v___y_1726_, lean_object* v_____r_1727_, lean_object* v_shortName_1728_, lean_object* v_currNamespace_1729_){
_start:
{
lean_object* v___f_1730_; lean_object* v___f_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_inc_n(v_toBind_1722_, 2);
lean_inc_ref_n(v_inst_1721_, 2);
lean_inc_ref_n(v_inst_1720_, 2);
lean_inc_ref(v_modifiers_1718_);
v___f_1730_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1730_, 0, v_modifiers_1718_);
lean_closure_set(v___f_1730_, 1, v_shortName_1728_);
lean_closure_set(v___f_1730_, 2, v_toPure_1719_);
lean_closure_set(v___f_1730_, 3, v_currNamespace_1729_);
lean_closure_set(v___f_1730_, 4, v_inst_1720_);
lean_closure_set(v___f_1730_, 5, v_inst_1721_);
lean_closure_set(v___f_1730_, 6, v_toBind_1722_);
lean_inc(v___y_1726_);
lean_inc_ref(v_inst_1723_);
v___f_1731_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1731_, 0, v_inst_1720_);
lean_closure_set(v___f_1731_, 1, v_inst_1723_);
lean_closure_set(v___f_1731_, 2, v_inst_1721_);
lean_closure_set(v___f_1731_, 3, v_inst_1724_);
lean_closure_set(v___f_1731_, 4, v_inst_1725_);
lean_closure_set(v___f_1731_, 5, v_modifiers_1718_);
lean_closure_set(v___f_1731_, 6, v___y_1726_);
lean_closure_set(v___f_1731_, 7, v_toBind_1722_);
lean_closure_set(v___f_1731_, 8, v___f_1730_);
v___x_1732_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1720_, v_inst_1723_, v_inst_1721_, v___y_1726_);
v___x_1733_ = lean_apply_4(v_toBind_1722_, lean_box(0), lean_box(0), v___x_1732_, v___f_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__4(lean_object* v___f_1734_, lean_object* v_shortName_1735_, lean_object* v_currNamespace_1736_, lean_object* v_____r_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_apply_3(v___f_1734_, v_____r_1737_, v_shortName_1735_, v_currNamespace_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5(lean_object* v_modifiers_1739_, lean_object* v_toPure_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_toBind_1743_, lean_object* v_inst_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_, uint8_t v_isRootName_1747_, lean_object* v_shortName_1748_, lean_object* v_currNamespace_1749_, lean_object* v_name_1750_, lean_object* v___x_1751_, lean_object* v_imported_1752_, lean_object* v_ctx_1753_, lean_object* v_scopes_1754_, lean_object* v_____r_1755_){
_start:
{
lean_object* v___y_1757_; 
if (v_isRootName_1747_ == 0)
{
lean_object* v___x_1776_; 
lean_dec(v_scopes_1754_);
lean_dec(v_ctx_1753_);
lean_dec(v_imported_1752_);
lean_inc(v_shortName_1748_);
lean_inc(v_currNamespace_1749_);
v___x_1776_ = l_Lean_Name_append(v_currNamespace_1749_, v_shortName_1748_);
v___y_1757_ = v___x_1776_;
goto v___jp_1756_;
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1777_ = lean_box(0);
lean_inc(v_name_1750_);
v___x_1778_ = l_Lean_Name_replacePrefix(v_name_1750_, v___x_1751_, v___x_1777_);
v___x_1779_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v_imported_1752_);
lean_ctor_set(v___x_1779_, 2, v_ctx_1753_);
lean_ctor_set(v___x_1779_, 3, v_scopes_1754_);
v___x_1780_ = l_Lean_MacroScopesView_review(v___x_1779_);
v___y_1757_ = v___x_1780_;
goto v___jp_1756_;
}
v___jp_1756_:
{
lean_object* v___f_1758_; 
lean_inc(v___y_1757_);
lean_inc_ref(v_inst_1746_);
lean_inc(v_inst_1745_);
lean_inc_ref(v_inst_1744_);
lean_inc(v_toBind_1743_);
lean_inc_ref(v_inst_1742_);
lean_inc_ref(v_inst_1741_);
lean_inc(v_toPure_1740_);
lean_inc_ref(v_modifiers_1739_);
v___f_1758_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__3), 12, 9);
lean_closure_set(v___f_1758_, 0, v_modifiers_1739_);
lean_closure_set(v___f_1758_, 1, v_toPure_1740_);
lean_closure_set(v___f_1758_, 2, v_inst_1741_);
lean_closure_set(v___f_1758_, 3, v_inst_1742_);
lean_closure_set(v___f_1758_, 4, v_toBind_1743_);
lean_closure_set(v___f_1758_, 5, v_inst_1744_);
lean_closure_set(v___f_1758_, 6, v_inst_1745_);
lean_closure_set(v___f_1758_, 7, v_inst_1746_);
lean_closure_set(v___f_1758_, 8, v___y_1757_);
if (v_isRootName_1747_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec_ref(v___f_1758_);
lean_dec(v_name_1750_);
v___x_1759_ = lean_box(0);
v___x_1760_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1739_, v_toPure_1740_, v_inst_1741_, v_inst_1742_, v_toBind_1743_, v_inst_1744_, v_inst_1745_, v_inst_1746_, v___y_1757_, v___x_1759_, v_shortName_1748_, v_currNamespace_1749_);
return v___x_1760_;
}
else
{
if (lean_obj_tag(v_name_1750_) == 1)
{
lean_object* v_pre_1761_; lean_object* v_str_1762_; lean_object* v___x_1763_; lean_object* v_shortName_1764_; lean_object* v_currNamespace_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec_ref(v___f_1758_);
lean_dec(v_currNamespace_1749_);
lean_dec(v_shortName_1748_);
v_pre_1761_ = lean_ctor_get(v_name_1750_, 0);
lean_inc(v_pre_1761_);
v_str_1762_ = lean_ctor_get(v_name_1750_, 1);
lean_inc_ref(v_str_1762_);
lean_dec_ref_known(v_name_1750_, 2);
v___x_1763_ = lean_box(0);
v_shortName_1764_ = l_Lean_Name_str___override(v___x_1763_, v_str_1762_);
v_currNamespace_1765_ = l_Lean_Name_replacePrefix(v_pre_1761_, v___x_1751_, v___x_1763_);
v___x_1766_ = lean_box(0);
v___x_1767_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1739_, v_toPure_1740_, v_inst_1741_, v_inst_1742_, v_toBind_1743_, v_inst_1744_, v_inst_1745_, v_inst_1746_, v___y_1757_, v___x_1766_, v_shortName_1764_, v_currNamespace_1765_);
return v___x_1767_;
}
else
{
lean_object* v___f_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_dec(v___y_1757_);
lean_dec_ref(v_inst_1746_);
lean_dec(v_inst_1745_);
lean_dec_ref(v_inst_1744_);
lean_dec(v_toPure_1740_);
lean_dec_ref(v_modifiers_1739_);
v___f_1768_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__4), 4, 3);
lean_closure_set(v___f_1768_, 0, v___f_1758_);
lean_closure_set(v___f_1768_, 1, v_shortName_1748_);
lean_closure_set(v___f_1768_, 2, v_currNamespace_1749_);
v___x_1769_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1770_ = l_Lean_MessageData_ofName(v_name_1750_);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1771_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = l_Lean_throwError___redArg(v_inst_1741_, v_inst_1742_, v___x_1773_);
v___x_1775_ = lean_apply_4(v_toBind_1743_, lean_box(0), lean_box(0), v___x_1774_, v___f_1768_);
return v___x_1775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_modifiers_1781_ = _args[0];
lean_object* v_toPure_1782_ = _args[1];
lean_object* v_inst_1783_ = _args[2];
lean_object* v_inst_1784_ = _args[3];
lean_object* v_toBind_1785_ = _args[4];
lean_object* v_inst_1786_ = _args[5];
lean_object* v_inst_1787_ = _args[6];
lean_object* v_inst_1788_ = _args[7];
lean_object* v_isRootName_1789_ = _args[8];
lean_object* v_shortName_1790_ = _args[9];
lean_object* v_currNamespace_1791_ = _args[10];
lean_object* v_name_1792_ = _args[11];
lean_object* v___x_1793_ = _args[12];
lean_object* v_imported_1794_ = _args[13];
lean_object* v_ctx_1795_ = _args[14];
lean_object* v_scopes_1796_ = _args[15];
lean_object* v_____r_1797_ = _args[16];
_start:
{
uint8_t v_isRootName_boxed_1798_; lean_object* v_res_1799_; 
v_isRootName_boxed_1798_ = lean_unbox(v_isRootName_1789_);
v_res_1799_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1781_, v_toPure_1782_, v_inst_1783_, v_inst_1784_, v_toBind_1785_, v_inst_1786_, v_inst_1787_, v_inst_1788_, v_isRootName_boxed_1798_, v_shortName_1790_, v_currNamespace_1791_, v_name_1792_, v___x_1793_, v_imported_1794_, v_ctx_1795_, v_scopes_1796_, v_____r_1797_);
lean_dec(v___x_1793_);
return v_res_1799_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___closed__3(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__2));
v___x_1805_ = l_Lean_stringToMessageData(v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg(lean_object* v_inst_1806_, lean_object* v_inst_1807_, lean_object* v_inst_1808_, lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_currNamespace_1811_, lean_object* v_modifiers_1812_, lean_object* v_shortName_1813_){
_start:
{
lean_object* v_view_1814_; lean_object* v_toApplicative_1815_; lean_object* v_name_1816_; lean_object* v_imported_1817_; lean_object* v_ctx_1818_; lean_object* v_scopes_1819_; lean_object* v_toBind_1820_; lean_object* v_toPure_1821_; lean_object* v___x_1822_; uint8_t v_isRootName_1823_; lean_object* v___x_1824_; lean_object* v___f_1825_; uint8_t v___x_1826_; 
lean_inc_n(v_shortName_1813_, 2);
v_view_1814_ = l_Lean_extractMacroScopes(v_shortName_1813_);
v_toApplicative_1815_ = lean_ctor_get(v_inst_1806_, 0);
v_name_1816_ = lean_ctor_get(v_view_1814_, 0);
lean_inc_n(v_name_1816_, 2);
v_imported_1817_ = lean_ctor_get(v_view_1814_, 1);
lean_inc_n(v_imported_1817_, 2);
v_ctx_1818_ = lean_ctor_get(v_view_1814_, 2);
lean_inc_n(v_ctx_1818_, 2);
v_scopes_1819_ = lean_ctor_get(v_view_1814_, 3);
lean_inc_n(v_scopes_1819_, 2);
lean_dec_ref(v_view_1814_);
v_toBind_1820_ = lean_ctor_get(v_inst_1806_, 1);
lean_inc_n(v_toBind_1820_, 2);
v_toPure_1821_ = lean_ctor_get(v_toApplicative_1815_, 1);
v___x_1822_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_1823_ = l_Lean_Name_isPrefixOf(v___x_1822_, v_name_1816_);
v___x_1824_ = lean_box(v_isRootName_1823_);
lean_inc(v_currNamespace_1811_);
lean_inc_ref(v_inst_1810_);
lean_inc(v_inst_1809_);
lean_inc_ref(v_inst_1807_);
lean_inc_ref(v_inst_1808_);
lean_inc_ref(v_inst_1806_);
lean_inc(v_toPure_1821_);
lean_inc_ref(v_modifiers_1812_);
v___f_1825_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1825_, 0, v_modifiers_1812_);
lean_closure_set(v___f_1825_, 1, v_toPure_1821_);
lean_closure_set(v___f_1825_, 2, v_inst_1806_);
lean_closure_set(v___f_1825_, 3, v_inst_1808_);
lean_closure_set(v___f_1825_, 4, v_toBind_1820_);
lean_closure_set(v___f_1825_, 5, v_inst_1807_);
lean_closure_set(v___f_1825_, 6, v_inst_1809_);
lean_closure_set(v___f_1825_, 7, v_inst_1810_);
lean_closure_set(v___f_1825_, 8, v___x_1824_);
lean_closure_set(v___f_1825_, 9, v_shortName_1813_);
lean_closure_set(v___f_1825_, 10, v_currNamespace_1811_);
lean_closure_set(v___f_1825_, 11, v_name_1816_);
lean_closure_set(v___f_1825_, 12, v___x_1822_);
lean_closure_set(v___f_1825_, 13, v_imported_1817_);
lean_closure_set(v___f_1825_, 14, v_ctx_1818_);
lean_closure_set(v___f_1825_, 15, v_scopes_1819_);
v___x_1826_ = lean_name_eq(v_name_1816_, v___x_1822_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_inc(v_toPure_1821_);
lean_dec_ref(v___f_1825_);
v___x_1827_ = lean_box(0);
v___x_1828_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1812_, v_toPure_1821_, v_inst_1806_, v_inst_1808_, v_toBind_1820_, v_inst_1807_, v_inst_1809_, v_inst_1810_, v_isRootName_1823_, v_shortName_1813_, v_currNamespace_1811_, v_name_1816_, v___x_1822_, v_imported_1817_, v_ctx_1818_, v_scopes_1819_, v___x_1827_);
return v___x_1828_;
}
else
{
lean_object* v___f_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec(v_scopes_1819_);
lean_dec(v_ctx_1818_);
lean_dec(v_imported_1817_);
lean_dec(v_name_1816_);
lean_dec(v_shortName_1813_);
lean_dec_ref(v_modifiers_1812_);
lean_dec(v_currNamespace_1811_);
lean_dec_ref(v_inst_1810_);
lean_dec(v_inst_1809_);
lean_dec_ref(v_inst_1807_);
v___f_1829_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1829_, 0, v___f_1825_);
v___x_1830_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_1831_ = l_Lean_throwError___redArg(v_inst_1806_, v_inst_1808_, v___x_1830_);
v___x_1832_ = lean_apply_4(v_toBind_1820_, lean_box(0), lean_box(0), v___x_1831_, v___f_1829_);
return v___x_1832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName(lean_object* v_m_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_inst_1838_, lean_object* v_currNamespace_1839_, lean_object* v_modifiers_1840_, lean_object* v_shortName_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Lean_Elab_mkDeclName___redArg(v_inst_1834_, v_inst_1835_, v_inst_1836_, v_inst_1837_, v_inst_1838_, v_currNamespace_1839_, v_modifiers_1840_, v_shortName_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore(lean_object* v_declId_1852_){
_start:
{
uint8_t v___x_1853_; 
v___x_1853_ = l_Lean_Syntax_isIdent(v_declId_1852_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v_id_1856_; lean_object* v___x_1857_; lean_object* v_optUnivDeclStx_1858_; lean_object* v___x_1859_; 
v___x_1854_ = lean_unsigned_to_nat(0u);
v___x_1855_ = l_Lean_Syntax_getArg(v_declId_1852_, v___x_1854_);
v_id_1856_ = l_Lean_Syntax_getId(v___x_1855_);
lean_dec(v___x_1855_);
v___x_1857_ = lean_unsigned_to_nat(1u);
v_optUnivDeclStx_1858_ = l_Lean_Syntax_getArg(v_declId_1852_, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v_id_1856_);
lean_ctor_set(v___x_1859_, 1, v_optUnivDeclStx_1858_);
return v___x_1859_;
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = l_Lean_Syntax_getId(v_declId_1852_);
v___x_1861_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__3));
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1860_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
return v___x_1862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore___boxed(lean_object* v_declId_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Elab_expandDeclIdCore(v_declId_1863_);
lean_dec(v_declId_1863_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(lean_object* v_msgData_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; lean_object* v_env_1872_; lean_object* v___x_1873_; lean_object* v_mctx_1874_; lean_object* v_lctx_1875_; lean_object* v_options_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1871_ = lean_st_ref_get(v___y_1869_);
v_env_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc_ref(v_env_1872_);
lean_dec(v___x_1871_);
v___x_1873_ = lean_st_ref_get(v___y_1867_);
v_mctx_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc_ref(v_mctx_1874_);
lean_dec(v___x_1873_);
v_lctx_1875_ = lean_ctor_get(v___y_1866_, 2);
v_options_1876_ = lean_ctor_get(v___y_1868_, 1);
lean_inc_ref(v_options_1876_);
lean_inc_ref(v_lctx_1875_);
v___x_1877_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1877_, 0, v_env_1872_);
lean_ctor_set(v___x_1877_, 1, v_mctx_1874_);
lean_ctor_set(v___x_1877_, 2, v_lctx_1875_);
lean_ctor_set(v___x_1877_, 3, v_options_1876_);
v___x_1878_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v_msgData_1865_);
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msgData_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1886_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(lean_object* v_opts_1887_, lean_object* v_opt_1888_){
_start:
{
lean_object* v_name_1889_; lean_object* v_defValue_1890_; lean_object* v_map_1891_; lean_object* v___x_1892_; 
v_name_1889_ = lean_ctor_get(v_opt_1888_, 0);
v_defValue_1890_ = lean_ctor_get(v_opt_1888_, 1);
v_map_1891_ = lean_ctor_get(v_opts_1887_, 0);
v___x_1892_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1891_, v_name_1889_);
if (lean_obj_tag(v___x_1892_) == 0)
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_unbox(v_defValue_1890_);
return v___x_1893_;
}
else
{
lean_object* v_val_1894_; 
v_val_1894_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_val_1894_);
lean_dec_ref_known(v___x_1892_, 1);
if (lean_obj_tag(v_val_1894_) == 1)
{
uint8_t v_v_1895_; 
v_v_1895_ = lean_ctor_get_uint8(v_val_1894_, 0);
lean_dec_ref_known(v_val_1894_, 0);
return v_v_1895_;
}
else
{
uint8_t v___x_1896_; 
lean_dec(v_val_1894_);
v___x_1896_ = lean_unbox(v_defValue_1890_);
return v___x_1896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_opts_1897_, lean_object* v_opt_1898_){
_start:
{
uint8_t v_res_1899_; lean_object* v_r_1900_; 
v_res_1899_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_opts_1897_, v_opt_1898_);
lean_dec_ref(v_opt_1898_);
lean_dec_ref(v_opts_1897_);
v_r_1900_ = lean_box(v_res_1899_);
return v_r_1900_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_box(1);
v___x_1902_ = l_Lean_MessageData_ofFormat(v___x_1901_);
return v___x_1902_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2));
v___x_1907_ = l_Lean_MessageData_ofFormat(v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(lean_object* v_x_1908_, lean_object* v_x_1909_){
_start:
{
if (lean_obj_tag(v_x_1909_) == 0)
{
return v_x_1908_;
}
else
{
lean_object* v_head_1910_; lean_object* v_tail_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1933_; 
v_head_1910_ = lean_ctor_get(v_x_1909_, 0);
v_tail_1911_ = lean_ctor_get(v_x_1909_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_x_1909_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1913_ = v_x_1909_;
v_isShared_1914_ = v_isSharedCheck_1933_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_tail_1911_);
lean_inc(v_head_1910_);
lean_dec(v_x_1909_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1933_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v_before_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1931_; 
v_before_1915_ = lean_ctor_get(v_head_1910_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_head_1910_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v_head_1910_, 1);
lean_dec(v_unused_1932_);
v___x_1917_ = v_head_1910_;
v_isShared_1918_ = v_isSharedCheck_1931_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_before_1915_);
lean_dec(v_head_1910_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1931_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1919_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 7);
lean_ctor_set(v___x_1917_, 1, v___x_1919_);
lean_ctor_set(v___x_1917_, 0, v_x_1908_);
v___x_1921_ = v___x_1917_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_x_1908_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1922_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3);
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 7);
lean_ctor_set(v___x_1913_, 1, v___x_1922_);
lean_ctor_set(v___x_1913_, 0, v___x_1921_);
v___x_1924_ = v___x_1913_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = l_Lean_MessageData_ofSyntax(v_before_1915_);
v___x_1926_ = l_Lean_indentD(v___x_1925_);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1924_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v_x_1908_ = v___x_1927_;
v_x_1909_ = v_tail_1911_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1));
v___x_1938_ = l_Lean_MessageData_ofFormat(v___x_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_1939_, lean_object* v_macroStack_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_options_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v_options_1943_ = lean_ctor_get(v___y_1941_, 1);
v___x_1944_ = l_Lean_Elab_pp_macroStack;
v___x_1945_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_options_1943_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; 
lean_dec(v_macroStack_1940_);
v___x_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1946_, 0, v_msgData_1939_);
return v___x_1946_;
}
else
{
if (lean_obj_tag(v_macroStack_1940_) == 0)
{
lean_object* v___x_1947_; 
v___x_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1947_, 0, v_msgData_1939_);
return v___x_1947_;
}
else
{
lean_object* v_head_1948_; lean_object* v_after_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1964_; 
v_head_1948_ = lean_ctor_get(v_macroStack_1940_, 0);
lean_inc(v_head_1948_);
v_after_1949_ = lean_ctor_get(v_head_1948_, 1);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_head_1948_);
if (v_isSharedCheck_1964_ == 0)
{
lean_object* v_unused_1965_; 
v_unused_1965_ = lean_ctor_get(v_head_1948_, 0);
lean_dec(v_unused_1965_);
v___x_1951_ = v_head_1948_;
v_isShared_1952_ = v_isSharedCheck_1964_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_after_1949_);
lean_dec(v_head_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1964_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_1952_ == 0)
{
lean_ctor_set_tag(v___x_1951_, 7);
lean_ctor_set(v___x_1951_, 1, v___x_1953_);
lean_ctor_set(v___x_1951_, 0, v_msgData_1939_);
v___x_1955_ = v___x_1951_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_msgData_1939_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v_msgData_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1956_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = l_Lean_MessageData_ofSyntax(v_after_1949_);
v___x_1959_ = l_Lean_indentD(v___x_1958_);
v_msgData_1960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1960_, 0, v___x_1957_);
lean_ctor_set(v_msgData_1960_, 1, v___x_1959_);
v___x_1961_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(v_msgData_1960_, v_macroStack_1940_);
v___x_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_1966_, lean_object* v_macroStack_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_1966_, v_macroStack_1967_, v___y_1968_);
lean_dec_ref(v___y_1968_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(lean_object* v_msg_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_ref_1979_; lean_object* v___x_1980_; lean_object* v_a_1981_; lean_object* v_macroStack_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1993_; 
v_ref_1979_ = lean_ctor_get(v___y_1976_, 4);
v___x_1980_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msg_1971_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref(v___x_1980_);
v_macroStack_1982_ = lean_ctor_get(v___y_1972_, 1);
v___x_1983_ = l_Lean_Elab_getBetterRef(v_ref_1979_, v_macroStack_1982_);
lean_inc(v_macroStack_1982_);
v___x_1984_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_a_1981_, v_macroStack_1982_, v___y_1976_);
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1987_ = v___x_1984_;
v_isShared_1988_ = v_isSharedCheck_1993_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1984_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1993_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1983_);
lean_ctor_set(v___x_1989_, 1, v_a_1985_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 1);
lean_ctor_set(v___x_1987_, 0, v___x_1989_);
v___x_1991_ = v___x_1987_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(lean_object* v_env_2003_, lean_object* v_declName_2004_, lean_object* v___f_2005_, lean_object* v_addInfo_2006_, lean_object* v_____r_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___x_2015_; uint8_t v___x_2016_; uint8_t v___x_2017_; 
lean_inc(v_declName_2004_);
v___x_2015_ = l_Lean_mkPrivateName(v_env_2003_, v_declName_2004_);
v___x_2016_ = 1;
lean_inc(v___x_2015_);
v___x_2017_ = l_Lean_Environment_contains(v_env_2003_, v___x_2015_, v___x_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec(v___x_2015_);
lean_dec_ref(v_addInfo_2006_);
lean_dec(v_declName_2004_);
v___x_2018_ = lean_box(0);
lean_inc(v___y_2013_);
lean_inc_ref(v___y_2012_);
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2010_);
lean_inc(v___y_2009_);
lean_inc_ref(v___y_2008_);
v___x_2019_ = lean_apply_8(v___f_2005_, v___x_2018_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, lean_box(0));
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; 
lean_dec_ref(v___f_2005_);
lean_inc(v___y_2013_);
lean_inc_ref(v___y_2012_);
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2010_);
lean_inc(v___y_2009_);
lean_inc_ref(v___y_2008_);
v___x_2020_ = lean_apply_8(v_addInfo_2006_, v___x_2015_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, lean_box(0));
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
lean_dec_ref_known(v___x_2020_, 1);
v___x_2021_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1);
v___x_2022_ = l_Lean_MessageData_ofConstName(v_declName_2004_, v___x_2016_);
v___x_2023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2021_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2023_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2025_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
return v___x_2026_;
}
else
{
lean_dec(v_declName_2004_);
return v___x_2020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed(lean_object* v_env_2027_, lean_object* v_declName_2028_, lean_object* v___f_2029_, lean_object* v_addInfo_2030_, lean_object* v_____r_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(v_env_2027_, v_declName_2028_, v___f_2029_, v_addInfo_2030_, v_____r_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(lean_object* v___f_2040_, lean_object* v_declName_2041_, uint8_t v___x_2042_, lean_object* v_env_2043_, lean_object* v_____do__lift_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
uint8_t v___y_2053_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
lean_inc(v_declName_2041_);
v___x_2062_ = l_Lean_privateToUserName(v_declName_2041_);
lean_inc_ref(v_env_2043_);
v___x_2063_ = lean_is_reserved_name(v_env_2043_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; uint8_t v___x_2065_; 
lean_inc(v_declName_2041_);
v___x_2064_ = l_Lean_mkPrivateName(v_____do__lift_2044_, v_declName_2041_);
v___x_2065_ = lean_is_reserved_name(v_env_2043_, v___x_2064_);
v___y_2053_ = v___x_2065_;
goto v___jp_2052_;
}
else
{
lean_dec_ref(v_env_2043_);
v___y_2053_ = v___x_2063_;
goto v___jp_2052_;
}
v___jp_2052_:
{
if (v___y_2053_ == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec(v_declName_2041_);
v___x_2054_ = lean_box(0);
lean_inc(v___y_2050_);
lean_inc_ref(v___y_2049_);
lean_inc(v___y_2048_);
lean_inc_ref(v___y_2047_);
lean_inc(v___y_2046_);
lean_inc_ref(v___y_2045_);
v___x_2055_ = lean_apply_8(v___f_2040_, v___x_2054_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, lean_box(0));
return v___x_2055_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_dec_ref(v___f_2040_);
v___x_2056_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2057_ = l_Lean_MessageData_ofConstName(v_declName_2041_, v___x_2042_);
v___x_2058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2056_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
v___x_2059_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3);
v___x_2060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2058_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2060_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
return v___x_2061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed(lean_object* v___f_2066_, lean_object* v_declName_2067_, lean_object* v___x_2068_, lean_object* v_env_2069_, lean_object* v_____do__lift_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
uint8_t v___x_16752__boxed_2078_; lean_object* v_res_2079_; 
v___x_16752__boxed_2078_ = lean_unbox(v___x_2068_);
v_res_2079_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(v___f_2066_, v_declName_2067_, v___x_16752__boxed_2078_, v_env_2069_, v_____do__lift_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec_ref(v_____do__lift_2070_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(lean_object* v_t_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v___x_2083_; lean_object* v_infoState_2084_; uint8_t v_enabled_2085_; 
v___x_2083_ = lean_st_ref_get(v___y_2081_);
v_infoState_2084_ = lean_ctor_get(v___x_2083_, 7);
lean_inc_ref(v_infoState_2084_);
lean_dec(v___x_2083_);
v_enabled_2085_ = lean_ctor_get_uint8(v_infoState_2084_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2084_);
if (v_enabled_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec_ref(v_t_2080_);
v___x_2086_ = lean_box(0);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
return v___x_2087_;
}
else
{
lean_object* v___x_2088_; lean_object* v_infoState_2089_; lean_object* v_env_2090_; lean_object* v_nextMacroScope_2091_; lean_object* v_ngen_2092_; lean_object* v_auxDeclNGen_2093_; lean_object* v_traceState_2094_; lean_object* v_cache_2095_; lean_object* v_messages_2096_; lean_object* v_snapshotTasks_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2119_; 
v___x_2088_ = lean_st_ref_take(v___y_2081_);
v_infoState_2089_ = lean_ctor_get(v___x_2088_, 7);
v_env_2090_ = lean_ctor_get(v___x_2088_, 0);
v_nextMacroScope_2091_ = lean_ctor_get(v___x_2088_, 1);
v_ngen_2092_ = lean_ctor_get(v___x_2088_, 2);
v_auxDeclNGen_2093_ = lean_ctor_get(v___x_2088_, 3);
v_traceState_2094_ = lean_ctor_get(v___x_2088_, 4);
v_cache_2095_ = lean_ctor_get(v___x_2088_, 5);
v_messages_2096_ = lean_ctor_get(v___x_2088_, 6);
v_snapshotTasks_2097_ = lean_ctor_get(v___x_2088_, 8);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2099_ = v___x_2088_;
v_isShared_2100_ = v_isSharedCheck_2119_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_snapshotTasks_2097_);
lean_inc(v_infoState_2089_);
lean_inc(v_messages_2096_);
lean_inc(v_cache_2095_);
lean_inc(v_traceState_2094_);
lean_inc(v_auxDeclNGen_2093_);
lean_inc(v_ngen_2092_);
lean_inc(v_nextMacroScope_2091_);
lean_inc(v_env_2090_);
lean_dec(v___x_2088_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2119_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
uint8_t v_enabled_2101_; lean_object* v_assignment_2102_; lean_object* v_lazyAssignment_2103_; lean_object* v_trees_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2118_; 
v_enabled_2101_ = lean_ctor_get_uint8(v_infoState_2089_, sizeof(void*)*3);
v_assignment_2102_ = lean_ctor_get(v_infoState_2089_, 0);
v_lazyAssignment_2103_ = lean_ctor_get(v_infoState_2089_, 1);
v_trees_2104_ = lean_ctor_get(v_infoState_2089_, 2);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_infoState_2089_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2106_ = v_infoState_2089_;
v_isShared_2107_ = v_isSharedCheck_2118_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_trees_2104_);
lean_inc(v_lazyAssignment_2103_);
lean_inc(v_assignment_2102_);
lean_dec(v_infoState_2089_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2118_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2108_ = l_Lean_PersistentArray_push___redArg(v_trees_2104_, v_t_2080_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 2, v___x_2108_);
v___x_2110_ = v___x_2106_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_assignment_2102_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_lazyAssignment_2103_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v___x_2108_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*3, v_enabled_2101_);
v___x_2110_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2112_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 7, v___x_2110_);
v___x_2112_ = v___x_2099_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_env_2090_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_nextMacroScope_2091_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_ngen_2092_);
lean_ctor_set(v_reuseFailAlloc_2116_, 3, v_auxDeclNGen_2093_);
lean_ctor_set(v_reuseFailAlloc_2116_, 4, v_traceState_2094_);
lean_ctor_set(v_reuseFailAlloc_2116_, 5, v_cache_2095_);
lean_ctor_set(v_reuseFailAlloc_2116_, 6, v_messages_2096_);
lean_ctor_set(v_reuseFailAlloc_2116_, 7, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2116_, 8, v_snapshotTasks_2097_);
v___x_2112_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = lean_st_ref_put(v___y_2081_, v___x_2112_);
v___x_2114_ = lean_box(0);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg___boxed(lean_object* v_t_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_2120_, v___y_2121_);
lean_dec(v___y_2121_);
return v_res_2123_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = lean_unsigned_to_nat(32u);
v___x_2125_ = lean_mk_empty_array_with_capacity(v___x_2124_);
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
return v___x_2126_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1(void){
_start:
{
size_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2127_ = ((size_t)5ULL);
v___x_2128_ = lean_unsigned_to_nat(0u);
v___x_2129_ = lean_unsigned_to_nat(32u);
v___x_2130_ = lean_mk_empty_array_with_capacity(v___x_2129_);
v___x_2131_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0);
v___x_2132_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v___x_2130_);
lean_ctor_set(v___x_2132_, 2, v___x_2128_);
lean_ctor_set(v___x_2132_, 3, v___x_2128_);
lean_ctor_set_usize(v___x_2132_, 4, v___x_2127_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(lean_object* v_t_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2141_; lean_object* v_infoState_2142_; uint8_t v_enabled_2143_; 
v___x_2141_ = lean_st_ref_get(v___y_2139_);
v_infoState_2142_ = lean_ctor_get(v___x_2141_, 7);
lean_inc_ref(v_infoState_2142_);
lean_dec(v___x_2141_);
v_enabled_2143_ = lean_ctor_get_uint8(v_infoState_2142_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2142_);
if (v_enabled_2143_ == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec_ref(v_t_2133_);
v___x_2144_ = lean_box(0);
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
return v___x_2145_;
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1);
v___x_2147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2147_, 0, v_t_2133_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v___x_2147_, v___y_2139_);
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___boxed(lean_object* v_t_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v_t_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
if (lean_obj_tag(v_a_2158_) == 0)
{
lean_object* v___x_2160_; 
v___x_2160_ = l_List_reverse___redArg(v_a_2159_);
return v___x_2160_;
}
else
{
lean_object* v_head_2161_; lean_object* v_tail_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2171_; 
v_head_2161_ = lean_ctor_get(v_a_2158_, 0);
v_tail_2162_ = lean_ctor_get(v_a_2158_, 1);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_a_2158_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2164_ = v_a_2158_;
v_isShared_2165_ = v_isSharedCheck_2171_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_tail_2162_);
lean_inc(v_head_2161_);
lean_dec(v_a_2158_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2171_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2166_ = l_Lean_mkLevelParam(v_head_2161_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 1, v_a_2159_);
lean_ctor_set(v___x_2164_, 0, v___x_2166_);
v___x_2168_ = v___x_2164_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_a_2159_);
v___x_2168_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
v_a_2158_ = v_tail_2162_;
v_a_2159_ = v___x_2168_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0(void){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0);
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
v___x_2176_ = lean_unsigned_to_nat(0u);
v___x_2177_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
lean_ctor_set(v___x_2177_, 2, v___x_2176_);
lean_ctor_set(v___x_2177_, 3, v___x_2176_);
lean_ctor_set(v___x_2177_, 4, v___x_2175_);
lean_ctor_set(v___x_2177_, 5, v___x_2175_);
lean_ctor_set(v___x_2177_, 6, v___x_2175_);
lean_ctor_set(v___x_2177_, 7, v___x_2175_);
lean_ctor_set(v___x_2177_, 8, v___x_2175_);
lean_ctor_set(v___x_2177_, 9, v___x_2175_);
lean_ctor_set(v___x_2177_, 10, v___x_2175_);
return v___x_2177_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2178_ = lean_box(1);
v___x_2179_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3);
v___x_2180_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
v___x_2181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
lean_ctor_set(v___x_2181_, 1, v___x_2179_);
lean_ctor_set(v___x_2181_, 2, v___x_2178_);
return v___x_2181_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4));
v___x_2184_ = l_Lean_stringToMessageData(v___x_2183_);
return v___x_2184_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6));
v___x_2187_ = l_Lean_stringToMessageData(v___x_2186_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8));
v___x_2190_ = l_Lean_stringToMessageData(v___x_2189_);
return v___x_2190_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10));
v___x_2193_ = l_Lean_stringToMessageData(v___x_2192_);
return v___x_2193_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12));
v___x_2196_ = l_Lean_stringToMessageData(v___x_2195_);
return v___x_2196_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14));
v___x_2199_ = l_Lean_stringToMessageData(v___x_2198_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16));
v___x_2202_ = l_Lean_stringToMessageData(v___x_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(lean_object* v_msg_2203_, lean_object* v_declHint_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; lean_object* v_env_2208_; uint8_t v___x_2209_; 
v___x_2207_ = lean_st_ref_get(v___y_2205_);
v_env_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc_ref(v_env_2208_);
lean_dec(v___x_2207_);
v___x_2209_ = l_Lean_Name_isAnonymous(v_declHint_2204_);
if (v___x_2209_ == 0)
{
uint8_t v_isExporting_2210_; 
v_isExporting_2210_ = lean_ctor_get_uint8(v_env_2208_, sizeof(void*)*8);
if (v_isExporting_2210_ == 0)
{
lean_object* v___x_2211_; 
lean_dec_ref(v_env_2208_);
lean_dec(v_declHint_2204_);
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_msg_2203_);
return v___x_2211_;
}
else
{
lean_object* v___x_2212_; uint8_t v___x_2213_; 
lean_inc_ref(v_env_2208_);
v___x_2212_ = l_Lean_Environment_setExporting(v_env_2208_, v___x_2209_);
lean_inc(v_declHint_2204_);
lean_inc_ref(v___x_2212_);
v___x_2213_ = l_Lean_Environment_contains(v___x_2212_, v_declHint_2204_, v_isExporting_2210_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
lean_dec_ref(v___x_2212_);
lean_dec_ref(v_env_2208_);
lean_dec(v_declHint_2204_);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_msg_2203_);
return v___x_2214_;
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v_c_2220_; lean_object* v___x_2221_; 
v___x_2215_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2);
v___x_2216_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3);
v___x_2217_ = l_Lean_Options_empty;
v___x_2218_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2212_);
lean_ctor_set(v___x_2218_, 1, v___x_2215_);
lean_ctor_set(v___x_2218_, 2, v___x_2216_);
lean_ctor_set(v___x_2218_, 3, v___x_2217_);
lean_inc(v_declHint_2204_);
v___x_2219_ = l_Lean_MessageData_ofConstName(v_declHint_2204_, v___x_2209_);
v_c_2220_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2220_, 0, v___x_2218_);
lean_ctor_set(v_c_2220_, 1, v___x_2219_);
v___x_2221_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2208_, v_declHint_2204_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec_ref(v_env_2208_);
lean_dec(v_declHint_2204_);
v___x_2222_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5);
v___x_2223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v_c_2220_);
v___x_2224_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7);
v___x_2225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2223_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = l_Lean_MessageData_note(v___x_2225_);
v___x_2227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2227_, 0, v_msg_2203_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
else
{
lean_object* v_val_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2264_; 
v_val_2229_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2231_ = v___x_2221_;
v_isShared_2232_ = v_isSharedCheck_2264_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_val_2229_);
lean_dec(v___x_2221_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2264_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v_mod_2236_; uint8_t v___x_2237_; 
v___x_2233_ = lean_box(0);
v___x_2234_ = l_Lean_Environment_header(v_env_2208_);
lean_dec_ref(v_env_2208_);
v___x_2235_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2234_);
v_mod_2236_ = lean_array_get(v___x_2233_, v___x_2235_, v_val_2229_);
lean_dec(v_val_2229_);
lean_dec_ref(v___x_2235_);
v___x_2237_ = l_Lean_isPrivateName(v_declHint_2204_);
lean_dec(v_declHint_2204_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2249_; 
v___x_2238_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9);
v___x_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set(v___x_2239_, 1, v_c_2220_);
v___x_2240_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11);
v___x_2241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2239_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = l_Lean_MessageData_ofName(v_mod_2236_);
v___x_2243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2241_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13);
v___x_2245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = l_Lean_MessageData_note(v___x_2245_);
v___x_2247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2247_, 0, v_msg_2203_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set_tag(v___x_2231_, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2247_);
v___x_2249_ = v___x_2231_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2251_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5);
v___x_2252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v_c_2220_);
v___x_2253_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15);
v___x_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = l_Lean_MessageData_ofName(v_mod_2236_);
v___x_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17);
v___x_2258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = l_Lean_MessageData_note(v___x_2258_);
v___x_2260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2260_, 0, v_msg_2203_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set_tag(v___x_2231_, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2260_);
v___x_2262_ = v___x_2231_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2265_; 
lean_dec_ref(v_env_2208_);
lean_dec(v_declHint_2204_);
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v_msg_2203_);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___boxed(lean_object* v_msg_2266_, lean_object* v_declHint_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2266_, v_declHint_2267_, v___y_2268_);
lean_dec(v___y_2268_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(lean_object* v_msg_2271_, lean_object* v_declHint_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v___x_2280_; lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2290_; 
v___x_2280_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2271_, v_declHint_2272_, v___y_2278_);
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2290_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2290_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2285_ = l_Lean_unknownIdentifierMessageTag;
v___x_2286_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_ctor_set(v___x_2286_, 1, v_a_2281_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2286_);
v___x_2288_ = v___x_2283_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23___boxed(lean_object* v_msg_2291_, lean_object* v_declHint_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2291_, v_declHint_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(lean_object* v_ref_2301_, lean_object* v_msg_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_toCold_2310_; lean_object* v_options_2311_; lean_object* v_currRecDepth_2312_; lean_object* v_maxRecDepth_2313_; lean_object* v_ref_2314_; lean_object* v_currNamespace_2315_; lean_object* v_openDecls_2316_; lean_object* v_initHeartbeats_2317_; lean_object* v_maxHeartbeats_2318_; lean_object* v_currMacroScope_2319_; uint8_t v_diag_2320_; uint8_t v_suppressElabErrors_2321_; lean_object* v_ref_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_toCold_2310_ = lean_ctor_get(v___y_2307_, 0);
v_options_2311_ = lean_ctor_get(v___y_2307_, 1);
v_currRecDepth_2312_ = lean_ctor_get(v___y_2307_, 2);
v_maxRecDepth_2313_ = lean_ctor_get(v___y_2307_, 3);
v_ref_2314_ = lean_ctor_get(v___y_2307_, 4);
v_currNamespace_2315_ = lean_ctor_get(v___y_2307_, 5);
v_openDecls_2316_ = lean_ctor_get(v___y_2307_, 6);
v_initHeartbeats_2317_ = lean_ctor_get(v___y_2307_, 7);
v_maxHeartbeats_2318_ = lean_ctor_get(v___y_2307_, 8);
v_currMacroScope_2319_ = lean_ctor_get(v___y_2307_, 9);
v_diag_2320_ = lean_ctor_get_uint8(v___y_2307_, sizeof(void*)*10);
v_suppressElabErrors_2321_ = lean_ctor_get_uint8(v___y_2307_, sizeof(void*)*10 + 1);
v_ref_2322_ = l_Lean_replaceRef(v_ref_2301_, v_ref_2314_);
lean_inc(v_currMacroScope_2319_);
lean_inc(v_maxHeartbeats_2318_);
lean_inc(v_initHeartbeats_2317_);
lean_inc(v_openDecls_2316_);
lean_inc(v_currNamespace_2315_);
lean_inc(v_maxRecDepth_2313_);
lean_inc(v_currRecDepth_2312_);
lean_inc_ref(v_options_2311_);
lean_inc_ref(v_toCold_2310_);
v___x_2323_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2323_, 0, v_toCold_2310_);
lean_ctor_set(v___x_2323_, 1, v_options_2311_);
lean_ctor_set(v___x_2323_, 2, v_currRecDepth_2312_);
lean_ctor_set(v___x_2323_, 3, v_maxRecDepth_2313_);
lean_ctor_set(v___x_2323_, 4, v_ref_2322_);
lean_ctor_set(v___x_2323_, 5, v_currNamespace_2315_);
lean_ctor_set(v___x_2323_, 6, v_openDecls_2316_);
lean_ctor_set(v___x_2323_, 7, v_initHeartbeats_2317_);
lean_ctor_set(v___x_2323_, 8, v_maxHeartbeats_2318_);
lean_ctor_set(v___x_2323_, 9, v_currMacroScope_2319_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*10, v_diag_2320_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*10 + 1, v_suppressElabErrors_2321_);
v___x_2324_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___x_2323_, v___y_2308_);
lean_dec_ref_known(v___x_2323_, 10);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg___boxed(lean_object* v_ref_2325_, lean_object* v_msg_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2325_, v_msg_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v_ref_2325_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(lean_object* v_ref_2335_, lean_object* v_msg_2336_, lean_object* v_declHint_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2345_; lean_object* v_a_2346_; lean_object* v___x_2347_; 
v___x_2345_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2336_, v_declHint_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref(v___x_2345_);
v___x_2347_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2335_, v_a_2346_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg___boxed(lean_object* v_ref_2348_, lean_object* v_msg_2349_, lean_object* v_declHint_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2348_, v_msg_2349_, v_declHint_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v_ref_2348_);
return v_res_2358_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0));
v___x_2361_ = l_Lean_stringToMessageData(v___x_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(lean_object* v_ref_2362_, lean_object* v_constName_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v___x_2371_; uint8_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2371_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1);
v___x_2372_ = 0;
lean_inc(v_constName_2363_);
v___x_2373_ = l_Lean_MessageData_ofConstName(v_constName_2363_, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2371_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2362_, v___x_2376_, v_constName_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___boxed(lean_object* v_ref_2378_, lean_object* v_constName_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2378_, v_constName_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v_ref_2378_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(lean_object* v_constName_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v_ref_2396_; lean_object* v___x_2397_; 
v_ref_2396_ = lean_ctor_get(v___y_2393_, 4);
v___x_2397_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2396_, v_constName_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_constName_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(lean_object* v_constName_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___x_2415_; lean_object* v_env_2416_; uint8_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2415_ = lean_st_ref_get(v___y_2413_);
v_env_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc_ref(v_env_2416_);
lean_dec(v___x_2415_);
v___x_2417_ = 0;
lean_inc(v_constName_2407_);
v___x_2418_ = l_Lean_Environment_findConstVal_x3f(v_env_2416_, v_constName_2407_, v___x_2417_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
return v___x_2419_;
}
else
{
lean_object* v_val_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v_constName_2407_);
v_val_2420_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2418_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_val_2420_);
lean_dec(v___x_2418_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set_tag(v___x_2422_, 0);
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_val_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14___boxed(lean_object* v_constName_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(lean_object* v_constName_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___x_2445_; 
lean_inc(v_constName_2437_);
v___x_2445_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2457_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2457_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2457_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v_levelParams_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
v_levelParams_2450_ = lean_ctor_get(v_a_2446_, 1);
lean_inc(v_levelParams_2450_);
lean_dec(v_a_2446_);
v___x_2451_ = lean_box(0);
v___x_2452_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(v_levelParams_2450_, v___x_2451_);
v___x_2453_ = l_Lean_mkConst(v_constName_2437_, v___x_2452_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2453_);
v___x_2455_ = v___x_2448_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec(v_constName_2437_);
v_a_2458_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2445_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2445_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_constName_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_constName_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(uint8_t v___x_2475_, lean_object* v_declName_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_ref_2484_; lean_object* v___x_2485_; 
v_ref_2484_ = lean_ctor_get(v___y_2481_, 4);
v___x_2485_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_declName_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
lean_dec_ref_known(v___x_2485_, 1);
v___x_2487_ = lean_box(0);
lean_inc(v_ref_2484_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
lean_ctor_set(v___x_2488_, 1, v_ref_2484_);
v___x_2489_ = lean_unsigned_to_nat(32u);
v___x_2490_ = lean_mk_empty_array_with_capacity(v___x_2489_);
lean_dec_ref(v___x_2490_);
v___x_2491_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4);
v___x_2492_ = lean_box(0);
v___x_2493_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2493_, 0, v___x_2488_);
lean_ctor_set(v___x_2493_, 1, v___x_2491_);
lean_ctor_set(v___x_2493_, 2, v___x_2492_);
lean_ctor_set(v___x_2493_, 3, v_a_2486_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*4, v___x_2475_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*4 + 1, v___x_2475_);
v___x_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
v___x_2495_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v___x_2494_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
return v___x_2495_;
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
v_a_2496_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2485_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2485_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v___x_2504_, lean_object* v_declName_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
uint8_t v___x_17483__boxed_2513_; lean_object* v_res_2514_; 
v___x_17483__boxed_2513_ = lean_unbox(v___x_2504_);
v_res_2514_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(v___x_17483__boxed_2513_, v_declName_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(lean_object* v___f_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___x_2523_; lean_object* v_env_2524_; lean_object* v___x_2525_; 
v___x_2523_ = lean_st_ref_get(v___y_2521_);
v_env_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc_ref(v_env_2524_);
lean_dec(v___x_2523_);
v___x_2525_ = lean_apply_8(v___f_2515_, v_env_2524_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, lean_box(0));
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed(lean_object* v___f_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(v___f_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
return v_res_2534_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2535_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
return v___x_2537_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
return v___x_2539_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
v___x_2541_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
lean_ctor_set(v___x_2541_, 2, v___x_2540_);
lean_ctor_set(v___x_2541_, 3, v___x_2540_);
lean_ctor_set(v___x_2541_, 4, v___x_2540_);
lean_ctor_set(v___x_2541_, 5, v___x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(lean_object* v_env_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v___x_2546_; lean_object* v_nextMacroScope_2547_; lean_object* v_ngen_2548_; lean_object* v_auxDeclNGen_2549_; lean_object* v_traceState_2550_; lean_object* v_messages_2551_; lean_object* v_infoState_2552_; lean_object* v_snapshotTasks_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2579_; 
v___x_2546_ = lean_st_ref_take(v___y_2544_);
v_nextMacroScope_2547_ = lean_ctor_get(v___x_2546_, 1);
v_ngen_2548_ = lean_ctor_get(v___x_2546_, 2);
v_auxDeclNGen_2549_ = lean_ctor_get(v___x_2546_, 3);
v_traceState_2550_ = lean_ctor_get(v___x_2546_, 4);
v_messages_2551_ = lean_ctor_get(v___x_2546_, 6);
v_infoState_2552_ = lean_ctor_get(v___x_2546_, 7);
v_snapshotTasks_2553_ = lean_ctor_get(v___x_2546_, 8);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; lean_object* v_unused_2581_; 
v_unused_2580_ = lean_ctor_get(v___x_2546_, 5);
lean_dec(v_unused_2580_);
v_unused_2581_ = lean_ctor_get(v___x_2546_, 0);
lean_dec(v_unused_2581_);
v___x_2555_ = v___x_2546_;
v_isShared_2556_ = v_isSharedCheck_2579_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_snapshotTasks_2553_);
lean_inc(v_infoState_2552_);
lean_inc(v_messages_2551_);
lean_inc(v_traceState_2550_);
lean_inc(v_auxDeclNGen_2549_);
lean_inc(v_ngen_2548_);
lean_inc(v_nextMacroScope_2547_);
lean_dec(v___x_2546_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2579_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2559_; 
v___x_2557_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 5, v___x_2557_);
lean_ctor_set(v___x_2555_, 0, v_env_2542_);
v___x_2559_ = v___x_2555_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_env_2542_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_nextMacroScope_2547_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_ngen_2548_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v_auxDeclNGen_2549_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v_traceState_2550_);
lean_ctor_set(v_reuseFailAlloc_2578_, 5, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2578_, 6, v_messages_2551_);
lean_ctor_set(v_reuseFailAlloc_2578_, 7, v_infoState_2552_);
lean_ctor_set(v_reuseFailAlloc_2578_, 8, v_snapshotTasks_2553_);
v___x_2559_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v_mctx_2562_; lean_object* v_zetaDeltaFVarIds_2563_; lean_object* v_postponed_2564_; lean_object* v_diag_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2576_; 
v___x_2560_ = lean_st_ref_put(v___y_2544_, v___x_2559_);
v___x_2561_ = lean_st_ref_take(v___y_2543_);
v_mctx_2562_ = lean_ctor_get(v___x_2561_, 0);
v_zetaDeltaFVarIds_2563_ = lean_ctor_get(v___x_2561_, 2);
v_postponed_2564_ = lean_ctor_get(v___x_2561_, 3);
v_diag_2565_ = lean_ctor_get(v___x_2561_, 4);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2576_ == 0)
{
lean_object* v_unused_2577_; 
v_unused_2577_ = lean_ctor_get(v___x_2561_, 1);
lean_dec(v_unused_2577_);
v___x_2567_ = v___x_2561_;
v_isShared_2568_ = v_isSharedCheck_2576_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_diag_2565_);
lean_inc(v_postponed_2564_);
lean_inc(v_zetaDeltaFVarIds_2563_);
lean_inc(v_mctx_2562_);
lean_dec(v___x_2561_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2576_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 1, v___x_2569_);
v___x_2571_ = v___x_2567_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_mctx_2562_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2575_, 2, v_zetaDeltaFVarIds_2563_);
lean_ctor_set(v_reuseFailAlloc_2575_, 3, v_postponed_2564_);
lean_ctor_set(v_reuseFailAlloc_2575_, 4, v_diag_2565_);
v___x_2571_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = lean_st_ref_put(v___y_2543_, v___x_2571_);
v___x_2573_ = lean_box(0);
v___x_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
return v___x_2574_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___boxed(lean_object* v_env_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2582_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec(v___y_2583_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(lean_object* v_env_2587_, lean_object* v_x_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v___x_2596_; lean_object* v_env_2597_; lean_object* v_a_2599_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2596_ = lean_st_ref_get(v___y_2594_);
v_env_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc_ref(v_env_2597_);
lean_dec(v___x_2596_);
v___x_2609_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2587_, v___y_2592_, v___y_2594_);
lean_dec_ref(v___x_2609_);
lean_inc(v___y_2594_);
lean_inc_ref(v___y_2593_);
lean_inc(v___y_2592_);
lean_inc_ref(v___y_2591_);
lean_inc(v___y_2590_);
lean_inc_ref(v___y_2589_);
v___x_2610_ = lean_apply_7(v_x_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, lean_box(0));
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v___x_2612_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2597_, v___y_2592_, v___y_2594_);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2619_ == 0)
{
lean_object* v_unused_2620_; 
v_unused_2620_ = lean_ctor_get(v___x_2612_, 0);
lean_dec(v_unused_2620_);
v___x_2614_ = v___x_2612_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_dec(v___x_2612_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v_a_2611_);
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2611_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
else
{
lean_object* v_a_2621_; 
v_a_2621_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2610_, 1);
v_a_2599_ = v_a_2621_;
goto v___jp_2598_;
}
v___jp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
v___x_2600_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2597_, v___y_2592_, v___y_2594_);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2607_ == 0)
{
lean_object* v_unused_2608_; 
v_unused_2608_ = lean_ctor_get(v___x_2600_, 0);
lean_dec(v_unused_2608_);
v___x_2602_ = v___x_2600_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_dec(v___x_2600_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
lean_ctor_set_tag(v___x_2602_, 1);
lean_ctor_set(v___x_2602_, 0, v_a_2599_);
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2599_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_env_2622_, lean_object* v_x_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2622_, v_x_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(lean_object* v_declName_2632_, lean_object* v_env_2633_, lean_object* v_addInfo_2634_, lean_object* v_____r_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Lean_privateToUserName_x3f(v_declName_2632_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
lean_dec_ref(v_addInfo_2634_);
lean_dec_ref(v_env_2633_);
v___x_2644_ = lean_box(0);
v___x_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
return v___x_2645_;
}
else
{
lean_object* v_val_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2663_; 
v_val_2646_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2648_ = v___x_2643_;
v_isShared_2649_ = v_isSharedCheck_2663_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_val_2646_);
lean_dec(v___x_2643_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2663_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
uint8_t v___x_2650_; uint8_t v___x_2651_; 
v___x_2650_ = 1;
lean_inc(v_val_2646_);
v___x_2651_ = l_Lean_Environment_contains(v_env_2633_, v_val_2646_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2654_; 
lean_dec(v_val_2646_);
lean_dec_ref(v_addInfo_2634_);
v___x_2652_ = lean_box(0);
if (v_isShared_2649_ == 0)
{
lean_ctor_set_tag(v___x_2648_, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2652_);
v___x_2654_ = v___x_2648_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
else
{
lean_object* v___x_2656_; 
lean_del_object(v___x_2648_);
lean_inc(v___y_2641_);
lean_inc_ref(v___y_2640_);
lean_inc(v___y_2639_);
lean_inc_ref(v___y_2638_);
lean_inc(v___y_2637_);
lean_inc_ref(v___y_2636_);
lean_inc(v_val_2646_);
v___x_2656_ = lean_apply_8(v_addInfo_2634_, v_val_2646_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, lean_box(0));
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
lean_dec_ref_known(v___x_2656_, 1);
v___x_2657_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
v___x_2658_ = l_Lean_MessageData_ofConstName(v_val_2646_, v___x_2650_);
v___x_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2657_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2661_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
return v___x_2662_;
}
else
{
lean_dec(v_val_2646_);
return v___x_2656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed(lean_object* v_declName_2664_, lean_object* v_env_2665_, lean_object* v_addInfo_2666_, lean_object* v_____r_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(v_declName_2664_, v_env_2665_, v_addInfo_2666_, v_____r_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(lean_object* v_addInfo_2676_, lean_object* v_declName_2677_, uint8_t v___x_2678_, lean_object* v___f_2679_, uint8_t v___x_2680_, lean_object* v_env_2681_, lean_object* v___f_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v___x_2690_; 
lean_inc(v___y_2688_);
lean_inc_ref(v___y_2687_);
lean_inc(v___y_2686_);
lean_inc_ref(v___y_2685_);
lean_inc(v___y_2684_);
lean_inc_ref(v___y_2683_);
lean_inc(v_declName_2677_);
v___x_2690_ = lean_apply_8(v_addInfo_2676_, v_declName_2677_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, lean_box(0));
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v___x_2691_; 
lean_dec_ref_known(v___x_2690_, 1);
lean_inc(v_declName_2677_);
v___x_2691_ = l_Lean_privateToUserName_x3f(v_declName_2677_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2692_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2693_ = l_Lean_MessageData_ofConstName(v_declName_2677_, v___x_2678_);
v___x_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2692_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2696_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
return v___x_2697_;
}
else
{
lean_object* v_val_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
lean_dec(v_declName_2677_);
v_val_2698_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_val_2698_);
lean_dec_ref_known(v___x_2691_, 1);
v___x_2699_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1);
v___x_2700_ = l_Lean_MessageData_ofConstName(v_val_2698_, v___x_2678_);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2703_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
return v___x_2704_;
}
}
else
{
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v_declName_2677_);
return v___x_2690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed(lean_object* v_addInfo_2705_, lean_object* v_declName_2706_, lean_object* v___x_2707_, lean_object* v___f_2708_, lean_object* v___x_2709_, lean_object* v_env_2710_, lean_object* v___f_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
uint8_t v___x_17837__boxed_2719_; uint8_t v___x_17839__boxed_2720_; lean_object* v_res_2721_; 
v___x_17837__boxed_2719_ = lean_unbox(v___x_2707_);
v___x_17839__boxed_2720_ = lean_unbox(v___x_2709_);
v_res_2721_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(v_addInfo_2705_, v_declName_2706_, v___x_17837__boxed_2719_, v___f_2708_, v___x_17839__boxed_2720_, v_env_2710_, v___f_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec_ref(v___f_2711_);
lean_dec_ref(v_env_2710_);
lean_dec_ref(v___f_2708_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(lean_object* v_declName_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2733_; lean_object* v_env_2734_; uint8_t v___x_2735_; lean_object* v_addInfo_2736_; lean_object* v_env_2737_; lean_object* v___f_2738_; lean_object* v___f_2739_; lean_object* v___x_2740_; lean_object* v___f_2741_; uint8_t v___x_2742_; uint8_t v___x_2743_; 
v___x_2733_ = lean_st_ref_get(v___y_2731_);
v_env_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc_ref(v_env_2734_);
lean_dec(v___x_2733_);
v___x_2735_ = 0;
v_addInfo_2736_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0));
v_env_2737_ = l_Lean_Environment_setExporting(v_env_2734_, v___x_2735_);
lean_inc_ref_n(v_env_2737_, 4);
lean_inc_n(v_declName_2725_, 4);
v___f_2738_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed), 11, 3);
lean_closure_set(v___f_2738_, 0, v_declName_2725_);
lean_closure_set(v___f_2738_, 1, v_env_2737_);
lean_closure_set(v___f_2738_, 2, v_addInfo_2736_);
v___f_2739_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2739_, 0, v_env_2737_);
lean_closure_set(v___f_2739_, 1, v_declName_2725_);
lean_closure_set(v___f_2739_, 2, v___f_2738_);
lean_closure_set(v___f_2739_, 3, v_addInfo_2736_);
v___x_2740_ = lean_box(v___x_2735_);
lean_inc_ref(v___f_2739_);
v___f_2741_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed), 12, 4);
lean_closure_set(v___f_2741_, 0, v___f_2739_);
lean_closure_set(v___f_2741_, 1, v_declName_2725_);
lean_closure_set(v___f_2741_, 2, v___x_2740_);
lean_closure_set(v___f_2741_, 3, v_env_2737_);
v___x_2742_ = 1;
v___x_2743_ = l_Lean_Environment_contains(v_env_2737_, v_declName_2725_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_object* v___f_2744_; lean_object* v___x_2745_; 
lean_dec_ref(v___f_2739_);
lean_dec(v_declName_2725_);
v___f_2744_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed), 8, 1);
lean_closure_set(v___f_2744_, 0, v___f_2741_);
v___x_2745_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2737_, v___f_2744_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
return v___x_2745_;
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___f_2748_; lean_object* v___x_2749_; 
v___x_2746_ = lean_box(v___x_2742_);
v___x_2747_ = lean_box(v___x_2735_);
lean_inc_ref(v_env_2737_);
v___f_2748_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed), 14, 7);
lean_closure_set(v___f_2748_, 0, v_addInfo_2736_);
lean_closure_set(v___f_2748_, 1, v_declName_2725_);
lean_closure_set(v___f_2748_, 2, v___x_2746_);
lean_closure_set(v___f_2748_, 3, v___f_2739_);
lean_closure_set(v___f_2748_, 4, v___x_2747_);
lean_closure_set(v___f_2748_, 5, v_env_2737_);
lean_closure_set(v___f_2748_, 6, v___f_2741_);
v___x_2749_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2737_, v___f_2748_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
return v___x_2749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___boxed(lean_object* v_declName_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(lean_object* v_modifiers_2759_, lean_object* v_declName_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v___x_2768_; lean_object* v_env_2769_; uint8_t v_visibility_2770_; uint8_t v_isProtected_2771_; lean_object* v_declName_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; uint8_t v___x_2835_; 
v___x_2768_ = lean_st_ref_get(v___y_2766_);
v_env_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc_ref(v_env_2769_);
lean_dec(v___x_2768_);
v_visibility_2770_ = lean_ctor_get_uint8(v_modifiers_2759_, sizeof(void*)*3);
v_isProtected_2771_ = lean_ctor_get_uint8(v_modifiers_2759_, sizeof(void*)*3 + 1);
v___x_2835_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_2769_, v_visibility_2770_);
lean_dec_ref(v_env_2769_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; lean_object* v_env_2837_; lean_object* v_declName_2838_; 
v___x_2836_ = lean_st_ref_get(v___y_2766_);
v_env_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc_ref(v_env_2837_);
lean_dec(v___x_2836_);
v_declName_2838_ = l_Lean_mkPrivateName(v_env_2837_, v_declName_2760_);
lean_dec_ref(v_env_2837_);
v_declName_2773_ = v_declName_2838_;
v___y_2774_ = v___y_2761_;
v___y_2775_ = v___y_2762_;
v___y_2776_ = v___y_2763_;
v___y_2777_ = v___y_2764_;
v___y_2778_ = v___y_2765_;
v___y_2779_ = v___y_2766_;
goto v___jp_2772_;
}
else
{
v_declName_2773_ = v_declName_2760_;
v___y_2774_ = v___y_2761_;
v___y_2775_ = v___y_2762_;
v___y_2776_ = v___y_2763_;
v___y_2777_ = v___y_2764_;
v___y_2778_ = v___y_2765_;
v___y_2779_ = v___y_2766_;
goto v___jp_2772_;
}
v___jp_2772_:
{
lean_object* v___x_2780_; 
lean_inc(v_declName_2773_);
v___x_2780_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2825_; 
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v___x_2780_, 0);
lean_dec(v_unused_2826_);
v___x_2782_ = v___x_2780_;
v_isShared_2783_ = v_isSharedCheck_2825_;
goto v_resetjp_2781_;
}
else
{
lean_dec(v___x_2780_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2825_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
if (v_isProtected_2771_ == 0)
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v_declName_2773_);
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_declName_2773_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
else
{
lean_object* v___x_2787_; lean_object* v_env_2788_; lean_object* v_nextMacroScope_2789_; lean_object* v_ngen_2790_; lean_object* v_auxDeclNGen_2791_; lean_object* v_traceState_2792_; lean_object* v_messages_2793_; lean_object* v_infoState_2794_; lean_object* v_snapshotTasks_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2823_; 
v___x_2787_ = lean_st_ref_take(v___y_2779_);
v_env_2788_ = lean_ctor_get(v___x_2787_, 0);
v_nextMacroScope_2789_ = lean_ctor_get(v___x_2787_, 1);
v_ngen_2790_ = lean_ctor_get(v___x_2787_, 2);
v_auxDeclNGen_2791_ = lean_ctor_get(v___x_2787_, 3);
v_traceState_2792_ = lean_ctor_get(v___x_2787_, 4);
v_messages_2793_ = lean_ctor_get(v___x_2787_, 6);
v_infoState_2794_ = lean_ctor_get(v___x_2787_, 7);
v_snapshotTasks_2795_ = lean_ctor_get(v___x_2787_, 8);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v___x_2787_, 5);
lean_dec(v_unused_2824_);
v___x_2797_ = v___x_2787_;
v_isShared_2798_ = v_isSharedCheck_2823_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_snapshotTasks_2795_);
lean_inc(v_infoState_2794_);
lean_inc(v_messages_2793_);
lean_inc(v_traceState_2792_);
lean_inc(v_auxDeclNGen_2791_);
lean_inc(v_ngen_2790_);
lean_inc(v_nextMacroScope_2789_);
lean_inc(v_env_2788_);
lean_dec(v___x_2787_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2823_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2802_; 
lean_inc(v_declName_2773_);
v___x_2799_ = l_Lean_addProtected(v_env_2788_, v_declName_2773_);
v___x_2800_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 5, v___x_2800_);
lean_ctor_set(v___x_2797_, 0, v___x_2799_);
v___x_2802_ = v___x_2797_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_nextMacroScope_2789_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_ngen_2790_);
lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_auxDeclNGen_2791_);
lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_traceState_2792_);
lean_ctor_set(v_reuseFailAlloc_2822_, 5, v___x_2800_);
lean_ctor_set(v_reuseFailAlloc_2822_, 6, v_messages_2793_);
lean_ctor_set(v_reuseFailAlloc_2822_, 7, v_infoState_2794_);
lean_ctor_set(v_reuseFailAlloc_2822_, 8, v_snapshotTasks_2795_);
v___x_2802_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v_mctx_2805_; lean_object* v_zetaDeltaFVarIds_2806_; lean_object* v_postponed_2807_; lean_object* v_diag_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2820_; 
v___x_2803_ = lean_st_ref_put(v___y_2779_, v___x_2802_);
v___x_2804_ = lean_st_ref_take(v___y_2777_);
v_mctx_2805_ = lean_ctor_get(v___x_2804_, 0);
v_zetaDeltaFVarIds_2806_ = lean_ctor_get(v___x_2804_, 2);
v_postponed_2807_ = lean_ctor_get(v___x_2804_, 3);
v_diag_2808_ = lean_ctor_get(v___x_2804_, 4);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2820_ == 0)
{
lean_object* v_unused_2821_; 
v_unused_2821_ = lean_ctor_get(v___x_2804_, 1);
lean_dec(v_unused_2821_);
v___x_2810_ = v___x_2804_;
v_isShared_2811_ = v_isSharedCheck_2820_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_diag_2808_);
lean_inc(v_postponed_2807_);
lean_inc(v_zetaDeltaFVarIds_2806_);
lean_inc(v_mctx_2805_);
lean_dec(v___x_2804_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2820_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2812_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 1, v___x_2812_);
v___x_2814_ = v___x_2810_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_mctx_2805_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2819_, 2, v_zetaDeltaFVarIds_2806_);
lean_ctor_set(v_reuseFailAlloc_2819_, 3, v_postponed_2807_);
lean_ctor_set(v_reuseFailAlloc_2819_, 4, v_diag_2808_);
v___x_2814_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2815_ = lean_st_ref_put(v___y_2777_, v___x_2814_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v_declName_2773_);
v___x_2817_ = v___x_2782_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_declName_2773_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
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
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec(v_declName_2773_);
v_a_2827_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2780_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2780_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4___boxed(lean_object* v_modifiers_2839_, lean_object* v_declName_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2839_, v_declName_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec_ref(v_modifiers_2839_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(lean_object* v_pre_2849_, lean_object* v_declName_2850_, lean_object* v_as_2851_, size_t v_sz_2852_, size_t v_i_2853_, lean_object* v_b_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v_a_2863_; uint8_t v___x_2867_; 
v___x_2867_ = lean_usize_dec_lt(v_i_2853_, v_sz_2852_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; 
lean_dec(v_declName_2850_);
lean_dec(v_pre_2849_);
v___x_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2868_, 0, v_b_2854_);
return v___x_2868_;
}
else
{
lean_object* v___x_2869_; lean_object* v_a_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2869_ = lean_box(0);
v_a_2870_ = lean_array_uget_borrowed(v_as_2851_, v_i_2853_);
lean_inc(v_a_2870_);
lean_inc(v_pre_2849_);
v___x_2871_ = l_Lean_Name_append(v_pre_2849_, v_a_2870_);
v___x_2872_ = lean_name_eq(v___x_2871_, v_declName_2850_);
lean_dec(v___x_2871_);
if (v___x_2872_ == 0)
{
v_a_2863_ = v___x_2869_;
goto v___jp_2862_;
}
else
{
lean_object* v___x_2873_; uint8_t v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2873_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_2874_ = 0;
lean_inc(v_declName_2850_);
v___x_2875_ = l_Lean_MessageData_ofConstName(v_declName_2850_, v___x_2874_);
v___x_2876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2873_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
v___x_2877_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_2878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2876_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
lean_inc(v_pre_2849_);
v___x_2879_ = l_Lean_MessageData_ofName(v_pre_2849_);
v___x_2880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2878_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
v___x_2881_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2880_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
lean_inc(v_a_2870_);
v___x_2883_ = l_Lean_MessageData_ofName(v_a_2870_);
v___x_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2882_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2884_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
v___x_2887_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2886_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_dec_ref_known(v___x_2887_, 1);
v_a_2863_ = v___x_2869_;
goto v___jp_2862_;
}
else
{
lean_dec(v_declName_2850_);
lean_dec(v_pre_2849_);
return v___x_2887_;
}
}
}
v___jp_2862_:
{
size_t v___x_2864_; size_t v___x_2865_; 
v___x_2864_ = ((size_t)1ULL);
v___x_2865_ = lean_usize_add(v_i_2853_, v___x_2864_);
v_i_2853_ = v___x_2865_;
v_b_2854_ = v_a_2863_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6___boxed(lean_object* v_pre_2888_, lean_object* v_declName_2889_, lean_object* v_as_2890_, lean_object* v_sz_2891_, lean_object* v_i_2892_, lean_object* v_b_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
size_t v_sz_boxed_2901_; size_t v_i_boxed_2902_; lean_object* v_res_2903_; 
v_sz_boxed_2901_ = lean_unbox_usize(v_sz_2891_);
lean_dec(v_sz_2891_);
v_i_boxed_2902_ = lean_unbox_usize(v_i_2892_);
lean_dec(v_i_2892_);
v_res_2903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2888_, v_declName_2889_, v_as_2890_, v_sz_boxed_2901_, v_i_boxed_2902_, v_b_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec_ref(v_as_2890_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(lean_object* v_declName_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
if (lean_obj_tag(v_declName_2904_) == 1)
{
lean_object* v_pre_2912_; lean_object* v___x_2913_; lean_object* v_env_2914_; uint8_t v___x_2915_; 
v_pre_2912_ = lean_ctor_get(v_declName_2904_, 0);
lean_inc_n(v_pre_2912_, 2);
v___x_2913_ = lean_st_ref_get(v___y_2910_);
v_env_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc_ref(v_env_2914_);
lean_dec(v___x_2913_);
v___x_2915_ = l_Lean_isStructure(v_env_2914_, v_pre_2912_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
lean_dec_ref_known(v_declName_2904_, 2);
lean_dec(v_pre_2912_);
v___x_2916_ = lean_box(0);
v___x_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
return v___x_2917_;
}
else
{
lean_object* v___x_2918_; lean_object* v_env_2919_; lean_object* v_fieldNames_2920_; lean_object* v___x_2921_; size_t v_sz_2922_; size_t v___x_2923_; lean_object* v___x_2924_; 
v___x_2918_ = lean_st_ref_get(v___y_2910_);
v_env_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc_ref(v_env_2919_);
lean_dec(v___x_2918_);
lean_inc(v_pre_2912_);
v_fieldNames_2920_ = l_Lean_getStructureFieldsFlattened(v_env_2919_, v_pre_2912_, v___x_2915_);
v___x_2921_ = lean_box(0);
v_sz_2922_ = lean_array_size(v_fieldNames_2920_);
v___x_2923_ = ((size_t)0ULL);
v___x_2924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2912_, v_declName_2904_, v_fieldNames_2920_, v_sz_2922_, v___x_2923_, v___x_2921_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec_ref(v_fieldNames_2920_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2931_ == 0)
{
lean_object* v_unused_2932_; 
v_unused_2932_ = lean_ctor_get(v___x_2924_, 0);
lean_dec(v_unused_2932_);
v___x_2926_ = v___x_2924_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_dec(v___x_2924_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2921_);
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2921_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
else
{
return v___x_2924_;
}
}
}
else
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_dec(v_declName_2904_);
v___x_2933_ = lean_box(0);
v___x_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
return v___x_2934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3___boxed(lean_object* v_declName_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v_declName_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(lean_object* v_currNamespace_2944_, lean_object* v_modifiers_2945_, lean_object* v_shortName_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2960_; lean_object* v_shortName_2961_; lean_object* v_currNamespace_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v_view_3022_; lean_object* v_name_3023_; lean_object* v_imported_3024_; lean_object* v_ctx_3025_; lean_object* v_scopes_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3084_; 
lean_inc(v_shortName_2946_);
v_view_3022_ = l_Lean_extractMacroScopes(v_shortName_2946_);
v_name_3023_ = lean_ctor_get(v_view_3022_, 0);
v_imported_3024_ = lean_ctor_get(v_view_3022_, 1);
v_ctx_3025_ = lean_ctor_get(v_view_3022_, 2);
v_scopes_3026_ = lean_ctor_get(v_view_3022_, 3);
v_isSharedCheck_3084_ = !lean_is_exclusive(v_view_3022_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3028_ = v_view_3022_;
v_isShared_3029_ = v_isSharedCheck_3084_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_scopes_3026_);
lean_inc(v_ctx_3025_);
lean_inc(v_imported_3024_);
lean_inc(v_name_3023_);
lean_dec(v_view_3022_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3084_;
goto v_resetjp_3027_;
}
v___jp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___y_2956_);
lean_ctor_set(v___x_2957_, 1, v___y_2955_);
v___x_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
return v___x_2958_;
}
v___jp_2959_:
{
lean_object* v___x_2969_; 
lean_inc(v___y_2960_);
v___x_2969_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v___y_2960_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v___x_2970_; 
lean_dec_ref_known(v___x_2969_, 1);
v___x_2970_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2945_, v___y_2960_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
if (lean_obj_tag(v___x_2970_) == 0)
{
uint8_t v_isProtected_2971_; 
v_isProtected_2971_ = lean_ctor_get_uint8(v_modifiers_2945_, sizeof(void*)*3 + 1);
if (v_isProtected_2971_ == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2980_; 
lean_dec(v_currNamespace_2962_);
v_a_2972_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2974_ = v___x_2970_;
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2970_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v_a_2972_);
lean_ctor_set(v___x_2976_, 1, v_shortName_2961_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2976_);
v___x_2978_ = v___x_2974_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
else
{
if (lean_obj_tag(v_currNamespace_2962_) == 1)
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2993_; 
v_a_2981_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2983_ = v___x_2970_;
v_isShared_2984_ = v_isSharedCheck_2993_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2970_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2993_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v_str_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2991_; 
v_str_2985_ = lean_ctor_get(v_currNamespace_2962_, 1);
lean_inc_ref(v_str_2985_);
lean_dec_ref_known(v_currNamespace_2962_, 2);
v___x_2986_ = lean_box(0);
v___x_2987_ = l_Lean_Name_str___override(v___x_2986_, v_str_2985_);
v___x_2988_ = l_Lean_Name_append(v___x_2987_, v_shortName_2961_);
v___x_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2989_, 0, v_a_2981_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 0, v___x_2989_);
v___x_2991_ = v___x_2983_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
else
{
lean_object* v_a_2994_; uint8_t v___x_2995_; 
lean_dec(v_currNamespace_2962_);
v_a_2994_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2970_, 1);
v___x_2995_ = l_Lean_Name_isAtomic(v_shortName_2961_);
if (v___x_2995_ == 0)
{
v___y_2955_ = v_shortName_2961_;
v___y_2956_ = v_a_2994_;
goto v___jp_2954_;
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec(v_a_2994_);
lean_dec(v_shortName_2961_);
v___x_2996_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_2997_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2996_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2997_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec(v_currNamespace_2962_);
lean_dec(v_shortName_2961_);
v_a_3006_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2970_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2970_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v_currNamespace_2962_);
lean_dec(v_shortName_2961_);
lean_dec(v___y_2960_);
v_a_3014_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2969_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2969_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; uint8_t v_isRootName_3031_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; uint8_t v___x_3073_; 
v___x_3030_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_3031_ = l_Lean_Name_isPrefixOf(v___x_3030_, v_name_3023_);
v___x_3073_ = lean_name_eq(v_name_3023_, v___x_3030_);
if (v___x_3073_ == 0)
{
v___y_3060_ = v___y_2947_;
v___y_3061_ = v___y_2948_;
v___y_3062_ = v___y_2949_;
v___y_3063_ = v___y_2950_;
v___y_3064_ = v___y_2951_;
v___y_3065_ = v___y_2952_;
goto v___jp_3059_;
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_del_object(v___x_3028_);
lean_dec(v_scopes_3026_);
lean_dec(v_ctx_3025_);
lean_dec(v_imported_3024_);
lean_dec(v_name_3023_);
lean_dec(v_shortName_2946_);
lean_dec(v_currNamespace_2944_);
v___x_3074_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_3075_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3074_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
v___jp_3032_:
{
if (v_isRootName_3031_ == 0)
{
lean_dec(v_name_3023_);
v___y_2960_ = v___y_3039_;
v_shortName_2961_ = v_shortName_2946_;
v_currNamespace_2962_ = v_currNamespace_2944_;
v___y_2963_ = v___y_3036_;
v___y_2964_ = v___y_3037_;
v___y_2965_ = v___y_3034_;
v___y_2966_ = v___y_3033_;
v___y_2967_ = v___y_3038_;
v___y_2968_ = v___y_3035_;
goto v___jp_2959_;
}
else
{
lean_dec(v_shortName_2946_);
lean_dec(v_currNamespace_2944_);
if (lean_obj_tag(v_name_3023_) == 1)
{
lean_object* v_pre_3040_; lean_object* v_str_3041_; lean_object* v___x_3042_; lean_object* v_shortName_3043_; lean_object* v_currNamespace_3044_; 
v_pre_3040_ = lean_ctor_get(v_name_3023_, 0);
lean_inc(v_pre_3040_);
v_str_3041_ = lean_ctor_get(v_name_3023_, 1);
lean_inc_ref(v_str_3041_);
lean_dec_ref_known(v_name_3023_, 2);
v___x_3042_ = lean_box(0);
v_shortName_3043_ = l_Lean_Name_str___override(v___x_3042_, v_str_3041_);
v_currNamespace_3044_ = l_Lean_Name_replacePrefix(v_pre_3040_, v___x_3030_, v___x_3042_);
v___y_2960_ = v___y_3039_;
v_shortName_2961_ = v_shortName_3043_;
v_currNamespace_2962_ = v_currNamespace_3044_;
v___y_2963_ = v___y_3036_;
v___y_2964_ = v___y_3037_;
v___y_2965_ = v___y_3034_;
v___y_2966_ = v___y_3033_;
v___y_2967_ = v___y_3038_;
v___y_2968_ = v___y_3035_;
goto v___jp_2959_;
}
else
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec(v___y_3039_);
v___x_3045_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_3046_ = l_Lean_MessageData_ofName(v_name_3023_);
v___x_3047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3045_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v___x_3048_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_3049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3047_);
lean_ctor_set(v___x_3049_, 1, v___x_3048_);
v___x_3050_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3049_, v___y_3036_, v___y_3037_, v___y_3034_, v___y_3033_, v___y_3038_, v___y_3035_);
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3050_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3050_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
v___jp_3059_:
{
if (v_isRootName_3031_ == 0)
{
lean_object* v___x_3066_; 
lean_del_object(v___x_3028_);
lean_dec(v_scopes_3026_);
lean_dec(v_ctx_3025_);
lean_dec(v_imported_3024_);
lean_inc(v_shortName_2946_);
lean_inc(v_currNamespace_2944_);
v___x_3066_ = l_Lean_Name_append(v_currNamespace_2944_, v_shortName_2946_);
v___y_3033_ = v___y_3063_;
v___y_3034_ = v___y_3062_;
v___y_3035_ = v___y_3065_;
v___y_3036_ = v___y_3060_;
v___y_3037_ = v___y_3061_;
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___x_3066_;
goto v___jp_3032_;
}
else
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3070_; 
v___x_3067_ = lean_box(0);
lean_inc(v_name_3023_);
v___x_3068_ = l_Lean_Name_replacePrefix(v_name_3023_, v___x_3030_, v___x_3067_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 0, v___x_3068_);
v___x_3070_ = v___x_3028_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3068_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_imported_3024_);
lean_ctor_set(v_reuseFailAlloc_3072_, 2, v_ctx_3025_);
lean_ctor_set(v_reuseFailAlloc_3072_, 3, v_scopes_3026_);
v___x_3070_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; 
v___x_3071_ = l_Lean_MacroScopesView_review(v___x_3070_);
v___y_3033_ = v___y_3063_;
v___y_3034_ = v___y_3062_;
v___y_3035_ = v___y_3065_;
v___y_3036_ = v___y_3060_;
v___y_3037_ = v___y_3061_;
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___x_3071_;
goto v___jp_3032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2___boxed(lean_object* v_currNamespace_3085_, lean_object* v_modifiers_3086_, lean_object* v_shortName_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3085_, v_modifiers_3086_, v_shortName_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec_ref(v_modifiers_3086_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(uint8_t v___x_3096_, lean_object* v_as_3097_, size_t v_i_3098_, size_t v_stop_3099_, lean_object* v_b_3100_){
_start:
{
lean_object* v___y_3102_; uint8_t v___x_3106_; 
v___x_3106_ = lean_usize_dec_eq(v_i_3098_, v_stop_3099_);
if (v___x_3106_ == 0)
{
lean_object* v_fst_3107_; uint8_t v___x_3108_; 
v_fst_3107_ = lean_ctor_get(v_b_3100_, 0);
v___x_3108_ = lean_unbox(v_fst_3107_);
if (v___x_3108_ == 0)
{
lean_object* v_snd_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3118_; 
v_snd_3109_ = lean_ctor_get(v_b_3100_, 1);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_b_3100_);
if (v_isSharedCheck_3118_ == 0)
{
lean_object* v_unused_3119_; 
v_unused_3119_ = lean_ctor_get(v_b_3100_, 0);
lean_dec(v_unused_3119_);
v___x_3111_ = v_b_3100_;
v_isShared_3112_ = v_isSharedCheck_3118_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_snd_3109_);
lean_dec(v_b_3100_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3118_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
uint8_t v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3116_; 
v___x_3113_ = 1;
v___x_3114_ = lean_box(v___x_3113_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v___x_3114_);
v___x_3116_ = v___x_3111_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_snd_3109_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
v___y_3102_ = v___x_3116_;
goto v___jp_3101_;
}
}
}
else
{
lean_object* v_snd_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3130_; 
v_snd_3120_ = lean_ctor_get(v_b_3100_, 1);
v_isSharedCheck_3130_ = !lean_is_exclusive(v_b_3100_);
if (v_isSharedCheck_3130_ == 0)
{
lean_object* v_unused_3131_; 
v_unused_3131_ = lean_ctor_get(v_b_3100_, 0);
lean_dec(v_unused_3131_);
v___x_3122_ = v_b_3100_;
v_isShared_3123_ = v_isSharedCheck_3130_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_snd_3120_);
lean_dec(v_b_3100_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3130_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3124_ = lean_array_uget_borrowed(v_as_3097_, v_i_3098_);
lean_inc(v___x_3124_);
v___x_3125_ = lean_array_push(v_snd_3120_, v___x_3124_);
v___x_3126_ = lean_box(v___x_3096_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 1, v___x_3125_);
lean_ctor_set(v___x_3122_, 0, v___x_3126_);
v___x_3128_ = v___x_3122_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v___x_3125_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
v___y_3102_ = v___x_3128_;
goto v___jp_3101_;
}
}
}
}
else
{
return v_b_3100_;
}
v___jp_3101_:
{
size_t v___x_3103_; size_t v___x_3104_; 
v___x_3103_ = ((size_t)1ULL);
v___x_3104_ = lean_usize_add(v_i_3098_, v___x_3103_);
v_i_3098_ = v___x_3104_;
v_b_3100_ = v___y_3102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4___boxed(lean_object* v___x_3132_, lean_object* v_as_3133_, lean_object* v_i_3134_, lean_object* v_stop_3135_, lean_object* v_b_3136_){
_start:
{
uint8_t v___x_18546__boxed_3137_; size_t v_i_boxed_3138_; size_t v_stop_boxed_3139_; lean_object* v_res_3140_; 
v___x_18546__boxed_3137_ = lean_unbox(v___x_3132_);
v_i_boxed_3138_ = lean_unbox_usize(v_i_3134_);
lean_dec(v_i_3134_);
v_stop_boxed_3139_ = lean_unbox_usize(v_stop_3135_);
lean_dec(v_stop_3135_);
v_res_3140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_18546__boxed_3137_, v_as_3133_, v_i_boxed_3138_, v_stop_boxed_3139_, v_b_3136_);
lean_dec_ref(v_as_3133_);
return v_res_3140_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(lean_object* v_a_3141_, lean_object* v_x_3142_){
_start:
{
if (lean_obj_tag(v_x_3142_) == 0)
{
uint8_t v___x_3143_; 
v___x_3143_ = 0;
return v___x_3143_;
}
else
{
lean_object* v_head_3144_; lean_object* v_tail_3145_; uint8_t v___x_3146_; 
v_head_3144_ = lean_ctor_get(v_x_3142_, 0);
v_tail_3145_ = lean_ctor_get(v_x_3142_, 1);
v___x_3146_ = lean_name_eq(v_a_3141_, v_head_3144_);
if (v___x_3146_ == 0)
{
v_x_3142_ = v_tail_3145_;
goto _start;
}
else
{
return v___x_3146_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_expandDeclId_spec__0___boxed(lean_object* v_a_3148_, lean_object* v_x_3149_){
_start:
{
uint8_t v_res_3150_; lean_object* v_r_3151_; 
v_res_3150_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_a_3148_, v_x_3149_);
lean_dec(v_x_3149_);
lean_dec(v_a_3148_);
v_r_3151_ = lean_box(v_res_3150_);
return v_r_3151_;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = ((lean_object*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0));
v___x_3154_ = l_Lean_stringToMessageData(v___x_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(lean_object* v_u_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3163_ = lean_obj_once(&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1, &l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1);
v___x_3164_ = l_Lean_MessageData_ofName(v_u_3155_);
v___x_3165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3163_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_3167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3165_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3167_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___boxed(lean_object* v_u_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(lean_object* v_as_3178_, size_t v_i_3179_, size_t v_stop_3180_, lean_object* v_b_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_a_3190_; uint8_t v___x_3194_; 
v___x_3194_ = lean_usize_dec_eq(v_i_3179_, v_stop_3180_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3195_; lean_object* v_id_3196_; uint8_t v___x_3197_; 
v___x_3195_ = lean_array_uget_borrowed(v_as_3178_, v_i_3179_);
v_id_3196_ = l_Lean_Syntax_getId(v___x_3195_);
v___x_3197_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_id_3196_, v_b_3181_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; 
v___x_3198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3198_, 0, v_id_3196_);
lean_ctor_set(v___x_3198_, 1, v_b_3181_);
v_a_3190_ = v___x_3198_;
goto v___jp_3189_;
}
else
{
lean_object* v_toCold_3199_; lean_object* v_options_3200_; lean_object* v_currRecDepth_3201_; lean_object* v_maxRecDepth_3202_; lean_object* v_ref_3203_; lean_object* v_currNamespace_3204_; lean_object* v_openDecls_3205_; lean_object* v_initHeartbeats_3206_; lean_object* v_maxHeartbeats_3207_; lean_object* v_currMacroScope_3208_; uint8_t v_diag_3209_; uint8_t v_suppressElabErrors_3210_; lean_object* v_ref_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
lean_dec(v_b_3181_);
v_toCold_3199_ = lean_ctor_get(v___y_3186_, 0);
v_options_3200_ = lean_ctor_get(v___y_3186_, 1);
v_currRecDepth_3201_ = lean_ctor_get(v___y_3186_, 2);
v_maxRecDepth_3202_ = lean_ctor_get(v___y_3186_, 3);
v_ref_3203_ = lean_ctor_get(v___y_3186_, 4);
v_currNamespace_3204_ = lean_ctor_get(v___y_3186_, 5);
v_openDecls_3205_ = lean_ctor_get(v___y_3186_, 6);
v_initHeartbeats_3206_ = lean_ctor_get(v___y_3186_, 7);
v_maxHeartbeats_3207_ = lean_ctor_get(v___y_3186_, 8);
v_currMacroScope_3208_ = lean_ctor_get(v___y_3186_, 9);
v_diag_3209_ = lean_ctor_get_uint8(v___y_3186_, sizeof(void*)*10);
v_suppressElabErrors_3210_ = lean_ctor_get_uint8(v___y_3186_, sizeof(void*)*10 + 1);
v_ref_3211_ = l_Lean_replaceRef(v___x_3195_, v_ref_3203_);
lean_inc(v_currMacroScope_3208_);
lean_inc(v_maxHeartbeats_3207_);
lean_inc(v_initHeartbeats_3206_);
lean_inc(v_openDecls_3205_);
lean_inc(v_currNamespace_3204_);
lean_inc(v_maxRecDepth_3202_);
lean_inc(v_currRecDepth_3201_);
lean_inc_ref(v_options_3200_);
lean_inc_ref(v_toCold_3199_);
v___x_3212_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3212_, 0, v_toCold_3199_);
lean_ctor_set(v___x_3212_, 1, v_options_3200_);
lean_ctor_set(v___x_3212_, 2, v_currRecDepth_3201_);
lean_ctor_set(v___x_3212_, 3, v_maxRecDepth_3202_);
lean_ctor_set(v___x_3212_, 4, v_ref_3211_);
lean_ctor_set(v___x_3212_, 5, v_currNamespace_3204_);
lean_ctor_set(v___x_3212_, 6, v_openDecls_3205_);
lean_ctor_set(v___x_3212_, 7, v_initHeartbeats_3206_);
lean_ctor_set(v___x_3212_, 8, v_maxHeartbeats_3207_);
lean_ctor_set(v___x_3212_, 9, v_currMacroScope_3208_);
lean_ctor_set_uint8(v___x_3212_, sizeof(void*)*10, v_diag_3209_);
lean_ctor_set_uint8(v___x_3212_, sizeof(void*)*10 + 1, v_suppressElabErrors_3210_);
v___x_3213_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_id_3196_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___x_3212_, v___y_3187_);
lean_dec_ref_known(v___x_3212_, 10);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___x_3213_, 1);
v_a_3190_ = v_a_3214_;
goto v___jp_3189_;
}
else
{
return v___x_3213_;
}
}
}
else
{
lean_object* v___x_3215_; 
v___x_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3215_, 0, v_b_3181_);
return v___x_3215_;
}
v___jp_3189_:
{
size_t v___x_3191_; size_t v___x_3192_; 
v___x_3191_ = ((size_t)1ULL);
v___x_3192_ = lean_usize_add(v_i_3179_, v___x_3191_);
v_i_3179_ = v___x_3192_;
v_b_3181_ = v_a_3190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3___boxed(lean_object* v_as_3216_, lean_object* v_i_3217_, lean_object* v_stop_3218_, lean_object* v_b_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
size_t v_i_boxed_3227_; size_t v_stop_boxed_3228_; lean_object* v_res_3229_; 
v_i_boxed_3227_ = lean_unbox_usize(v_i_3217_);
lean_dec(v_i_3217_);
v_stop_boxed_3228_ = lean_unbox_usize(v_stop_3218_);
lean_dec(v_stop_3218_);
v_res_3229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v_as_3216_, v_i_boxed_3227_, v_stop_boxed_3228_, v_b_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec_ref(v_as_3216_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId(lean_object* v_currNamespace_3230_, lean_object* v_currLevelNames_3231_, lean_object* v_declId_3232_, lean_object* v_modifiers_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v___x_3241_; lean_object* v_fst_3242_; lean_object* v_snd_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3329_; 
v___x_3241_ = l_Lean_Elab_expandDeclIdCore(v_declId_3232_);
v_fst_3242_ = lean_ctor_get(v___x_3241_, 0);
v_snd_3243_ = lean_ctor_get(v___x_3241_, 1);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3245_ = v___x_3241_;
v_isShared_3246_ = v_isSharedCheck_3329_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_snd_3243_);
lean_inc(v_fst_3242_);
lean_dec(v___x_3241_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3329_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v_levelNames_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3291_; lean_object* v___y_3302_; uint8_t v___x_3313_; 
v___x_3313_ = l_Lean_Syntax_isNone(v_snd_3243_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3314_ = lean_unsigned_to_nat(1u);
v___x_3315_ = l_Lean_Syntax_getArg(v_snd_3243_, v___x_3314_);
lean_dec(v_snd_3243_);
v___x_3316_ = l_Lean_Syntax_getArgs(v___x_3315_);
lean_dec(v___x_3315_);
v___x_3317_ = lean_unsigned_to_nat(0u);
v___x_3318_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__0));
v___x_3319_ = lean_array_get_size(v___x_3316_);
v___x_3320_ = lean_nat_dec_lt(v___x_3317_, v___x_3319_);
if (v___x_3320_ == 0)
{
lean_dec_ref(v___x_3316_);
lean_del_object(v___x_3245_);
v___y_3302_ = v___x_3318_;
goto v___jp_3301_;
}
else
{
lean_object* v___x_3321_; lean_object* v___x_3323_; 
v___x_3321_ = lean_box(v___x_3320_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 1, v___x_3318_);
lean_ctor_set(v___x_3245_, 0, v___x_3321_);
v___x_3323_ = v___x_3245_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3328_, 1, v___x_3318_);
v___x_3323_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
size_t v___x_3324_; size_t v___x_3325_; lean_object* v___x_3326_; lean_object* v_snd_3327_; 
v___x_3324_ = ((size_t)0ULL);
v___x_3325_ = lean_usize_of_nat(v___x_3319_);
v___x_3326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3313_, v___x_3316_, v___x_3324_, v___x_3325_, v___x_3323_);
lean_dec_ref(v___x_3316_);
v_snd_3327_ = lean_ctor_get(v___x_3326_, 1);
lean_inc(v_snd_3327_);
lean_dec_ref(v___x_3326_);
v___y_3302_ = v_snd_3327_;
goto v___jp_3301_;
}
}
}
else
{
lean_del_object(v___x_3245_);
lean_dec(v_snd_3243_);
v_levelNames_3248_ = v_currLevelNames_3231_;
v___y_3249_ = v_a_3234_;
v___y_3250_ = v_a_3235_;
v___y_3251_ = v_a_3236_;
v___y_3252_ = v_a_3237_;
v___y_3253_ = v_a_3238_;
v___y_3254_ = v_a_3239_;
goto v___jp_3247_;
}
v___jp_3247_:
{
lean_object* v_toCold_3255_; lean_object* v_options_3256_; lean_object* v_currRecDepth_3257_; lean_object* v_maxRecDepth_3258_; lean_object* v_ref_3259_; lean_object* v_currNamespace_3260_; lean_object* v_openDecls_3261_; lean_object* v_initHeartbeats_3262_; lean_object* v_maxHeartbeats_3263_; lean_object* v_currMacroScope_3264_; uint8_t v_diag_3265_; uint8_t v_suppressElabErrors_3266_; lean_object* v_ref_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v_toCold_3255_ = lean_ctor_get(v___y_3253_, 0);
v_options_3256_ = lean_ctor_get(v___y_3253_, 1);
v_currRecDepth_3257_ = lean_ctor_get(v___y_3253_, 2);
v_maxRecDepth_3258_ = lean_ctor_get(v___y_3253_, 3);
v_ref_3259_ = lean_ctor_get(v___y_3253_, 4);
v_currNamespace_3260_ = lean_ctor_get(v___y_3253_, 5);
v_openDecls_3261_ = lean_ctor_get(v___y_3253_, 6);
v_initHeartbeats_3262_ = lean_ctor_get(v___y_3253_, 7);
v_maxHeartbeats_3263_ = lean_ctor_get(v___y_3253_, 8);
v_currMacroScope_3264_ = lean_ctor_get(v___y_3253_, 9);
v_diag_3265_ = lean_ctor_get_uint8(v___y_3253_, sizeof(void*)*10);
v_suppressElabErrors_3266_ = lean_ctor_get_uint8(v___y_3253_, sizeof(void*)*10 + 1);
v_ref_3267_ = l_Lean_replaceRef(v_declId_3232_, v_ref_3259_);
lean_inc(v_currMacroScope_3264_);
lean_inc(v_maxHeartbeats_3263_);
lean_inc(v_initHeartbeats_3262_);
lean_inc(v_openDecls_3261_);
lean_inc(v_currNamespace_3260_);
lean_inc(v_maxRecDepth_3258_);
lean_inc(v_currRecDepth_3257_);
lean_inc_ref(v_options_3256_);
lean_inc_ref(v_toCold_3255_);
v___x_3268_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3268_, 0, v_toCold_3255_);
lean_ctor_set(v___x_3268_, 1, v_options_3256_);
lean_ctor_set(v___x_3268_, 2, v_currRecDepth_3257_);
lean_ctor_set(v___x_3268_, 3, v_maxRecDepth_3258_);
lean_ctor_set(v___x_3268_, 4, v_ref_3267_);
lean_ctor_set(v___x_3268_, 5, v_currNamespace_3260_);
lean_ctor_set(v___x_3268_, 6, v_openDecls_3261_);
lean_ctor_set(v___x_3268_, 7, v_initHeartbeats_3262_);
lean_ctor_set(v___x_3268_, 8, v_maxHeartbeats_3263_);
lean_ctor_set(v___x_3268_, 9, v_currMacroScope_3264_);
lean_ctor_set_uint8(v___x_3268_, sizeof(void*)*10, v_diag_3265_);
lean_ctor_set_uint8(v___x_3268_, sizeof(void*)*10 + 1, v_suppressElabErrors_3266_);
v___x_3269_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3230_, v_modifiers_3233_, v_fst_3242_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___x_3268_, v___y_3254_);
lean_dec_ref_known(v___x_3268_, 10);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3281_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3272_ = v___x_3269_;
v_isShared_3273_ = v_isSharedCheck_3281_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3281_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v_fst_3274_; lean_object* v_snd_3275_; lean_object* v_docString_x3f_3276_; lean_object* v___x_3277_; lean_object* v___x_3279_; 
v_fst_3274_ = lean_ctor_get(v_a_3270_, 0);
lean_inc(v_fst_3274_);
v_snd_3275_ = lean_ctor_get(v_a_3270_, 1);
lean_inc(v_snd_3275_);
lean_dec(v_a_3270_);
v_docString_x3f_3276_ = lean_ctor_get(v_modifiers_3233_, 1);
lean_inc(v_docString_x3f_3276_);
v___x_3277_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3277_, 0, v_snd_3275_);
lean_ctor_set(v___x_3277_, 1, v_fst_3274_);
lean_ctor_set(v___x_3277_, 2, v_levelNames_3248_);
lean_ctor_set(v___x_3277_, 3, v_docString_x3f_3276_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 0, v___x_3277_);
v___x_3279_ = v___x_3272_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3277_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
else
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_dec(v_levelNames_3248_);
v_a_3282_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3269_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3269_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
v___jp_3290_:
{
if (lean_obj_tag(v___y_3291_) == 0)
{
lean_object* v_a_3292_; 
v_a_3292_ = lean_ctor_get(v___y_3291_, 0);
lean_inc(v_a_3292_);
lean_dec_ref_known(v___y_3291_, 1);
v_levelNames_3248_ = v_a_3292_;
v___y_3249_ = v_a_3234_;
v___y_3250_ = v_a_3235_;
v___y_3251_ = v_a_3236_;
v___y_3252_ = v_a_3237_;
v___y_3253_ = v_a_3238_;
v___y_3254_ = v_a_3239_;
goto v___jp_3247_;
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
lean_dec(v_fst_3242_);
lean_dec(v_currNamespace_3230_);
v_a_3293_ = lean_ctor_get(v___y_3291_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___y_3291_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___y_3291_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___y_3291_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
v___jp_3301_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v___x_3303_ = lean_unsigned_to_nat(0u);
v___x_3304_ = lean_array_get_size(v___y_3302_);
v___x_3305_ = lean_nat_dec_lt(v___x_3303_, v___x_3304_);
if (v___x_3305_ == 0)
{
lean_dec_ref(v___y_3302_);
v_levelNames_3248_ = v_currLevelNames_3231_;
v___y_3249_ = v_a_3234_;
v___y_3250_ = v_a_3235_;
v___y_3251_ = v_a_3236_;
v___y_3252_ = v_a_3237_;
v___y_3253_ = v_a_3238_;
v___y_3254_ = v_a_3239_;
goto v___jp_3247_;
}
else
{
uint8_t v___x_3306_; 
v___x_3306_ = lean_nat_dec_le(v___x_3304_, v___x_3304_);
if (v___x_3306_ == 0)
{
if (v___x_3305_ == 0)
{
lean_dec_ref(v___y_3302_);
v_levelNames_3248_ = v_currLevelNames_3231_;
v___y_3249_ = v_a_3234_;
v___y_3250_ = v_a_3235_;
v___y_3251_ = v_a_3236_;
v___y_3252_ = v_a_3237_;
v___y_3253_ = v_a_3238_;
v___y_3254_ = v_a_3239_;
goto v___jp_3247_;
}
else
{
size_t v___x_3307_; size_t v___x_3308_; lean_object* v___x_3309_; 
v___x_3307_ = ((size_t)0ULL);
v___x_3308_ = lean_usize_of_nat(v___x_3304_);
v___x_3309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3302_, v___x_3307_, v___x_3308_, v_currLevelNames_3231_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
lean_dec_ref(v___y_3302_);
v___y_3291_ = v___x_3309_;
goto v___jp_3290_;
}
}
else
{
size_t v___x_3310_; size_t v___x_3311_; lean_object* v___x_3312_; 
v___x_3310_ = ((size_t)0ULL);
v___x_3311_ = lean_usize_of_nat(v___x_3304_);
v___x_3312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3302_, v___x_3310_, v___x_3311_, v_currLevelNames_3231_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
lean_dec_ref(v___y_3302_);
v___y_3291_ = v___x_3312_;
goto v___jp_3290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___boxed(lean_object* v_currNamespace_3330_, lean_object* v_currLevelNames_3331_, lean_object* v_declId_3332_, lean_object* v_modifiers_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Lean_Elab_expandDeclId(v_currNamespace_3330_, v_currLevelNames_3331_, v_declId_3332_, v_modifiers_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
lean_dec(v_a_3339_);
lean_dec_ref(v_a_3338_);
lean_dec(v_a_3337_);
lean_dec_ref(v_a_3336_);
lean_dec(v_a_3335_);
lean_dec_ref(v_a_3334_);
lean_dec_ref(v_modifiers_3333_);
lean_dec(v_declId_3332_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(lean_object* v_00_u03b1_3342_, lean_object* v_u_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v___x_3351_; 
v___x_3351_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___boxed(lean_object* v_00_u03b1_3352_, lean_object* v_u_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(v_00_u03b1_3352_, v_u_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(lean_object* v_00_u03b1_3362_, lean_object* v_msg_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3372_, lean_object* v_msg_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(v_00_u03b1_3372_, v_msg_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(lean_object* v_msgData_3382_, lean_object* v_macroStack_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_3382_, v_macroStack_3383_, v___y_3388_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_3392_, lean_object* v_macroStack_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(v_msgData_3392_, v_macroStack_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(lean_object* v_t_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_3402_, v___y_3408_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___boxed(lean_object* v_t_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(v_t_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(lean_object* v_env_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_3420_, v___y_3424_, v___y_3426_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___boxed(lean_object* v_env_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(v_env_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(lean_object* v_00_u03b1_3438_, lean_object* v_env_3439_, lean_object* v_x_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_3439_, v_x_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3449_, lean_object* v_env_3450_, lean_object* v_x_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(v_00_u03b1_3449_, v_env_3450_, v_x_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(lean_object* v_00_u03b1_3460_, lean_object* v_constName_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v___x_3469_; 
v___x_3469_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___boxed(lean_object* v_00_u03b1_3470_, lean_object* v_constName_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(v_00_u03b1_3470_, v_constName_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(lean_object* v_00_u03b1_3480_, lean_object* v_ref_3481_, lean_object* v_constName_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v___x_3490_; 
v___x_3490_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_3481_, v_constName_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___boxed(lean_object* v_00_u03b1_3491_, lean_object* v_ref_3492_, lean_object* v_constName_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(v_00_u03b1_3491_, v_ref_3492_, v_constName_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v_ref_3492_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(lean_object* v_00_u03b1_3502_, lean_object* v_ref_3503_, lean_object* v_msg_3504_, lean_object* v_declHint_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_3503_, v_msg_3504_, v_declHint_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___boxed(lean_object* v_00_u03b1_3514_, lean_object* v_ref_3515_, lean_object* v_msg_3516_, lean_object* v_declHint_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(v_00_u03b1_3514_, v_ref_3515_, v_msg_3516_, v_declHint_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v_ref_3515_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(lean_object* v_msg_3526_, lean_object* v_declHint_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_3526_, v_declHint_3527_, v___y_3533_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___boxed(lean_object* v_msg_3536_, lean_object* v_declHint_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(v_msg_3536_, v_declHint_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(lean_object* v_00_u03b1_3546_, lean_object* v_ref_3547_, lean_object* v_msg_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_3547_, v_msg_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___boxed(lean_object* v_00_u03b1_3557_, lean_object* v_ref_3558_, lean_object* v_msg_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(v_00_u03b1_3557_, v_ref_3558_, v_msg_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v_ref_3558_);
return v_res_3567_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(lean_object* v_x_3571_){
_start:
{
lean_object* v_name_3572_; lean_object* v___x_3573_; uint8_t v___x_3574_; 
v_name_3572_ = lean_ctor_get(v_x_3571_, 0);
v___x_3573_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__1));
v___x_3574_ = lean_name_eq(v_name_3572_, v___x_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___boxed(lean_object* v_x_3575_){
_start:
{
uint8_t v_res_3576_; lean_object* v_r_3577_; 
v_res_3576_ = l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(v_x_3575_);
lean_dec_ref(v_x_3575_);
v_r_3577_ = lean_box(v_res_3576_);
return v_r_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__1(lean_object* v_ctx_3578_){
_start:
{
lean_object* v_declName_x3f_3579_; lean_object* v_macroStack_3580_; uint8_t v_mayPostpone_3581_; uint8_t v_errToSorry_3582_; lean_object* v_autoBoundImplicitContext_3583_; lean_object* v_autoBoundImplicitForbidden_3584_; lean_object* v_sectionVars_3585_; lean_object* v_sectionFVars_3586_; uint8_t v_implicitLambda_3587_; uint8_t v_heedElabAsElim_3588_; uint8_t v_isNoncomputableSection_3589_; uint8_t v_isMetaSection_3590_; uint8_t v_ignoreTCFailures_3591_; uint8_t v_inPattern_3592_; lean_object* v_tacSnap_x3f_3593_; uint8_t v_saveRecAppSyntax_3594_; uint8_t v_holesAsSyntheticOpaque_3595_; lean_object* v_fixedTermElabs_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3604_; 
v_declName_x3f_3579_ = lean_ctor_get(v_ctx_3578_, 0);
v_macroStack_3580_ = lean_ctor_get(v_ctx_3578_, 1);
v_mayPostpone_3581_ = lean_ctor_get_uint8(v_ctx_3578_, sizeof(void*)*8);
v_errToSorry_3582_ = lean_ctor_get_uint8(v_ctx_3578_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_3583_ = lean_ctor_get(v_ctx_3578_, 2);
v_autoBoundImplicitForbidden_3584_ = lean_ctor_get(v_ctx_3578_, 3);
v_sectionVars_3585_ = lean_ctor_get(v_ctx_3578_, 4);
v_sectionFVars_3586_ = lean_ctor_get(v_ctx_3578_, 5);
v_implicitLambda_3587_ = lean_ctor_get_uint8(v_ctx_3578_, sizeof(void*)*8 + 2);
v_heedElabAsElim_3588_ = lean_ctor_get_uint8(v_ctx_3578_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_3589_ = lean_ctor_get_uint8(v_ctx_3578_, sizeof(void*)*8 + 4);
v_isMetaSection_3590_ = lean_ctor_get_uint8(v_ctx_3578_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_3591_ = lean_ctor_get_uint8(v_ctx_3578_, sizeof(void*)*8 + 6);
v_inPattern_3592_ = lean_ctor_get_uint8(v_ctx_3578_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_3593_ = lean_ctor_get(v_ctx_3578_, 6);
v_saveRecAppSyntax_3594_ = lean_ctor_get_uint8(v_ctx_3578_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_3595_ = lean_ctor_get_uint8(v_ctx_3578_, sizeof(void*)*8 + 9);
v_fixedTermElabs_3596_ = lean_ctor_get(v_ctx_3578_, 7);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_ctx_3578_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3598_ = v_ctx_3578_;
v_isShared_3599_ = v_isSharedCheck_3604_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_fixedTermElabs_3596_);
lean_inc(v_tacSnap_x3f_3593_);
lean_inc(v_sectionFVars_3586_);
lean_inc(v_sectionVars_3585_);
lean_inc(v_autoBoundImplicitForbidden_3584_);
lean_inc(v_autoBoundImplicitContext_3583_);
lean_inc(v_macroStack_3580_);
lean_inc(v_declName_x3f_3579_);
lean_dec(v_ctx_3578_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3604_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
uint8_t v___x_3600_; lean_object* v___x_3602_; 
v___x_3600_ = 0;
if (v_isShared_3599_ == 0)
{
v___x_3602_ = v___x_3598_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_declName_x3f_3579_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_macroStack_3580_);
lean_ctor_set(v_reuseFailAlloc_3603_, 2, v_autoBoundImplicitContext_3583_);
lean_ctor_set(v_reuseFailAlloc_3603_, 3, v_autoBoundImplicitForbidden_3584_);
lean_ctor_set(v_reuseFailAlloc_3603_, 4, v_sectionVars_3585_);
lean_ctor_set(v_reuseFailAlloc_3603_, 5, v_sectionFVars_3586_);
lean_ctor_set(v_reuseFailAlloc_3603_, 6, v_tacSnap_x3f_3593_);
lean_ctor_set(v_reuseFailAlloc_3603_, 7, v_fixedTermElabs_3596_);
lean_ctor_set_uint8(v_reuseFailAlloc_3603_, sizeof(void*)*8, v_mayPostpone_3581_);
lean_ctor_set_uint8(v_reuseFailAlloc_3603_, sizeof(void*)*8 + 1, v_errToSorry_3582_);
lean_ctor_set_uint8(v_reuseFailAlloc_3603_, sizeof(void*)*8 + 2, v_implicitLambda_3587_);
lean_ctor_set_uint8(v_reuseFailAlloc_3603_, sizeof(void*)*8 + 3, v_heedElabAsElim_3588_);
lean_ctor_set_uint8(v_reuseFailAlloc_3603_, sizeof(void*)*8 + 4, v_isNoncomputableSection_3589_);
lean_ctor_set_uint8(v_reuseFailAlloc_3603_, sizeof(void*)*8 + 5, v_isMetaSection_3590_);
lean_ctor_set_uint8(v_reuseFailAlloc_3603_, sizeof(void*)*8 + 6, v_ignoreTCFailures_3591_);
lean_ctor_set_uint8(v_reuseFailAlloc_3603_, sizeof(void*)*8 + 7, v_inPattern_3592_);
lean_ctor_set_uint8(v_reuseFailAlloc_3603_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_3594_);
lean_ctor_set_uint8(v_reuseFailAlloc_3603_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_3595_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
lean_ctor_set_uint8(v___x_3602_, sizeof(void*)*8 + 10, v___x_3600_);
return v___x_3602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg(lean_object* v_inst_3626_, lean_object* v_attrs_3627_, lean_object* v_a_3628_){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; uint8_t v___x_3632_; 
v___x_3629_ = lean_unsigned_to_nat(0u);
v___x_3630_ = lean_array_get_size(v_attrs_3627_);
v___x_3631_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9));
v___x_3632_ = lean_nat_dec_lt(v___x_3629_, v___x_3630_);
if (v___x_3632_ == 0)
{
lean_dec_ref(v_attrs_3627_);
lean_dec(v_inst_3626_);
return v_a_3628_;
}
else
{
if (v___x_3632_ == 0)
{
lean_dec_ref(v_attrs_3627_);
lean_dec(v_inst_3626_);
return v_a_3628_;
}
else
{
lean_object* v___f_3633_; size_t v___x_3634_; size_t v___x_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v___f_3633_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10));
v___x_3634_ = ((size_t)0ULL);
v___x_3635_ = lean_usize_of_nat(v___x_3630_);
v___x_3636_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_3631_, v___f_3633_, v_attrs_3627_, v___x_3634_, v___x_3635_);
v___x_3637_ = lean_unbox(v___x_3636_);
lean_dec(v___x_3636_);
if (v___x_3637_ == 0)
{
lean_dec(v_inst_3626_);
return v_a_3628_;
}
else
{
lean_object* v___f_3638_; lean_object* v___x_3639_; 
v___f_3638_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11));
v___x_3639_ = lean_apply_3(v_inst_3626_, lean_box(0), v___f_3638_, v_a_3628_);
return v___x_3639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs(lean_object* v_m_3640_, lean_object* v_00_u03b1_3641_, lean_object* v_inst_3642_, lean_object* v_attrs_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3645_ = lean_unsigned_to_nat(0u);
v___x_3646_ = lean_array_get_size(v_attrs_3643_);
v___x_3647_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9));
v___x_3648_ = lean_nat_dec_lt(v___x_3645_, v___x_3646_);
if (v___x_3648_ == 0)
{
lean_dec_ref(v_attrs_3643_);
lean_dec(v_inst_3642_);
return v_a_3644_;
}
else
{
if (v___x_3648_ == 0)
{
lean_dec_ref(v_attrs_3643_);
lean_dec(v_inst_3642_);
return v_a_3644_;
}
else
{
lean_object* v___f_3649_; size_t v___x_3650_; size_t v___x_3651_; lean_object* v___x_3652_; uint8_t v___x_3653_; 
v___f_3649_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10));
v___x_3650_ = ((size_t)0ULL);
v___x_3651_ = lean_usize_of_nat(v___x_3646_);
v___x_3652_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_3647_, v___f_3649_, v_attrs_3643_, v___x_3650_, v___x_3651_);
v___x_3653_ = lean_unbox(v___x_3652_);
lean_dec(v___x_3652_);
if (v___x_3653_ == 0)
{
lean_dec(v_inst_3642_);
return v_a_3644_;
}
else
{
lean_object* v___f_3654_; lean_object* v___x_3655_; 
v___f_3654_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11));
v___x_3655_ = lean_apply_3(v_inst_3642_, lean_box(0), v___f_3654_, v_a_3644_);
return v___x_3655_;
}
}
}
}
}
lean_object* runtime_initialize_Lean_DocString_Add(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeclModifiers(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_DocString_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_linter_redundantVisibility = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_linter_redundantVisibility);
lean_dec_ref(res);
l_Lean_Elab_instInhabitedVisibility_default = _init_l_Lean_Elab_instInhabitedVisibility_default();
l_Lean_Elab_instInhabitedVisibility = _init_l_Lean_Elab_instInhabitedVisibility();
l_Lean_Elab_instInhabitedRecKind_default = _init_l_Lean_Elab_instInhabitedRecKind_default();
l_Lean_Elab_instInhabitedRecKind = _init_l_Lean_Elab_instInhabitedRecKind();
l_Lean_Elab_instInhabitedComputeKind_default = _init_l_Lean_Elab_instInhabitedComputeKind_default();
l_Lean_Elab_instInhabitedComputeKind = _init_l_Lean_Elab_instInhabitedComputeKind();
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DeclModifiers(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString_Add(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeclModifiers(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeclModifiers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DeclModifiers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DeclModifiers(builtin);
}
#ifdef __cplusplus
}
#endif
