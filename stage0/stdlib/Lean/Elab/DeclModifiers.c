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
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
uint8_t v___x_880__boxed_90_; lean_object* v_res_91_; 
v___x_880__boxed_90_ = lean_unbox(v___x_86_);
v_res_91_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(v_____do__lift_85_, v___x_880__boxed_90_, v_inst_87_, v_inst_88_, v_____do__lift_89_);
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
uint8_t v___x_924__boxed_112_; lean_object* v_res_113_; 
v___x_924__boxed_112_ = lean_unbox(v___x_104_);
v_res_113_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(v___x_924__boxed_112_, v_inst_105_, v_inst_106_, v_inst_107_, v_inst_108_, v_declName_109_, v_toBind_110_, v_____do__lift_111_);
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
uint8_t v___x_950__boxed_134_; lean_object* v_res_135_; 
v___x_950__boxed_134_ = lean_unbox(v___x_127_);
v_res_135_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(v_toMonadRef_126_, v___x_950__boxed_134_, v_inst_128_, v_inst_129_, v_inst_130_, v_inst_131_, v_toBind_132_, v_declName_133_);
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
uint8_t v___x_984__boxed_158_; lean_object* v_res_159_; 
v___x_984__boxed_158_ = lean_unbox(v___x_154_);
v_res_159_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(v_val_153_, v___x_984__boxed_158_, v_inst_155_, v_inst_156_, v_____r_157_);
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
uint8_t v___x_1061__boxed_207_; lean_object* v_res_208_; 
v___x_1061__boxed_207_ = lean_unbox(v___x_201_);
v_res_208_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(v_declName_200_, v___x_1061__boxed_207_, v_inst_202_, v_inst_203_, v_toBind_204_, v___f_205_, v_____r_206_);
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
uint8_t v___x_1134__boxed_266_; lean_object* v_res_267_; 
v___x_1134__boxed_266_ = lean_unbox(v___x_259_);
v_res_267_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(v___f_257_, v_declName_258_, v___x_1134__boxed_266_, v_inst_260_, v_inst_261_, v_toBind_262_, v___f_263_, v_env_264_, v_____do__lift_265_);
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
uint8_t v___x_1208__boxed_308_; lean_object* v_res_309_; 
v___x_1208__boxed_308_ = lean_unbox(v___x_301_);
v_res_309_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(v_declName_300_, v___x_1208__boxed_308_, v_inst_302_, v_inst_303_, v_toBind_304_, v___f_305_, v___f_306_, v_____r_307_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_toCtorIdx(uint8_t v_x_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Elab_Visibility_ctorIdx(v_x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_toCtorIdx___boxed(lean_object* v_x_371_){
_start:
{
uint8_t v_x_4__boxed_372_; lean_object* v_res_373_; 
v_x_4__boxed_372_ = lean_unbox(v_x_371_);
v_res_373_ = l_Lean_Elab_Visibility_toCtorIdx(v_x_4__boxed_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___redArg(lean_object* v_k_374_){
_start:
{
lean_inc(v_k_374_);
return v_k_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___redArg___boxed(lean_object* v_k_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Elab_Visibility_ctorElim___redArg(v_k_375_);
lean_dec(v_k_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim(lean_object* v_motive_377_, lean_object* v_ctorIdx_378_, uint8_t v_t_379_, lean_object* v_h_380_, lean_object* v_k_381_){
_start:
{
lean_inc(v_k_381_);
return v_k_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___boxed(lean_object* v_motive_382_, lean_object* v_ctorIdx_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_k_386_){
_start:
{
uint8_t v_t_boxed_387_; lean_object* v_res_388_; 
v_t_boxed_387_ = lean_unbox(v_t_384_);
v_res_388_ = l_Lean_Elab_Visibility_ctorElim(v_motive_382_, v_ctorIdx_383_, v_t_boxed_387_, v_h_385_, v_k_386_);
lean_dec(v_k_386_);
lean_dec(v_ctorIdx_383_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___redArg(lean_object* v_regular_389_){
_start:
{
lean_inc(v_regular_389_);
return v_regular_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___redArg___boxed(lean_object* v_regular_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Elab_Visibility_regular_elim___redArg(v_regular_390_);
lean_dec(v_regular_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim(lean_object* v_motive_392_, uint8_t v_t_393_, lean_object* v_h_394_, lean_object* v_regular_395_){
_start:
{
lean_inc(v_regular_395_);
return v_regular_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___boxed(lean_object* v_motive_396_, lean_object* v_t_397_, lean_object* v_h_398_, lean_object* v_regular_399_){
_start:
{
uint8_t v_t_boxed_400_; lean_object* v_res_401_; 
v_t_boxed_400_ = lean_unbox(v_t_397_);
v_res_401_ = l_Lean_Elab_Visibility_regular_elim(v_motive_396_, v_t_boxed_400_, v_h_398_, v_regular_399_);
lean_dec(v_regular_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___redArg(lean_object* v_private_402_){
_start:
{
lean_inc(v_private_402_);
return v_private_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___redArg___boxed(lean_object* v_private_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Elab_Visibility_private_elim___redArg(v_private_403_);
lean_dec(v_private_403_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim(lean_object* v_motive_405_, uint8_t v_t_406_, lean_object* v_h_407_, lean_object* v_private_408_){
_start:
{
lean_inc(v_private_408_);
return v_private_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___boxed(lean_object* v_motive_409_, lean_object* v_t_410_, lean_object* v_h_411_, lean_object* v_private_412_){
_start:
{
uint8_t v_t_boxed_413_; lean_object* v_res_414_; 
v_t_boxed_413_ = lean_unbox(v_t_410_);
v_res_414_ = l_Lean_Elab_Visibility_private_elim(v_motive_409_, v_t_boxed_413_, v_h_411_, v_private_412_);
lean_dec(v_private_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___redArg(lean_object* v_public_415_){
_start:
{
lean_inc(v_public_415_);
return v_public_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___redArg___boxed(lean_object* v_public_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Elab_Visibility_public_elim___redArg(v_public_416_);
lean_dec(v_public_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim(lean_object* v_motive_418_, uint8_t v_t_419_, lean_object* v_h_420_, lean_object* v_public_421_){
_start:
{
lean_inc(v_public_421_);
return v_public_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___boxed(lean_object* v_motive_422_, lean_object* v_t_423_, lean_object* v_h_424_, lean_object* v_public_425_){
_start:
{
uint8_t v_t_boxed_426_; lean_object* v_res_427_; 
v_t_boxed_426_ = lean_unbox(v_t_423_);
v_res_427_ = l_Lean_Elab_Visibility_public_elim(v_motive_422_, v_t_boxed_426_, v_h_424_, v_public_425_);
lean_dec(v_public_425_);
return v_res_427_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedVisibility_default(void){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = 0;
return v___x_428_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedVisibility(void){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = 0;
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0(uint8_t v_x_433_){
_start:
{
switch(v_x_433_)
{
case 0:
{
lean_object* v___x_434_; 
v___x_434_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__0));
return v___x_434_;
}
case 1:
{
lean_object* v___x_435_; 
v___x_435_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__1));
return v___x_435_;
}
default: 
{
lean_object* v___x_436_; 
v___x_436_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__2));
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0___boxed(lean_object* v_x_437_){
_start:
{
uint8_t v_x_36__boxed_438_; lean_object* v_res_439_; 
v_x_36__boxed_438_ = lean_unbox(v_x_437_);
v_res_439_ = l_Lean_Elab_instToStringVisibility___lam__0(v_x_36__boxed_438_);
return v_res_439_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPrivate(uint8_t v_x_442_){
_start:
{
if (v_x_442_ == 1)
{
uint8_t v___x_443_; 
v___x_443_ = 1;
return v___x_443_;
}
else
{
uint8_t v___x_444_; 
v___x_444_ = 0;
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPrivate___boxed(lean_object* v_x_445_){
_start:
{
uint8_t v_x_21__boxed_446_; uint8_t v_res_447_; lean_object* v_r_448_; 
v_x_21__boxed_446_ = lean_unbox(v_x_445_);
v_res_447_ = l_Lean_Elab_Visibility_isPrivate(v_x_21__boxed_446_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPublic(uint8_t v_x_449_){
_start:
{
if (v_x_449_ == 2)
{
uint8_t v___x_450_; 
v___x_450_ = 1;
return v___x_450_;
}
else
{
uint8_t v___x_451_; 
v___x_451_ = 0;
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPublic___boxed(lean_object* v_x_452_){
_start:
{
uint8_t v_x_21__boxed_453_; uint8_t v_res_454_; lean_object* v_r_455_; 
v_x_21__boxed_453_ = lean_unbox(v_x_452_);
v_res_454_ = l_Lean_Elab_Visibility_isPublic(v_x_21__boxed_453_);
v_r_455_ = lean_box(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isInferredPublic(lean_object* v_env_456_, uint8_t v_v_457_){
_start:
{
uint8_t v_isExporting_461_; 
v_isExporting_461_ = lean_ctor_get_uint8(v_env_456_, sizeof(void*)*8);
if (v_isExporting_461_ == 0)
{
lean_object* v___x_462_; uint8_t v_isModule_463_; uint8_t v___x_464_; 
v___x_462_ = l_Lean_Environment_header(v_env_456_);
v_isModule_463_ = lean_ctor_get_uint8(v___x_462_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_462_);
v___x_464_ = lean_bool_not(v_isModule_463_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; 
v___x_465_ = l_Lean_Elab_Visibility_isPublic(v_v_457_);
return v___x_465_;
}
else
{
goto v___jp_458_;
}
}
else
{
goto v___jp_458_;
}
v___jp_458_:
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = l_Lean_Elab_Visibility_isPrivate(v_v_457_);
v___x_460_ = lean_bool_not(v___x_459_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isInferredPublic___boxed(lean_object* v_env_466_, lean_object* v_v_467_){
_start:
{
uint8_t v_v_boxed_468_; uint8_t v_res_469_; lean_object* v_r_470_; 
v_v_boxed_468_ = lean_unbox(v_v_467_);
v_res_469_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_466_, v_v_boxed_468_);
lean_dec_ref(v_env_466_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__0(lean_object* v_toPure_471_, lean_object* v_____r_472_){
_start:
{
uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = 2;
v___x_474_ = lean_box(v___x_473_);
v___x_475_ = lean_apply_2(v_toPure_471_, lean_box(0), v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__2(lean_object* v_toPure_476_, lean_object* v_____r_477_){
_start:
{
uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = 1;
v___x_479_ = lean_box(v___x_478_);
v___x_480_ = lean_apply_2(v_toPure_476_, lean_box(0), v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__0));
v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__2));
v___x_486_ = l_Lean_stringToMessageData(v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__10));
v___x_503_ = l_Lean_stringToMessageData(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__12));
v___x_506_ = l_Lean_stringToMessageData(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3(lean_object* v_vis_x3f_507_, lean_object* v_toPure_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_toBind_515_, lean_object* v___f_516_, lean_object* v___f_517_, lean_object* v___f_518_, lean_object* v___f_519_, lean_object* v_env_520_){
_start:
{
if (lean_obj_tag(v_vis_x3f_507_) == 0)
{
uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
lean_dec(v___f_519_);
lean_dec(v___f_518_);
lean_dec(v___f_517_);
lean_dec(v___f_516_);
lean_dec(v_toBind_515_);
lean_dec_ref(v_inst_514_);
lean_dec(v_inst_513_);
lean_dec(v_inst_512_);
lean_dec_ref(v_inst_511_);
lean_dec_ref(v_inst_510_);
lean_dec_ref(v_inst_509_);
v___x_524_ = 0;
v___x_525_ = lean_box(v___x_524_);
v___x_526_ = lean_apply_2(v_toPure_508_, lean_box(0), v___x_525_);
return v___x_526_;
}
else
{
lean_object* v_val_527_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___x_552_; uint8_t v___x_553_; 
lean_dec(v_toPure_508_);
v_val_527_ = lean_ctor_get(v_vis_x3f_507_, 0);
lean_inc_n(v_val_527_, 2);
lean_dec_ref_known(v_vis_x3f_507_, 1);
v___x_552_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8));
v___x_553_ = l_Lean_Syntax_isOfKind(v_val_527_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; uint8_t v___x_555_; 
lean_dec(v___f_519_);
lean_dec(v___f_518_);
v___x_554_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9));
lean_inc(v_val_527_);
v___x_555_ = l_Lean_Syntax_isOfKind(v_val_527_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec(v___f_517_);
lean_dec(v___f_516_);
lean_dec(v_toBind_515_);
lean_dec_ref(v_inst_514_);
lean_dec(v_inst_513_);
lean_dec(v_inst_512_);
lean_dec_ref(v_inst_511_);
v___x_556_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11);
v___x_557_ = l_Lean_throwErrorAt___redArg(v_inst_509_, v_inst_510_, v_val_527_, v___x_556_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; 
lean_dec_ref(v_inst_510_);
v___x_558_ = l_Lean_Syntax_getHeadInfo(v_val_527_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_dec_ref_known(v___x_558_, 4);
goto v___jp_545_;
}
else
{
lean_dec(v___x_558_);
if (v___x_553_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v_val_527_);
lean_dec(v___f_516_);
lean_dec(v_toBind_515_);
lean_dec_ref(v_inst_514_);
lean_dec(v_inst_513_);
lean_dec(v_inst_512_);
lean_dec_ref(v_inst_511_);
lean_dec_ref(v_inst_509_);
v___x_559_ = lean_box(0);
v___x_560_ = lean_apply_1(v___f_517_, v___x_559_);
return v___x_560_;
}
else
{
goto v___jp_545_;
}
}
}
}
else
{
lean_object* v___x_561_; 
lean_dec(v___f_517_);
lean_dec(v___f_516_);
lean_dec_ref(v_inst_510_);
v___x_561_ = l_Lean_Syntax_getHeadInfo(v_val_527_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_562_; uint8_t v_isModule_563_; 
lean_dec_ref_known(v___x_561_, 4);
v___x_562_ = l_Lean_Environment_header(v_env_520_);
v_isModule_563_ = lean_ctor_get_uint8(v___x_562_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_562_);
if (v_isModule_563_ == 0)
{
lean_dec(v_val_527_);
lean_dec(v___f_519_);
lean_dec(v_toBind_515_);
lean_dec_ref(v_inst_514_);
lean_dec(v_inst_513_);
lean_dec(v_inst_512_);
lean_dec_ref(v_inst_511_);
lean_dec_ref(v_inst_509_);
goto v___jp_521_;
}
else
{
uint8_t v_isExporting_564_; uint8_t v___x_565_; 
v_isExporting_564_ = lean_ctor_get_uint8(v_env_520_, sizeof(void*)*8);
v___x_565_ = lean_bool_not(v_isExporting_564_);
if (v___x_565_ == 0)
{
lean_dec(v_val_527_);
lean_dec(v___f_519_);
lean_dec(v_toBind_515_);
lean_dec_ref(v_inst_514_);
lean_dec(v_inst_513_);
lean_dec(v_inst_512_);
lean_dec_ref(v_inst_511_);
lean_dec_ref(v_inst_509_);
goto v___jp_521_;
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec(v___f_518_);
v___x_566_ = l_Lean_linter_redundantVisibility;
v___x_567_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13);
v___x_568_ = l_Lean_Linter_logLintIf___redArg(v_inst_509_, v_inst_511_, v_inst_512_, v_inst_513_, v_inst_514_, v___x_566_, v_val_527_, v___x_567_);
v___x_569_ = lean_apply_4(v_toBind_515_, lean_box(0), lean_box(0), v___x_568_, v___f_519_);
return v___x_569_;
}
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v___x_561_);
lean_dec(v_val_527_);
lean_dec(v___f_519_);
lean_dec(v_toBind_515_);
lean_dec_ref(v_inst_514_);
lean_dec(v_inst_513_);
lean_dec(v_inst_512_);
lean_dec_ref(v_inst_511_);
lean_dec_ref(v_inst_509_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_apply_1(v___f_518_, v___x_570_);
return v___x_571_;
}
}
v___jp_528_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
lean_inc_ref(v___y_531_);
v___x_532_ = l_Lean_stringToMessageData(v___y_531_);
lean_inc_ref(v___y_529_);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___y_529_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
lean_inc_ref(v___y_530_);
v___x_536_ = l_Lean_Linter_logLintIf___redArg(v_inst_509_, v_inst_511_, v_inst_512_, v_inst_513_, v_inst_514_, v___y_530_, v_val_527_, v___x_535_);
v___x_537_ = lean_apply_4(v_toBind_515_, lean_box(0), lean_box(0), v___x_536_, v___f_516_);
return v___x_537_;
}
v___jp_538_:
{
lean_object* v___x_539_; uint8_t v_isModule_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_539_ = l_Lean_Environment_header(v_env_520_);
v_isModule_540_ = lean_ctor_get_uint8(v___x_539_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_539_);
v___x_541_ = l_Lean_linter_redundantVisibility;
v___x_542_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3);
if (v_isModule_540_ == 0)
{
lean_object* v___x_543_; 
v___x_543_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4));
v___y_529_ = v___x_542_;
v___y_530_ = v___x_541_;
v___y_531_ = v___x_543_;
goto v___jp_528_;
}
else
{
lean_object* v___x_544_; 
v___x_544_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__5));
v___y_529_ = v___x_542_;
v___y_530_ = v___x_541_;
v___y_531_ = v___x_544_;
goto v___jp_528_;
}
}
v___jp_545_:
{
uint8_t v_isExporting_546_; 
v_isExporting_546_ = lean_ctor_get_uint8(v_env_520_, sizeof(void*)*8);
if (v_isExporting_546_ == 0)
{
lean_object* v___x_547_; uint8_t v_isModule_548_; uint8_t v___x_549_; 
v___x_547_ = l_Lean_Environment_header(v_env_520_);
v_isModule_548_ = lean_ctor_get_uint8(v___x_547_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_547_);
v___x_549_ = lean_bool_not(v_isModule_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v_val_527_);
lean_dec(v___f_516_);
lean_dec(v_toBind_515_);
lean_dec_ref(v_inst_514_);
lean_dec(v_inst_513_);
lean_dec(v_inst_512_);
lean_dec_ref(v_inst_511_);
lean_dec_ref(v_inst_509_);
v___x_550_ = lean_box(0);
v___x_551_ = lean_apply_1(v___f_517_, v___x_550_);
return v___x_551_;
}
else
{
lean_dec(v___f_517_);
goto v___jp_538_;
}
}
else
{
lean_dec(v___f_517_);
goto v___jp_538_;
}
}
}
v___jp_521_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_box(0);
v___x_523_ = lean_apply_1(v___f_518_, v___x_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___boxed(lean_object* v_vis_x3f_572_, lean_object* v_toPure_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_toBind_580_, lean_object* v___f_581_, lean_object* v___f_582_, lean_object* v___f_583_, lean_object* v___f_584_, lean_object* v_env_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Elab_elabVisibility___redArg___lam__3(v_vis_x3f_572_, v_toPure_573_, v_inst_574_, v_inst_575_, v_inst_576_, v_inst_577_, v_inst_578_, v_inst_579_, v_toBind_580_, v___f_581_, v___f_582_, v___f_583_, v___f_584_, v_env_585_);
lean_dec_ref(v_env_585_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg(lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_vis_x3f_593_){
_start:
{
lean_object* v_toApplicative_594_; lean_object* v_toBind_595_; lean_object* v_getEnv_596_; lean_object* v_toPure_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___x_603_; 
v_toApplicative_594_ = lean_ctor_get(v_inst_587_, 0);
v_toBind_595_ = lean_ctor_get(v_inst_587_, 1);
lean_inc_n(v_toBind_595_, 2);
v_getEnv_596_ = lean_ctor_get(v_inst_589_, 0);
lean_inc(v_getEnv_596_);
v_toPure_597_ = lean_ctor_get(v_toApplicative_594_, 1);
lean_inc_n(v_toPure_597_, 3);
v___f_598_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__0), 2, 1);
lean_closure_set(v___f_598_, 0, v_toPure_597_);
lean_inc_ref(v___f_598_);
v___f_599_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_599_, 0, v___f_598_);
v___f_600_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__2), 2, 1);
lean_closure_set(v___f_600_, 0, v_toPure_597_);
lean_inc_ref(v___f_600_);
v___f_601_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_601_, 0, v___f_600_);
v___f_602_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__3___boxed), 14, 13);
lean_closure_set(v___f_602_, 0, v_vis_x3f_593_);
lean_closure_set(v___f_602_, 1, v_toPure_597_);
lean_closure_set(v___f_602_, 2, v_inst_587_);
lean_closure_set(v___f_602_, 3, v_inst_588_);
lean_closure_set(v___f_602_, 4, v_inst_591_);
lean_closure_set(v___f_602_, 5, v_inst_592_);
lean_closure_set(v___f_602_, 6, v_inst_590_);
lean_closure_set(v___f_602_, 7, v_inst_589_);
lean_closure_set(v___f_602_, 8, v_toBind_595_);
lean_closure_set(v___f_602_, 9, v___f_599_);
lean_closure_set(v___f_602_, 10, v___f_598_);
lean_closure_set(v___f_602_, 11, v___f_600_);
lean_closure_set(v___f_602_, 12, v___f_601_);
v___x_603_ = lean_apply_4(v_toBind_595_, lean_box(0), lean_box(0), v_getEnv_596_, v___f_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility(lean_object* v_m_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_vis_x3f_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_Elab_elabVisibility___redArg(v_inst_605_, v_inst_606_, v_inst_607_, v_inst_608_, v_inst_609_, v_inst_610_, v_vis_x3f_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx(uint8_t v_x_613_){
_start:
{
switch(v_x_613_)
{
case 0:
{
lean_object* v___x_614_; 
v___x_614_ = lean_unsigned_to_nat(0u);
return v___x_614_;
}
case 1:
{
lean_object* v___x_615_; 
v___x_615_ = lean_unsigned_to_nat(1u);
return v___x_615_;
}
default: 
{
lean_object* v___x_616_; 
v___x_616_ = lean_unsigned_to_nat(2u);
return v___x_616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___boxed(lean_object* v_x_617_){
_start:
{
uint8_t v_x_boxed_618_; lean_object* v_res_619_; 
v_x_boxed_618_ = lean_unbox(v_x_617_);
v_res_619_ = l_Lean_Elab_RecKind_ctorIdx(v_x_boxed_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx(uint8_t v_x_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_Elab_RecKind_ctorIdx(v_x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx___boxed(lean_object* v_x_622_){
_start:
{
uint8_t v_x_4__boxed_623_; lean_object* v_res_624_; 
v_x_4__boxed_623_ = lean_unbox(v_x_622_);
v_res_624_ = l_Lean_Elab_RecKind_toCtorIdx(v_x_4__boxed_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg(lean_object* v_k_625_){
_start:
{
lean_inc(v_k_625_);
return v_k_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg___boxed(lean_object* v_k_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Elab_RecKind_ctorElim___redArg(v_k_626_);
lean_dec(v_k_626_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim(lean_object* v_motive_628_, lean_object* v_ctorIdx_629_, uint8_t v_t_630_, lean_object* v_h_631_, lean_object* v_k_632_){
_start:
{
lean_inc(v_k_632_);
return v_k_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___boxed(lean_object* v_motive_633_, lean_object* v_ctorIdx_634_, lean_object* v_t_635_, lean_object* v_h_636_, lean_object* v_k_637_){
_start:
{
uint8_t v_t_boxed_638_; lean_object* v_res_639_; 
v_t_boxed_638_ = lean_unbox(v_t_635_);
v_res_639_ = l_Lean_Elab_RecKind_ctorElim(v_motive_633_, v_ctorIdx_634_, v_t_boxed_638_, v_h_636_, v_k_637_);
lean_dec(v_k_637_);
lean_dec(v_ctorIdx_634_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg(lean_object* v_partial_640_){
_start:
{
lean_inc(v_partial_640_);
return v_partial_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg___boxed(lean_object* v_partial_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_Elab_RecKind_partial_elim___redArg(v_partial_641_);
lean_dec(v_partial_641_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim(lean_object* v_motive_643_, uint8_t v_t_644_, lean_object* v_h_645_, lean_object* v_partial_646_){
_start:
{
lean_inc(v_partial_646_);
return v_partial_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___boxed(lean_object* v_motive_647_, lean_object* v_t_648_, lean_object* v_h_649_, lean_object* v_partial_650_){
_start:
{
uint8_t v_t_boxed_651_; lean_object* v_res_652_; 
v_t_boxed_651_ = lean_unbox(v_t_648_);
v_res_652_ = l_Lean_Elab_RecKind_partial_elim(v_motive_647_, v_t_boxed_651_, v_h_649_, v_partial_650_);
lean_dec(v_partial_650_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg(lean_object* v_nonrec_653_){
_start:
{
lean_inc(v_nonrec_653_);
return v_nonrec_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg___boxed(lean_object* v_nonrec_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_Elab_RecKind_nonrec_elim___redArg(v_nonrec_654_);
lean_dec(v_nonrec_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim(lean_object* v_motive_656_, uint8_t v_t_657_, lean_object* v_h_658_, lean_object* v_nonrec_659_){
_start:
{
lean_inc(v_nonrec_659_);
return v_nonrec_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___boxed(lean_object* v_motive_660_, lean_object* v_t_661_, lean_object* v_h_662_, lean_object* v_nonrec_663_){
_start:
{
uint8_t v_t_boxed_664_; lean_object* v_res_665_; 
v_t_boxed_664_ = lean_unbox(v_t_661_);
v_res_665_ = l_Lean_Elab_RecKind_nonrec_elim(v_motive_660_, v_t_boxed_664_, v_h_662_, v_nonrec_663_);
lean_dec(v_nonrec_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg(lean_object* v_default_666_){
_start:
{
lean_inc(v_default_666_);
return v_default_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg___boxed(lean_object* v_default_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Elab_RecKind_default_elim___redArg(v_default_667_);
lean_dec(v_default_667_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim(lean_object* v_motive_669_, uint8_t v_t_670_, lean_object* v_h_671_, lean_object* v_default_672_){
_start:
{
lean_inc(v_default_672_);
return v_default_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___boxed(lean_object* v_motive_673_, lean_object* v_t_674_, lean_object* v_h_675_, lean_object* v_default_676_){
_start:
{
uint8_t v_t_boxed_677_; lean_object* v_res_678_; 
v_t_boxed_677_ = lean_unbox(v_t_674_);
v_res_678_ = l_Lean_Elab_RecKind_default_elim(v_motive_673_, v_t_boxed_677_, v_h_675_, v_default_676_);
lean_dec(v_default_676_);
return v_res_678_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind_default(void){
_start:
{
uint8_t v___x_679_; 
v___x_679_ = 0;
return v___x_679_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind(void){
_start:
{
uint8_t v___x_680_; 
v___x_680_ = 0;
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx(uint8_t v_x_681_){
_start:
{
switch(v_x_681_)
{
case 0:
{
lean_object* v___x_682_; 
v___x_682_ = lean_unsigned_to_nat(0u);
return v___x_682_;
}
case 1:
{
lean_object* v___x_683_; 
v___x_683_ = lean_unsigned_to_nat(1u);
return v___x_683_;
}
default: 
{
lean_object* v___x_684_; 
v___x_684_ = lean_unsigned_to_nat(2u);
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___boxed(lean_object* v_x_685_){
_start:
{
uint8_t v_x_boxed_686_; lean_object* v_res_687_; 
v_x_boxed_686_ = lean_unbox(v_x_685_);
v_res_687_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_boxed_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_toCtorIdx(uint8_t v_x_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_toCtorIdx___boxed(lean_object* v_x_690_){
_start:
{
uint8_t v_x_4__boxed_691_; lean_object* v_res_692_; 
v_x_4__boxed_691_ = lean_unbox(v_x_690_);
v_res_692_ = l_Lean_Elab_ComputeKind_toCtorIdx(v_x_4__boxed_691_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg(lean_object* v_k_693_){
_start:
{
lean_inc(v_k_693_);
return v_k_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg___boxed(lean_object* v_k_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Elab_ComputeKind_ctorElim___redArg(v_k_694_);
lean_dec(v_k_694_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim(lean_object* v_motive_696_, lean_object* v_ctorIdx_697_, uint8_t v_t_698_, lean_object* v_h_699_, lean_object* v_k_700_){
_start:
{
lean_inc(v_k_700_);
return v_k_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___boxed(lean_object* v_motive_701_, lean_object* v_ctorIdx_702_, lean_object* v_t_703_, lean_object* v_h_704_, lean_object* v_k_705_){
_start:
{
uint8_t v_t_boxed_706_; lean_object* v_res_707_; 
v_t_boxed_706_ = lean_unbox(v_t_703_);
v_res_707_ = l_Lean_Elab_ComputeKind_ctorElim(v_motive_701_, v_ctorIdx_702_, v_t_boxed_706_, v_h_704_, v_k_705_);
lean_dec(v_k_705_);
lean_dec(v_ctorIdx_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg(lean_object* v_regular_708_){
_start:
{
lean_inc(v_regular_708_);
return v_regular_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg___boxed(lean_object* v_regular_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Elab_ComputeKind_regular_elim___redArg(v_regular_709_);
lean_dec(v_regular_709_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim(lean_object* v_motive_711_, uint8_t v_t_712_, lean_object* v_h_713_, lean_object* v_regular_714_){
_start:
{
lean_inc(v_regular_714_);
return v_regular_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___boxed(lean_object* v_motive_715_, lean_object* v_t_716_, lean_object* v_h_717_, lean_object* v_regular_718_){
_start:
{
uint8_t v_t_boxed_719_; lean_object* v_res_720_; 
v_t_boxed_719_ = lean_unbox(v_t_716_);
v_res_720_ = l_Lean_Elab_ComputeKind_regular_elim(v_motive_715_, v_t_boxed_719_, v_h_717_, v_regular_718_);
lean_dec(v_regular_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg(lean_object* v_meta_721_){
_start:
{
lean_inc(v_meta_721_);
return v_meta_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg___boxed(lean_object* v_meta_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Elab_ComputeKind_meta_elim___redArg(v_meta_722_);
lean_dec(v_meta_722_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim(lean_object* v_motive_724_, uint8_t v_t_725_, lean_object* v_h_726_, lean_object* v_meta_727_){
_start:
{
lean_inc(v_meta_727_);
return v_meta_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___boxed(lean_object* v_motive_728_, lean_object* v_t_729_, lean_object* v_h_730_, lean_object* v_meta_731_){
_start:
{
uint8_t v_t_boxed_732_; lean_object* v_res_733_; 
v_t_boxed_732_ = lean_unbox(v_t_729_);
v_res_733_ = l_Lean_Elab_ComputeKind_meta_elim(v_motive_728_, v_t_boxed_732_, v_h_730_, v_meta_731_);
lean_dec(v_meta_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(lean_object* v_noncomputable_734_){
_start:
{
lean_inc(v_noncomputable_734_);
return v_noncomputable_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg___boxed(lean_object* v_noncomputable_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(v_noncomputable_735_);
lean_dec(v_noncomputable_735_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim(lean_object* v_motive_737_, uint8_t v_t_738_, lean_object* v_h_739_, lean_object* v_noncomputable_740_){
_start:
{
lean_inc(v_noncomputable_740_);
return v_noncomputable_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___boxed(lean_object* v_motive_741_, lean_object* v_t_742_, lean_object* v_h_743_, lean_object* v_noncomputable_744_){
_start:
{
uint8_t v_t_boxed_745_; lean_object* v_res_746_; 
v_t_boxed_745_ = lean_unbox(v_t_742_);
v_res_746_ = l_Lean_Elab_ComputeKind_noncomputable_elim(v_motive_741_, v_t_boxed_745_, v_h_743_, v_noncomputable_744_);
lean_dec(v_noncomputable_744_);
return v_res_746_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind_default(void){
_start:
{
uint8_t v___x_747_; 
v___x_747_ = 0;
return v___x_747_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind(void){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = 0;
return v___x_748_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqComputeKind_beq(uint8_t v_x_749_, uint8_t v_y_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_751_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_749_);
v___x_752_ = l_Lean_Elab_ComputeKind_ctorIdx(v_y_750_);
v___x_753_ = lean_nat_dec_eq(v___x_751_, v___x_752_);
lean_dec(v___x_752_);
lean_dec(v___x_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqComputeKind_beq___boxed(lean_object* v_x_754_, lean_object* v_y_755_){
_start:
{
uint8_t v_x_17__boxed_756_; uint8_t v_y_18__boxed_757_; uint8_t v_res_758_; lean_object* v_r_759_; 
v_x_17__boxed_756_ = lean_unbox(v_x_754_);
v_y_18__boxed_757_ = lean_unbox(v_y_755_);
v_res_758_ = l_Lean_Elab_instBEqComputeKind_beq(v_x_17__boxed_756_, v_y_18__boxed_757_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
static lean_object* _init_l_Lean_Elab_instReprComputeKind_repr___closed__6(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_unsigned_to_nat(2u);
v___x_772_ = lean_nat_to_int(v___x_771_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_Elab_instReprComputeKind_repr___closed__7(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_to_int(v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprComputeKind_repr(uint8_t v_x_775_, lean_object* v_prec_776_){
_start:
{
lean_object* v___y_778_; lean_object* v___y_785_; lean_object* v___y_792_; 
switch(v_x_775_)
{
case 0:
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = lean_unsigned_to_nat(1024u);
v___x_799_ = lean_nat_dec_le(v___x_798_, v_prec_776_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; 
v___x_800_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_778_ = v___x_800_;
goto v___jp_777_;
}
else
{
lean_object* v___x_801_; 
v___x_801_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_778_ = v___x_801_;
goto v___jp_777_;
}
}
case 1:
{
lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_802_ = lean_unsigned_to_nat(1024u);
v___x_803_ = lean_nat_dec_le(v___x_802_, v_prec_776_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
v___x_804_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_785_ = v___x_804_;
goto v___jp_784_;
}
else
{
lean_object* v___x_805_; 
v___x_805_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_785_ = v___x_805_;
goto v___jp_784_;
}
}
default: 
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = lean_unsigned_to_nat(1024u);
v___x_807_ = lean_nat_dec_le(v___x_806_, v_prec_776_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; 
v___x_808_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_792_ = v___x_808_;
goto v___jp_791_;
}
else
{
lean_object* v___x_809_; 
v___x_809_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_792_ = v___x_809_;
goto v___jp_791_;
}
}
}
v___jp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_779_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__1));
lean_inc(v___y_778_);
v___x_780_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_780_, 0, v___y_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = 0;
v___x_782_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*1, v___x_781_);
v___x_783_ = l_Repr_addAppParen(v___x_782_, v_prec_776_);
return v___x_783_;
}
v___jp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_786_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__3));
lean_inc(v___y_785_);
v___x_787_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_787_, 0, v___y_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = 0;
v___x_789_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*1, v___x_788_);
v___x_790_ = l_Repr_addAppParen(v___x_789_, v_prec_776_);
return v___x_790_;
}
v___jp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_793_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__5));
lean_inc(v___y_792_);
v___x_794_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_794_, 0, v___y_792_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = 0;
v___x_796_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set_uint8(v___x_796_, sizeof(void*)*1, v___x_795_);
v___x_797_ = l_Repr_addAppParen(v___x_796_, v_prec_776_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprComputeKind_repr___boxed(lean_object* v_x_810_, lean_object* v_prec_811_){
_start:
{
uint8_t v_x_177__boxed_812_; lean_object* v_res_813_; 
v_x_177__boxed_812_ = lean_unbox(v_x_810_);
v_res_813_ = l_Lean_Elab_instReprComputeKind_repr(v_x_177__boxed_812_, v_prec_811_);
lean_dec(v_prec_811_);
return v_res_813_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object* v_m_828_){
_start:
{
uint8_t v_visibility_829_; uint8_t v___x_830_; 
v_visibility_829_ = lean_ctor_get_uint8(v_m_828_, sizeof(void*)*3);
v___x_830_ = l_Lean_Elab_Visibility_isPrivate(v_visibility_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPrivate___boxed(lean_object* v_m_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Lean_Elab_Modifiers_isPrivate(v_m_831_);
lean_dec_ref(v_m_831_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPublic(lean_object* v_m_834_){
_start:
{
uint8_t v_visibility_835_; uint8_t v___x_836_; 
v_visibility_835_ = lean_ctor_get_uint8(v_m_834_, sizeof(void*)*3);
v___x_836_ = l_Lean_Elab_Visibility_isPublic(v_visibility_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPublic___boxed(lean_object* v_m_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l_Lean_Elab_Modifiers_isPublic(v_m_837_);
lean_dec_ref(v_m_837_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isInferredPublic(lean_object* v_env_840_, lean_object* v_m_841_){
_start:
{
uint8_t v_visibility_842_; uint8_t v___x_843_; 
v_visibility_842_ = lean_ctor_get_uint8(v_m_841_, sizeof(void*)*3);
v___x_843_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_840_, v_visibility_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isInferredPublic___boxed(lean_object* v_env_844_, lean_object* v_m_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l_Lean_Elab_Modifiers_isInferredPublic(v_env_844_, v_m_845_);
lean_dec_ref(v_m_845_);
lean_dec_ref(v_env_844_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object* v_x_848_){
_start:
{
uint8_t v_recKind_849_; 
v_recKind_849_ = lean_ctor_get_uint8(v_x_848_, sizeof(void*)*3 + 3);
if (v_recKind_849_ == 0)
{
uint8_t v___x_850_; 
v___x_850_ = 1;
return v___x_850_;
}
else
{
uint8_t v___x_851_; 
v___x_851_ = 0;
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPartial___boxed(lean_object* v_x_852_){
_start:
{
uint8_t v_res_853_; lean_object* v_r_854_; 
v_res_853_ = l_Lean_Elab_Modifiers_isPartial(v_x_852_);
lean_dec_ref(v_x_852_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNonrec(lean_object* v_x_855_){
_start:
{
uint8_t v_recKind_856_; 
v_recKind_856_ = lean_ctor_get_uint8(v_x_855_, sizeof(void*)*3 + 3);
if (v_recKind_856_ == 1)
{
uint8_t v___x_857_; 
v___x_857_ = 1;
return v___x_857_;
}
else
{
uint8_t v___x_858_; 
v___x_858_ = 0;
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNonrec___boxed(lean_object* v_x_859_){
_start:
{
uint8_t v_res_860_; lean_object* v_r_861_; 
v_res_860_ = l_Lean_Elab_Modifiers_isNonrec(v_x_859_);
lean_dec_ref(v_x_859_);
v_r_861_ = lean_box(v_res_860_);
return v_r_861_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isMeta(lean_object* v_m_862_){
_start:
{
uint8_t v_computeKind_863_; 
v_computeKind_863_ = lean_ctor_get_uint8(v_m_862_, sizeof(void*)*3 + 2);
if (v_computeKind_863_ == 1)
{
uint8_t v___x_864_; 
v___x_864_ = 1;
return v___x_864_;
}
else
{
uint8_t v___x_865_; 
v___x_865_ = 0;
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isMeta___boxed(lean_object* v_m_866_){
_start:
{
uint8_t v_res_867_; lean_object* v_r_868_; 
v_res_867_ = l_Lean_Elab_Modifiers_isMeta(v_m_866_);
lean_dec_ref(v_m_866_);
v_r_868_ = lean_box(v_res_867_);
return v_r_868_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNoncomputable(lean_object* v_m_869_){
_start:
{
uint8_t v_computeKind_870_; 
v_computeKind_870_ = lean_ctor_get_uint8(v_m_869_, sizeof(void*)*3 + 2);
if (v_computeKind_870_ == 2)
{
uint8_t v___x_871_; 
v___x_871_ = 1;
return v___x_871_;
}
else
{
uint8_t v___x_872_; 
v___x_872_ = 0;
return v___x_872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNoncomputable___boxed(lean_object* v_m_873_){
_start:
{
uint8_t v_res_874_; lean_object* v_r_875_; 
v_res_874_ = l_Lean_Elab_Modifiers_isNoncomputable(v_m_873_);
lean_dec_ref(v_m_873_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addAttr(lean_object* v_modifiers_876_, lean_object* v_attr_877_){
_start:
{
lean_object* v_stx_878_; lean_object* v_docString_x3f_879_; uint8_t v_visibility_880_; uint8_t v_isProtected_881_; uint8_t v_computeKind_882_; uint8_t v_recKind_883_; uint8_t v_isUnsafe_884_; lean_object* v_attrs_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_893_; 
v_stx_878_ = lean_ctor_get(v_modifiers_876_, 0);
v_docString_x3f_879_ = lean_ctor_get(v_modifiers_876_, 1);
v_visibility_880_ = lean_ctor_get_uint8(v_modifiers_876_, sizeof(void*)*3);
v_isProtected_881_ = lean_ctor_get_uint8(v_modifiers_876_, sizeof(void*)*3 + 1);
v_computeKind_882_ = lean_ctor_get_uint8(v_modifiers_876_, sizeof(void*)*3 + 2);
v_recKind_883_ = lean_ctor_get_uint8(v_modifiers_876_, sizeof(void*)*3 + 3);
v_isUnsafe_884_ = lean_ctor_get_uint8(v_modifiers_876_, sizeof(void*)*3 + 4);
v_attrs_885_ = lean_ctor_get(v_modifiers_876_, 2);
v_isSharedCheck_893_ = !lean_is_exclusive(v_modifiers_876_);
if (v_isSharedCheck_893_ == 0)
{
v___x_887_ = v_modifiers_876_;
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_attrs_885_);
lean_inc(v_docString_x3f_879_);
lean_inc(v_stx_878_);
lean_dec(v_modifiers_876_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_889_ = lean_array_push(v_attrs_885_, v_attr_877_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 2, v___x_889_);
v___x_891_ = v___x_887_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_stx_878_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_docString_x3f_879_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v___x_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_892_, sizeof(void*)*3, v_visibility_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_892_, sizeof(void*)*3 + 1, v_isProtected_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_892_, sizeof(void*)*3 + 2, v_computeKind_882_);
lean_ctor_set_uint8(v_reuseFailAlloc_892_, sizeof(void*)*3 + 3, v_recKind_883_);
lean_ctor_set_uint8(v_reuseFailAlloc_892_, sizeof(void*)*3 + 4, v_isUnsafe_884_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addFirstAttr(lean_object* v_modifiers_894_, lean_object* v_attr_895_){
_start:
{
lean_object* v_stx_896_; lean_object* v_docString_x3f_897_; uint8_t v_visibility_898_; uint8_t v_isProtected_899_; uint8_t v_computeKind_900_; uint8_t v_recKind_901_; uint8_t v_isUnsafe_902_; lean_object* v_attrs_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_914_; 
v_stx_896_ = lean_ctor_get(v_modifiers_894_, 0);
v_docString_x3f_897_ = lean_ctor_get(v_modifiers_894_, 1);
v_visibility_898_ = lean_ctor_get_uint8(v_modifiers_894_, sizeof(void*)*3);
v_isProtected_899_ = lean_ctor_get_uint8(v_modifiers_894_, sizeof(void*)*3 + 1);
v_computeKind_900_ = lean_ctor_get_uint8(v_modifiers_894_, sizeof(void*)*3 + 2);
v_recKind_901_ = lean_ctor_get_uint8(v_modifiers_894_, sizeof(void*)*3 + 3);
v_isUnsafe_902_ = lean_ctor_get_uint8(v_modifiers_894_, sizeof(void*)*3 + 4);
v_attrs_903_ = lean_ctor_get(v_modifiers_894_, 2);
v_isSharedCheck_914_ = !lean_is_exclusive(v_modifiers_894_);
if (v_isSharedCheck_914_ == 0)
{
v___x_905_ = v_modifiers_894_;
v_isShared_906_ = v_isSharedCheck_914_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_attrs_903_);
lean_inc(v_docString_x3f_897_);
lean_inc(v_stx_896_);
lean_dec(v_modifiers_894_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_914_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_mk_empty_array_with_capacity(v___x_907_);
v___x_909_ = lean_array_push(v___x_908_, v_attr_895_);
v___x_910_ = l_Array_append___redArg(v___x_909_, v_attrs_903_);
lean_dec_ref(v_attrs_903_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 2, v___x_910_);
v___x_912_ = v___x_905_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_stx_896_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_docString_x3f_897_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v___x_910_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*3, v_visibility_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*3 + 1, v_isProtected_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*3 + 2, v_computeKind_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*3 + 3, v_recKind_901_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*3 + 4, v_isUnsafe_902_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(lean_object* v_p_915_, lean_object* v_as_916_, size_t v_i_917_, size_t v_stop_918_, lean_object* v_b_919_){
_start:
{
lean_object* v___y_921_; uint8_t v___x_925_; 
v___x_925_ = lean_usize_dec_eq(v_i_917_, v_stop_918_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_926_ = lean_array_uget_borrowed(v_as_916_, v_i_917_);
lean_inc_ref(v_p_915_);
lean_inc(v___x_926_);
v___x_927_ = lean_apply_1(v_p_915_, v___x_926_);
v___x_928_ = lean_unbox(v___x_927_);
if (v___x_928_ == 0)
{
v___y_921_ = v_b_919_;
goto v___jp_920_;
}
else
{
lean_object* v___x_929_; 
lean_inc(v___x_926_);
v___x_929_ = lean_array_push(v_b_919_, v___x_926_);
v___y_921_ = v___x_929_;
goto v___jp_920_;
}
}
else
{
lean_dec_ref(v_p_915_);
return v_b_919_;
}
v___jp_920_:
{
size_t v___x_922_; size_t v___x_923_; 
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_add(v_i_917_, v___x_922_);
v_i_917_ = v___x_923_;
v_b_919_ = v___y_921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0___boxed(lean_object* v_p_930_, lean_object* v_as_931_, lean_object* v_i_932_, lean_object* v_stop_933_, lean_object* v_b_934_){
_start:
{
size_t v_i_boxed_935_; size_t v_stop_boxed_936_; lean_object* v_res_937_; 
v_i_boxed_935_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_stop_boxed_936_ = lean_unbox_usize(v_stop_933_);
lean_dec(v_stop_933_);
v_res_937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_930_, v_as_931_, v_i_boxed_935_, v_stop_boxed_936_, v_b_934_);
lean_dec_ref(v_as_931_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object* v_modifiers_938_, lean_object* v_p_939_){
_start:
{
lean_object* v_stx_940_; lean_object* v_docString_x3f_941_; uint8_t v_visibility_942_; uint8_t v_isProtected_943_; uint8_t v_computeKind_944_; uint8_t v_recKind_945_; uint8_t v_isUnsafe_946_; lean_object* v_attrs_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_974_; 
v_stx_940_ = lean_ctor_get(v_modifiers_938_, 0);
v_docString_x3f_941_ = lean_ctor_get(v_modifiers_938_, 1);
v_visibility_942_ = lean_ctor_get_uint8(v_modifiers_938_, sizeof(void*)*3);
v_isProtected_943_ = lean_ctor_get_uint8(v_modifiers_938_, sizeof(void*)*3 + 1);
v_computeKind_944_ = lean_ctor_get_uint8(v_modifiers_938_, sizeof(void*)*3 + 2);
v_recKind_945_ = lean_ctor_get_uint8(v_modifiers_938_, sizeof(void*)*3 + 3);
v_isUnsafe_946_ = lean_ctor_get_uint8(v_modifiers_938_, sizeof(void*)*3 + 4);
v_attrs_947_ = lean_ctor_get(v_modifiers_938_, 2);
v_isSharedCheck_974_ = !lean_is_exclusive(v_modifiers_938_);
if (v_isSharedCheck_974_ == 0)
{
v___x_949_ = v_modifiers_938_;
v_isShared_950_ = v_isSharedCheck_974_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_attrs_947_);
lean_inc(v_docString_x3f_941_);
lean_inc(v_stx_940_);
lean_dec(v_modifiers_938_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_974_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_951_ = lean_unsigned_to_nat(0u);
v___x_952_ = lean_array_get_size(v_attrs_947_);
v___x_953_ = ((lean_object*)(l_Lean_Elab_instInhabitedModifiers_default___closed__0));
v___x_954_ = lean_nat_dec_lt(v___x_951_, v___x_952_);
if (v___x_954_ == 0)
{
lean_object* v___x_956_; 
lean_dec_ref(v_attrs_947_);
lean_dec_ref(v_p_939_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 2, v___x_953_);
v___x_956_ = v___x_949_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_stx_940_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_docString_x3f_941_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v___x_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_957_, sizeof(void*)*3, v_visibility_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_957_, sizeof(void*)*3 + 1, v_isProtected_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_957_, sizeof(void*)*3 + 2, v_computeKind_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_957_, sizeof(void*)*3 + 3, v_recKind_945_);
lean_ctor_set_uint8(v_reuseFailAlloc_957_, sizeof(void*)*3 + 4, v_isUnsafe_946_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
else
{
uint8_t v___x_958_; 
v___x_958_ = lean_nat_dec_le(v___x_952_, v___x_952_);
if (v___x_958_ == 0)
{
if (v___x_954_ == 0)
{
lean_object* v___x_960_; 
lean_dec_ref(v_attrs_947_);
lean_dec_ref(v_p_939_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 2, v___x_953_);
v___x_960_ = v___x_949_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_stx_940_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_docString_x3f_941_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v___x_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, sizeof(void*)*3, v_visibility_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, sizeof(void*)*3 + 1, v_isProtected_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, sizeof(void*)*3 + 2, v_computeKind_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, sizeof(void*)*3 + 3, v_recKind_945_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, sizeof(void*)*3 + 4, v_isUnsafe_946_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
else
{
size_t v___x_962_; size_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_962_ = ((size_t)0ULL);
v___x_963_ = lean_usize_of_nat(v___x_952_);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_939_, v_attrs_947_, v___x_962_, v___x_963_, v___x_953_);
lean_dec_ref(v_attrs_947_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 2, v___x_964_);
v___x_966_ = v___x_949_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_stx_940_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_docString_x3f_941_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v___x_964_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*3, v_visibility_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*3 + 1, v_isProtected_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*3 + 2, v_computeKind_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*3 + 3, v_recKind_945_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*3 + 4, v_isUnsafe_946_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
else
{
size_t v___x_968_; size_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_968_ = ((size_t)0ULL);
v___x_969_ = lean_usize_of_nat(v___x_952_);
v___x_970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_939_, v_attrs_947_, v___x_968_, v___x_969_, v___x_953_);
lean_dec_ref(v_attrs_947_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 2, v___x_970_);
v___x_972_ = v___x_949_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_stx_940_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_docString_x3f_941_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v___x_970_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3, v_visibility_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3 + 1, v_isProtected_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3 + 2, v_computeKind_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3 + 3, v_recKind_945_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3 + 4, v_isUnsafe_946_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(lean_object* v_p_975_, lean_object* v_as_976_, size_t v_i_977_, size_t v_stop_978_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = lean_usize_dec_eq(v_i_977_, v_stop_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_980_ = lean_array_uget_borrowed(v_as_976_, v_i_977_);
lean_inc_ref(v_p_975_);
lean_inc(v___x_980_);
v___x_981_ = lean_apply_1(v_p_975_, v___x_980_);
v___x_982_ = lean_unbox(v___x_981_);
if (v___x_982_ == 0)
{
size_t v___x_983_; size_t v___x_984_; 
v___x_983_ = ((size_t)1ULL);
v___x_984_ = lean_usize_add(v_i_977_, v___x_983_);
v_i_977_ = v___x_984_;
goto _start;
}
else
{
uint8_t v___x_986_; 
lean_dec_ref(v_p_975_);
v___x_986_ = lean_unbox(v___x_981_);
return v___x_986_;
}
}
else
{
uint8_t v___x_987_; 
lean_dec_ref(v_p_975_);
v___x_987_ = 0;
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0___boxed(lean_object* v_p_988_, lean_object* v_as_989_, lean_object* v_i_990_, lean_object* v_stop_991_){
_start:
{
size_t v_i_boxed_992_; size_t v_stop_boxed_993_; uint8_t v_res_994_; lean_object* v_r_995_; 
v_i_boxed_992_ = lean_unbox_usize(v_i_990_);
lean_dec(v_i_990_);
v_stop_boxed_993_ = lean_unbox_usize(v_stop_991_);
lean_dec(v_stop_991_);
v_res_994_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_988_, v_as_989_, v_i_boxed_992_, v_stop_boxed_993_);
lean_dec_ref(v_as_989_);
v_r_995_ = lean_box(v_res_994_);
return v_r_995_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_anyAttr(lean_object* v_modifiers_996_, lean_object* v_p_997_){
_start:
{
lean_object* v_attrs_998_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v_attrs_998_ = lean_ctor_get(v_modifiers_996_, 2);
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = lean_array_get_size(v_attrs_998_);
v___x_1001_ = lean_nat_dec_lt(v___x_999_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_dec_ref(v_p_997_);
return v___x_1001_;
}
else
{
if (v___x_1001_ == 0)
{
lean_dec_ref(v_p_997_);
return v___x_1001_;
}
else
{
size_t v___x_1002_; size_t v___x_1003_; uint8_t v___x_1004_; 
v___x_1002_ = ((size_t)0ULL);
v___x_1003_ = lean_usize_of_nat(v___x_1000_);
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_997_, v_attrs_998_, v___x_1002_, v___x_1003_);
return v___x_1004_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_anyAttr___boxed(lean_object* v_modifiers_1005_, lean_object* v_p_1006_){
_start:
{
uint8_t v_res_1007_; lean_object* v_r_1008_; 
v_res_1007_ = l_Lean_Elab_Modifiers_anyAttr(v_modifiers_1005_, v_p_1006_);
lean_dec_ref(v_modifiers_1005_);
v_r_1008_ = lean_box(v_res_1007_);
return v_r_1008_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__0));
v___x_1012_ = lean_string_length(v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__2, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__2_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2);
v___x_1014_ = lean_nat_to_int(v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__0(lean_object* v_attr_1021_){
_start:
{
uint8_t v_kind_1022_; lean_object* v_name_1023_; lean_object* v_stx_1024_; lean_object* v___y_1026_; 
v_kind_1022_ = lean_ctor_get_uint8(v_attr_1021_, sizeof(void*)*2);
v_name_1023_ = lean_ctor_get(v_attr_1021_, 0);
lean_inc(v_name_1023_);
v_stx_1024_ = lean_ctor_get(v_attr_1021_, 1);
lean_inc(v_stx_1024_);
lean_dec_ref(v_attr_1021_);
switch(v_kind_1022_)
{
case 0:
{
lean_object* v___x_1048_; 
v___x_1048_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4));
v___y_1026_ = v___x_1048_;
goto v___jp_1025_;
}
case 1:
{
lean_object* v___x_1049_; 
v___x_1049_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__6));
v___y_1026_ = v___x_1049_;
goto v___jp_1025_;
}
default: 
{
lean_object* v___x_1050_; 
v___x_1050_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__7));
v___y_1026_ = v___x_1050_;
goto v___jp_1025_;
}
}
v___jp_1025_:
{
lean_object* v___x_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; 
lean_inc_ref(v___y_1026_);
v___x_1027_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___y_1026_);
v___x_1028_ = 1;
v___x_1029_ = l_Lean_Name_toString(v_name_1023_, v___x_1028_);
v___x_1030_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1027_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_box(0);
v___x_1033_ = 0;
v___x_1034_ = l_Lean_Syntax_formatStx(v_stx_1024_, v___x_1032_, v___x_1033_);
v___x_1035_ = l_Std_Format_defWidth;
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = l_Std_Format_pretty(v___x_1034_, v___x_1035_, v___x_1036_, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1031_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__3, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__3_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3);
v___x_1041_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__4));
v___x_1042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___x_1039_);
v___x_1043_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__5));
v___x_1044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1040_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = 0;
v___x_1047_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*1, v___x_1046_);
return v___x_1047_;
}
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__0));
v___x_1060_ = lean_string_length(v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__5, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__5_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5);
v___x_1062_ = lean_nat_to_int(v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__1(lean_object* v___f_1119_, lean_object* v___f_1120_, lean_object* v_m_1121_){
_start:
{
lean_object* v_docString_x3f_1122_; uint8_t v_visibility_1123_; uint8_t v_isProtected_1124_; uint8_t v_computeKind_1125_; uint8_t v_recKind_1126_; uint8_t v_isUnsafe_1127_; lean_object* v_attrs_1128_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1174_; 
v_docString_x3f_1122_ = lean_ctor_get(v_m_1121_, 1);
lean_inc(v_docString_x3f_1122_);
v_visibility_1123_ = lean_ctor_get_uint8(v_m_1121_, sizeof(void*)*3);
v_isProtected_1124_ = lean_ctor_get_uint8(v_m_1121_, sizeof(void*)*3 + 1);
v_computeKind_1125_ = lean_ctor_get_uint8(v_m_1121_, sizeof(void*)*3 + 2);
v_recKind_1126_ = lean_ctor_get_uint8(v_m_1121_, sizeof(void*)*3 + 3);
v_isUnsafe_1127_ = lean_ctor_get_uint8(v_m_1121_, sizeof(void*)*3 + 4);
v_attrs_1128_ = lean_ctor_get(v_m_1121_, 2);
lean_inc_ref(v_attrs_1128_);
lean_dec_ref(v_m_1121_);
if (lean_obj_tag(v_docString_x3f_1122_) == 0)
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_box(0);
v___y_1174_ = v___x_1178_;
goto v___jp_1173_;
}
else
{
lean_object* v_val_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_val_1179_ = lean_ctor_get(v_docString_x3f_1122_, 0);
lean_inc(v_val_1179_);
lean_dec_ref_known(v_docString_x3f_1122_, 1);
v___x_1180_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__32));
v___x_1181_ = lean_box(0);
v___x_1182_ = 0;
v___x_1183_ = l_Lean_Syntax_formatStx(v_val_1179_, v___x_1181_, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1180_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__34));
v___x_1186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___y_1174_ = v___x_1188_;
goto v___jp_1173_;
}
v___jp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v_components_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; lean_object* v___x_1146_; 
lean_inc(v___y_1131_);
v___x_1132_ = l_List_appendTR___redArg(v___y_1130_, v___y_1131_);
v___x_1133_ = lean_array_to_list(v_attrs_1128_);
v___x_1134_ = lean_box(0);
v___x_1135_ = l_List_mapTR_loop___redArg(v___f_1119_, v___x_1133_, v___x_1134_);
v_components_1136_ = l_List_appendTR___redArg(v___x_1132_, v___x_1135_);
v___x_1137_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__3));
v___x_1138_ = l_Std_Format_joinSep___redArg(v___f_1120_, v_components_1136_, v___x_1137_);
v___x_1139_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__6, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__6_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6);
v___x_1140_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__7));
v___x_1141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v___x_1138_);
v___x_1142_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__8));
v___x_1143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1139_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = 0;
v___x_1146_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set_uint8(v___x_1146_, sizeof(void*)*1, v___x_1145_);
return v___x_1146_;
}
v___jp_1147_:
{
lean_object* v___x_1150_; 
lean_inc(v___y_1149_);
v___x_1150_ = l_List_appendTR___redArg(v___y_1148_, v___y_1149_);
if (v_isUnsafe_1127_ == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_box(0);
v___y_1130_ = v___x_1150_;
v___y_1131_ = v___x_1151_;
goto v___jp_1129_;
}
else
{
lean_object* v___x_1152_; 
v___x_1152_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__11));
v___y_1130_ = v___x_1150_;
v___y_1131_ = v___x_1152_;
goto v___jp_1129_;
}
}
v___jp_1153_:
{
lean_object* v___x_1156_; 
lean_inc(v___y_1155_);
v___x_1156_ = l_List_appendTR___redArg(v___y_1154_, v___y_1155_);
switch(v_recKind_1126_)
{
case 0:
{
lean_object* v___x_1157_; 
v___x_1157_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__14));
v___y_1148_ = v___x_1156_;
v___y_1149_ = v___x_1157_;
goto v___jp_1147_;
}
case 1:
{
lean_object* v___x_1158_; 
v___x_1158_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__17));
v___y_1148_ = v___x_1156_;
v___y_1149_ = v___x_1158_;
goto v___jp_1147_;
}
default: 
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_box(0);
v___y_1148_ = v___x_1156_;
v___y_1149_ = v___x_1159_;
goto v___jp_1147_;
}
}
}
v___jp_1160_:
{
lean_object* v___x_1163_; 
lean_inc(v___y_1162_);
v___x_1163_ = l_List_appendTR___redArg(v___y_1161_, v___y_1162_);
switch(v_computeKind_1125_)
{
case 0:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_box(0);
v___y_1154_ = v___x_1163_;
v___y_1155_ = v___x_1164_;
goto v___jp_1153_;
}
case 1:
{
lean_object* v___x_1165_; 
v___x_1165_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__20));
v___y_1154_ = v___x_1163_;
v___y_1155_ = v___x_1165_;
goto v___jp_1153_;
}
default: 
{
lean_object* v___x_1166_; 
v___x_1166_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__23));
v___y_1154_ = v___x_1163_;
v___y_1155_ = v___x_1166_;
goto v___jp_1153_;
}
}
}
v___jp_1167_:
{
lean_object* v___x_1170_; 
lean_inc(v___y_1169_);
v___x_1170_ = l_List_appendTR___redArg(v___y_1168_, v___y_1169_);
if (v_isProtected_1124_ == 0)
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_box(0);
v___y_1161_ = v___x_1170_;
v___y_1162_ = v___x_1171_;
goto v___jp_1160_;
}
else
{
lean_object* v___x_1172_; 
v___x_1172_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__26));
v___y_1161_ = v___x_1170_;
v___y_1162_ = v___x_1172_;
goto v___jp_1160_;
}
}
v___jp_1173_:
{
switch(v_visibility_1123_)
{
case 0:
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_box(0);
v___y_1168_ = v___y_1174_;
v___y_1169_ = v___x_1175_;
goto v___jp_1167_;
}
case 1:
{
lean_object* v___x_1176_; 
v___x_1176_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__28));
v___y_1168_ = v___y_1174_;
v___y_1169_ = v___x_1176_;
goto v___jp_1167_;
}
default: 
{
lean_object* v___x_1177_; 
v___x_1177_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__30));
v___y_1168_ = v___y_1174_;
v___y_1169_ = v___x_1177_;
goto v___jp_1167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lam__0(lean_object* v_f_1195_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = l_Std_Format_defWidth;
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = l_Std_Format_pretty(v_f_1195_, v___x_1196_, v___x_1197_, v___x_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = ((lean_object*)(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0));
v___x_1206_ = l_Lean_stringToMessageData(v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg(lean_object* v_inst_1207_, lean_object* v_inst_1208_, lean_object* v_optDocComment_1209_){
_start:
{
lean_object* v_toApplicative_1210_; lean_object* v_toPure_1211_; lean_object* v___x_1212_; 
v_toApplicative_1210_ = lean_ctor_get(v_inst_1207_, 0);
v_toPure_1211_ = lean_ctor_get(v_toApplicative_1210_, 1);
v___x_1212_ = l_Lean_Syntax_getOptional_x3f(v_optDocComment_1209_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_inc(v_toPure_1211_);
lean_dec_ref(v_inst_1208_);
lean_dec_ref(v_inst_1207_);
v___x_1213_ = lean_box(0);
v___x_1214_ = lean_apply_2(v_toPure_1211_, lean_box(0), v___x_1213_);
return v___x_1214_;
}
else
{
lean_object* v_val_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1236_; 
v_val_1215_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1217_ = v___x_1212_;
v_isShared_1218_ = v_isSharedCheck_1236_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_val_1215_);
lean_dec(v___x_1212_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1236_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = l_Lean_Syntax_getArg(v_val_1215_, v___x_1219_);
if (lean_obj_tag(v___x_1220_) == 2)
{
lean_object* v_val_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
lean_inc(v_toPure_1211_);
lean_dec(v_val_1215_);
lean_dec_ref(v_inst_1208_);
lean_dec_ref(v_inst_1207_);
v_val_1221_ = lean_ctor_get(v___x_1220_, 1);
lean_inc_ref(v_val_1221_);
lean_dec_ref_known(v___x_1220_, 2);
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = lean_string_utf8_byte_size(v_val_1221_);
v___x_1224_ = lean_unsigned_to_nat(2u);
v___x_1225_ = lean_nat_sub(v___x_1223_, v___x_1224_);
v___x_1226_ = lean_string_utf8_extract(v_val_1221_, v___x_1222_, v___x_1225_);
lean_dec(v___x_1225_);
lean_dec_ref(v_val_1221_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1226_);
v___x_1228_ = v___x_1217_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_apply_2(v_toPure_1211_, lean_box(0), v___x_1228_);
return v___x_1229_;
}
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_del_object(v___x_1217_);
v___x_1231_ = lean_obj_once(&l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1, &l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1_once, _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1);
v___x_1232_ = l_Lean_MessageData_ofSyntax(v___x_1220_);
v___x_1233_ = l_Lean_indentD(v___x_1232_);
v___x_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1231_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = l_Lean_throwErrorAt___redArg(v_inst_1207_, v_inst_1208_, v_val_1215_, v___x_1234_);
return v___x_1235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___boxed(lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_optDocComment_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1237_, v_inst_1238_, v_optDocComment_1239_);
lean_dec(v_optDocComment_1239_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f(lean_object* v_m_1241_, lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v_optDocComment_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1242_, v_inst_1243_, v_optDocComment_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___boxed(lean_object* v_m_1246_, lean_object* v_inst_1247_, lean_object* v_inst_1248_, lean_object* v_optDocComment_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Elab_expandOptDocComment_x3f(v_m_1246_, v_inst_1247_, v_inst_1248_, v_optDocComment_1249_);
lean_dec(v_optDocComment_1249_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0(lean_object* v_unsafeStx_1251_, lean_object* v_stx_1252_, lean_object* v___y_1253_, uint8_t v_visibility_1254_, uint8_t v_isProtected_1255_, uint8_t v___y_1256_, uint8_t v___y_1257_, lean_object* v_toPure_1258_, lean_object* v_attrs_1259_){
_start:
{
uint8_t v___x_1260_; uint8_t v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1260_ = l_Lean_Syntax_isNone(v_unsafeStx_1251_);
v___x_1261_ = lean_bool_not(v___x_1260_);
v___x_1262_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1262_, 0, v_stx_1252_);
lean_ctor_set(v___x_1262_, 1, v___y_1253_);
lean_ctor_set(v___x_1262_, 2, v_attrs_1259_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*3, v_visibility_1254_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*3 + 1, v_isProtected_1255_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*3 + 2, v___y_1256_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*3 + 3, v___y_1257_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*3 + 4, v___x_1261_);
v___x_1263_ = lean_apply_2(v_toPure_1258_, lean_box(0), v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0___boxed(lean_object* v_unsafeStx_1264_, lean_object* v_stx_1265_, lean_object* v___y_1266_, lean_object* v_visibility_1267_, lean_object* v_isProtected_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v_toPure_1271_, lean_object* v_attrs_1272_){
_start:
{
uint8_t v_visibility_boxed_1273_; uint8_t v_isProtected_boxed_1274_; uint8_t v___y_406__boxed_1275_; uint8_t v___y_407__boxed_1276_; lean_object* v_res_1277_; 
v_visibility_boxed_1273_ = lean_unbox(v_visibility_1267_);
v_isProtected_boxed_1274_ = lean_unbox(v_isProtected_1268_);
v___y_406__boxed_1275_ = lean_unbox(v___y_1269_);
v___y_407__boxed_1276_ = lean_unbox(v___y_1270_);
v_res_1277_ = l_Lean_Elab_elabModifiers___redArg___lam__0(v_unsafeStx_1264_, v_stx_1265_, v___y_1266_, v_visibility_boxed_1273_, v_isProtected_boxed_1274_, v___y_406__boxed_1275_, v___y_407__boxed_1276_, v_toPure_1271_, v_attrs_1272_);
lean_dec(v_unsafeStx_1264_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__1(lean_object* v___f_1278_, lean_object* v_attrs_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_apply_1(v___f_1278_, v_attrs_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3(lean_object* v_protectedStx_1281_, lean_object* v_unsafeStx_1282_, lean_object* v_stx_1283_, lean_object* v___y_1284_, uint8_t v___y_1285_, uint8_t v___y_1286_, lean_object* v_toPure_1287_, lean_object* v_attrsStx_1288_, lean_object* v___x_1289_, lean_object* v_toBind_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_, uint8_t v_visibility_1303_){
_start:
{
uint8_t v___x_1304_; uint8_t v_isProtected_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___f_1310_; lean_object* v___x_1311_; 
v___x_1304_ = l_Lean_Syntax_isNone(v_protectedStx_1281_);
v_isProtected_1305_ = lean_bool_not(v___x_1304_);
v___x_1306_ = lean_box(v_visibility_1303_);
v___x_1307_ = lean_box(v_isProtected_1305_);
v___x_1308_ = lean_box(v___y_1285_);
v___x_1309_ = lean_box(v___y_1286_);
lean_inc(v_toPure_1287_);
v___f_1310_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_1310_, 0, v_unsafeStx_1282_);
lean_closure_set(v___f_1310_, 1, v_stx_1283_);
lean_closure_set(v___f_1310_, 2, v___y_1284_);
lean_closure_set(v___f_1310_, 3, v___x_1306_);
lean_closure_set(v___f_1310_, 4, v___x_1307_);
lean_closure_set(v___f_1310_, 5, v___x_1308_);
lean_closure_set(v___f_1310_, 6, v___x_1309_);
lean_closure_set(v___f_1310_, 7, v_toPure_1287_);
v___x_1311_ = l_Lean_Syntax_getOptional_x3f(v_attrsStx_1288_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v___f_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec(v_inst_1302_);
lean_dec(v_inst_1301_);
lean_dec_ref(v_inst_1300_);
lean_dec(v_inst_1299_);
lean_dec(v_inst_1298_);
lean_dec_ref(v_inst_1297_);
lean_dec_ref(v_inst_1296_);
lean_dec_ref(v_inst_1295_);
lean_dec_ref(v_inst_1294_);
lean_dec_ref(v_inst_1293_);
lean_dec_ref(v_inst_1292_);
lean_dec_ref(v_inst_1291_);
v___f_1312_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1312_, 0, v___f_1310_);
v___x_1313_ = lean_mk_empty_array_with_capacity(v___x_1289_);
v___x_1314_ = lean_apply_2(v_toPure_1287_, lean_box(0), v___x_1313_);
v___x_1315_ = lean_apply_4(v_toBind_1290_, lean_box(0), lean_box(0), v___x_1314_, v___f_1312_);
return v___x_1315_;
}
else
{
lean_object* v_val_1316_; lean_object* v___f_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec(v_toPure_1287_);
v_val_1316_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_val_1316_);
lean_dec_ref_known(v___x_1311_, 1);
v___f_1317_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1317_, 0, v___f_1310_);
v___x_1318_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_1291_, v_inst_1292_, v_inst_1293_, v_inst_1294_, v_inst_1295_, v_inst_1296_, v_inst_1297_, v_inst_1298_, v_inst_1299_, v_inst_1300_, v_inst_1301_, v_inst_1302_, v_val_1316_);
lean_dec(v_val_1316_);
v___x_1319_ = lean_apply_4(v_toBind_1290_, lean_box(0), lean_box(0), v___x_1318_, v___f_1317_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_protectedStx_1320_ = _args[0];
lean_object* v_unsafeStx_1321_ = _args[1];
lean_object* v_stx_1322_ = _args[2];
lean_object* v___y_1323_ = _args[3];
lean_object* v___y_1324_ = _args[4];
lean_object* v___y_1325_ = _args[5];
lean_object* v_toPure_1326_ = _args[6];
lean_object* v_attrsStx_1327_ = _args[7];
lean_object* v___x_1328_ = _args[8];
lean_object* v_toBind_1329_ = _args[9];
lean_object* v_inst_1330_ = _args[10];
lean_object* v_inst_1331_ = _args[11];
lean_object* v_inst_1332_ = _args[12];
lean_object* v_inst_1333_ = _args[13];
lean_object* v_inst_1334_ = _args[14];
lean_object* v_inst_1335_ = _args[15];
lean_object* v_inst_1336_ = _args[16];
lean_object* v_inst_1337_ = _args[17];
lean_object* v_inst_1338_ = _args[18];
lean_object* v_inst_1339_ = _args[19];
lean_object* v_inst_1340_ = _args[20];
lean_object* v_inst_1341_ = _args[21];
lean_object* v_visibility_1342_ = _args[22];
_start:
{
uint8_t v___y_427__boxed_1343_; uint8_t v___y_428__boxed_1344_; uint8_t v_visibility_boxed_1345_; lean_object* v_res_1346_; 
v___y_427__boxed_1343_ = lean_unbox(v___y_1324_);
v___y_428__boxed_1344_ = lean_unbox(v___y_1325_);
v_visibility_boxed_1345_ = lean_unbox(v_visibility_1342_);
v_res_1346_ = l_Lean_Elab_elabModifiers___redArg___lam__3(v_protectedStx_1320_, v_unsafeStx_1321_, v_stx_1322_, v___y_1323_, v___y_427__boxed_1343_, v___y_428__boxed_1344_, v_toPure_1326_, v_attrsStx_1327_, v___x_1328_, v_toBind_1329_, v_inst_1330_, v_inst_1331_, v_inst_1332_, v_inst_1333_, v_inst_1334_, v_inst_1335_, v_inst_1336_, v_inst_1337_, v_inst_1338_, v_inst_1339_, v_inst_1340_, v_inst_1341_, v_visibility_boxed_1345_);
lean_dec(v___x_1328_);
lean_dec(v_attrsStx_1327_);
lean_dec(v_protectedStx_1320_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg(lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_inst_1361_, lean_object* v_inst_1362_, lean_object* v_inst_1363_, lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_inst_1368_, lean_object* v_stx_1369_){
_start:
{
lean_object* v_toApplicative_1370_; lean_object* v_toBind_1371_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v_toPure_1377_; lean_object* v___x_1378_; lean_object* v_docCommentStx_1379_; lean_object* v___x_1380_; lean_object* v_attrsStx_1381_; lean_object* v___x_1382_; lean_object* v_visibilityStx_1383_; lean_object* v___x_1384_; lean_object* v_protectedStx_1385_; lean_object* v___y_1387_; uint8_t v___y_1388_; uint8_t v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1405_; uint8_t v___y_1406_; uint8_t v___y_1407_; uint8_t v___y_1419_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_toApplicative_1370_ = lean_ctor_get(v_inst_1357_, 0);
v_toBind_1371_ = lean_ctor_get(v_inst_1357_, 1);
lean_inc(v_toBind_1371_);
v_toPure_1377_ = lean_ctor_get(v_toApplicative_1370_, 1);
v___x_1378_ = lean_unsigned_to_nat(0u);
v_docCommentStx_1379_ = l_Lean_Syntax_getArg(v_stx_1369_, v___x_1378_);
v___x_1380_ = lean_unsigned_to_nat(1u);
v_attrsStx_1381_ = l_Lean_Syntax_getArg(v_stx_1369_, v___x_1380_);
v___x_1382_ = lean_unsigned_to_nat(2u);
v_visibilityStx_1383_ = l_Lean_Syntax_getArg(v_stx_1369_, v___x_1382_);
v___x_1384_ = lean_unsigned_to_nat(3u);
v_protectedStx_1385_ = l_Lean_Syntax_getArg(v_stx_1369_, v___x_1384_);
v___x_1432_ = lean_unsigned_to_nat(4u);
v___x_1433_ = l_Lean_Syntax_getArg(v_stx_1369_, v___x_1432_);
v___x_1434_ = l_Lean_Syntax_isNone(v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1435_ = l_Lean_Syntax_getArg(v___x_1433_, v___x_1378_);
lean_dec(v___x_1433_);
v___x_1436_ = l_Lean_Syntax_getKind(v___x_1435_);
v___x_1437_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__1));
v___x_1438_ = lean_name_eq(v___x_1436_, v___x_1437_);
lean_dec(v___x_1436_);
if (v___x_1438_ == 0)
{
uint8_t v___x_1439_; 
v___x_1439_ = 2;
v___y_1419_ = v___x_1439_;
goto v___jp_1418_;
}
else
{
uint8_t v___x_1440_; 
v___x_1440_ = 1;
v___y_1419_ = v___x_1440_;
goto v___jp_1418_;
}
}
else
{
uint8_t v___x_1441_; 
lean_dec(v___x_1433_);
v___x_1441_ = 0;
v___y_1419_ = v___x_1441_;
goto v___jp_1418_;
}
v___jp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = l_Lean_Elab_elabVisibility___redArg(v_inst_1357_, v_inst_1360_, v_inst_1358_, v_inst_1365_, v_inst_1367_, v_inst_1366_, v___y_1374_);
v___x_1376_ = lean_apply_4(v_toBind_1371_, lean_box(0), lean_box(0), v___x_1375_, v___y_1373_);
return v___x_1376_;
}
v___jp_1386_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___f_1393_; lean_object* v___x_1394_; 
v___x_1391_ = lean_box(v___y_1388_);
v___x_1392_ = lean_box(v___y_1389_);
lean_inc_ref(v_inst_1367_);
lean_inc(v_inst_1366_);
lean_inc(v_inst_1365_);
lean_inc_ref(v_inst_1360_);
lean_inc_ref(v_inst_1358_);
lean_inc_ref(v_inst_1357_);
lean_inc(v_toBind_1371_);
lean_inc(v_toPure_1377_);
v___f_1393_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__3___boxed), 23, 22);
lean_closure_set(v___f_1393_, 0, v_protectedStx_1385_);
lean_closure_set(v___f_1393_, 1, v___y_1387_);
lean_closure_set(v___f_1393_, 2, v_stx_1369_);
lean_closure_set(v___f_1393_, 3, v___y_1390_);
lean_closure_set(v___f_1393_, 4, v___x_1391_);
lean_closure_set(v___f_1393_, 5, v___x_1392_);
lean_closure_set(v___f_1393_, 6, v_toPure_1377_);
lean_closure_set(v___f_1393_, 7, v_attrsStx_1381_);
lean_closure_set(v___f_1393_, 8, v___x_1378_);
lean_closure_set(v___f_1393_, 9, v_toBind_1371_);
lean_closure_set(v___f_1393_, 10, v_inst_1357_);
lean_closure_set(v___f_1393_, 11, v_inst_1358_);
lean_closure_set(v___f_1393_, 12, v_inst_1359_);
lean_closure_set(v___f_1393_, 13, v_inst_1360_);
lean_closure_set(v___f_1393_, 14, v_inst_1362_);
lean_closure_set(v___f_1393_, 15, v_inst_1363_);
lean_closure_set(v___f_1393_, 16, v_inst_1364_);
lean_closure_set(v___f_1393_, 17, v_inst_1365_);
lean_closure_set(v___f_1393_, 18, v_inst_1366_);
lean_closure_set(v___f_1393_, 19, v_inst_1367_);
lean_closure_set(v___f_1393_, 20, v_inst_1368_);
lean_closure_set(v___f_1393_, 21, v_inst_1361_);
v___x_1394_ = l_Lean_Syntax_getOptional_x3f(v_visibilityStx_1383_);
lean_dec(v_visibilityStx_1383_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_box(0);
v___y_1373_ = v___f_1393_;
v___y_1374_ = v___x_1395_;
goto v___jp_1372_;
}
else
{
lean_object* v_val_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
v_val_1396_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1394_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_val_1396_);
lean_dec(v___x_1394_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_val_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
v___y_1373_ = v___f_1393_;
v___y_1374_ = v___x_1401_;
goto v___jp_1372_;
}
}
}
}
v___jp_1404_:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_Syntax_getOptional_x3f(v_docCommentStx_1379_);
lean_dec(v_docCommentStx_1379_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v___x_1409_; 
v___x_1409_ = lean_box(0);
v___y_1387_ = v___y_1405_;
v___y_1388_ = v___y_1406_;
v___y_1389_ = v___y_1407_;
v___y_1390_ = v___x_1409_;
goto v___jp_1386_;
}
else
{
lean_object* v_val_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
v_val_1410_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1408_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_val_1410_);
lean_dec(v___x_1408_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_val_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
v___y_1387_ = v___y_1405_;
v___y_1388_ = v___y_1406_;
v___y_1389_ = v___y_1407_;
v___y_1390_ = v___x_1415_;
goto v___jp_1386_;
}
}
}
}
v___jp_1418_:
{
lean_object* v___x_1420_; lean_object* v_unsafeStx_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1420_ = lean_unsigned_to_nat(5u);
v_unsafeStx_1421_ = l_Lean_Syntax_getArg(v_stx_1369_, v___x_1420_);
v___x_1422_ = lean_unsigned_to_nat(6u);
v___x_1423_ = l_Lean_Syntax_getArg(v_stx_1369_, v___x_1422_);
v___x_1424_ = l_Lean_Syntax_isNone(v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1425_ = l_Lean_Syntax_getArg(v___x_1423_, v___x_1378_);
lean_dec(v___x_1423_);
v___x_1426_ = l_Lean_Syntax_getKind(v___x_1425_);
v___x_1427_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__0));
v___x_1428_ = lean_name_eq(v___x_1426_, v___x_1427_);
lean_dec(v___x_1426_);
if (v___x_1428_ == 0)
{
uint8_t v___x_1429_; 
v___x_1429_ = 1;
v___y_1405_ = v_unsafeStx_1421_;
v___y_1406_ = v___y_1419_;
v___y_1407_ = v___x_1429_;
goto v___jp_1404_;
}
else
{
uint8_t v___x_1430_; 
v___x_1430_ = 0;
v___y_1405_ = v_unsafeStx_1421_;
v___y_1406_ = v___y_1419_;
v___y_1407_ = v___x_1430_;
goto v___jp_1404_;
}
}
else
{
uint8_t v___x_1431_; 
lean_dec(v___x_1423_);
v___x_1431_ = 2;
v___y_1405_ = v_unsafeStx_1421_;
v___y_1406_ = v___y_1419_;
v___y_1407_ = v___x_1431_;
goto v___jp_1404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object* v_m_1442_, lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_inst_1445_, lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_inst_1448_, lean_object* v_inst_1449_, lean_object* v_inst_1450_, lean_object* v_inst_1451_, lean_object* v_inst_1452_, lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_stx_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_Elab_elabModifiers___redArg(v_inst_1443_, v_inst_1444_, v_inst_1445_, v_inst_1446_, v_inst_1447_, v_inst_1448_, v_inst_1449_, v_inst_1450_, v_inst_1451_, v_inst_1452_, v_inst_1453_, v_inst_1454_, v_stx_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__0(lean_object* v_toPure_1457_, lean_object* v_declName_1458_, lean_object* v_____r_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_apply_2(v_toPure_1457_, lean_box(0), v_declName_1458_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__1(lean_object* v_declName_1461_, lean_object* v_env_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_addProtected(v_env_1462_, v_declName_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2(lean_object* v_modifiers_1464_, lean_object* v_toPure_1465_, lean_object* v_declName_1466_, lean_object* v_modifyEnv_1467_, lean_object* v___f_1468_, lean_object* v_toBind_1469_, lean_object* v___f_1470_, lean_object* v_____r_1471_){
_start:
{
uint8_t v_isProtected_1472_; 
v_isProtected_1472_ = lean_ctor_get_uint8(v_modifiers_1464_, sizeof(void*)*3 + 1);
if (v_isProtected_1472_ == 0)
{
lean_object* v___x_1473_; 
lean_dec(v___f_1470_);
lean_dec(v_toBind_1469_);
lean_dec_ref(v___f_1468_);
lean_dec(v_modifyEnv_1467_);
v___x_1473_ = lean_apply_2(v_toPure_1465_, lean_box(0), v_declName_1466_);
return v___x_1473_;
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec(v_declName_1466_);
lean_dec(v_toPure_1465_);
v___x_1474_ = lean_apply_1(v_modifyEnv_1467_, v___f_1468_);
v___x_1475_ = lean_apply_4(v_toBind_1469_, lean_box(0), lean_box(0), v___x_1474_, v___f_1470_);
return v___x_1475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2___boxed(lean_object* v_modifiers_1476_, lean_object* v_toPure_1477_, lean_object* v_declName_1478_, lean_object* v_modifyEnv_1479_, lean_object* v___f_1480_, lean_object* v_toBind_1481_, lean_object* v___f_1482_, lean_object* v_____r_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Elab_applyVisibility___redArg___lam__2(v_modifiers_1476_, v_toPure_1477_, v_declName_1478_, v_modifyEnv_1479_, v___f_1480_, v_toBind_1481_, v___f_1482_, v_____r_1483_);
lean_dec_ref(v_modifiers_1476_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__3(lean_object* v_toPure_1485_, lean_object* v_modifiers_1486_, lean_object* v_modifyEnv_1487_, lean_object* v_toBind_1488_, lean_object* v_inst_1489_, lean_object* v_inst_1490_, lean_object* v_inst_1491_, lean_object* v_inst_1492_, lean_object* v_inst_1493_, lean_object* v_____r_1494_, lean_object* v_declName_1495_){
_start:
{
lean_object* v___f_1496_; lean_object* v___f_1497_; lean_object* v___f_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_inc_n(v_declName_1495_, 3);
lean_inc(v_toPure_1485_);
v___f_1496_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1496_, 0, v_toPure_1485_);
lean_closure_set(v___f_1496_, 1, v_declName_1495_);
v___f_1497_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1497_, 0, v_declName_1495_);
lean_inc(v_toBind_1488_);
v___f_1498_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1498_, 0, v_modifiers_1486_);
lean_closure_set(v___f_1498_, 1, v_toPure_1485_);
lean_closure_set(v___f_1498_, 2, v_declName_1495_);
lean_closure_set(v___f_1498_, 3, v_modifyEnv_1487_);
lean_closure_set(v___f_1498_, 4, v___f_1497_);
lean_closure_set(v___f_1498_, 5, v_toBind_1488_);
lean_closure_set(v___f_1498_, 6, v___f_1496_);
v___x_1499_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(v_inst_1489_, v_inst_1490_, v_inst_1491_, v_inst_1492_, v_inst_1493_, v_declName_1495_);
v___x_1500_ = lean_apply_4(v_toBind_1488_, lean_box(0), lean_box(0), v___x_1499_, v___f_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4(lean_object* v_declName_1501_, lean_object* v___f_1502_, lean_object* v_____do__lift_1503_){
_start:
{
lean_object* v_declName_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v_declName_1504_ = l_Lean_mkPrivateName(v_____do__lift_1503_, v_declName_1501_);
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_apply_2(v___f_1502_, v___x_1505_, v_declName_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4___boxed(lean_object* v_declName_1507_, lean_object* v___f_1508_, lean_object* v_____do__lift_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_Elab_applyVisibility___redArg___lam__4(v_declName_1507_, v___f_1508_, v_____do__lift_1509_);
lean_dec_ref(v_____do__lift_1509_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5(lean_object* v_modifiers_1511_, lean_object* v___f_1512_, lean_object* v_declName_1513_, lean_object* v_toBind_1514_, lean_object* v_getEnv_1515_, lean_object* v___f_1516_, lean_object* v_____do__lift_1517_){
_start:
{
uint8_t v_visibility_1518_; uint8_t v___x_1519_; uint8_t v___x_1520_; 
v_visibility_1518_ = lean_ctor_get_uint8(v_modifiers_1511_, sizeof(void*)*3);
v___x_1519_ = l_Lean_Elab_Visibility_isInferredPublic(v_____do__lift_1517_, v_visibility_1518_);
v___x_1520_ = lean_bool_not(v___x_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec(v___f_1516_);
lean_dec(v_getEnv_1515_);
lean_dec(v_toBind_1514_);
v___x_1521_ = lean_box(0);
v___x_1522_ = lean_apply_2(v___f_1512_, v___x_1521_, v_declName_1513_);
return v___x_1522_;
}
else
{
lean_object* v___x_1523_; 
lean_dec(v_declName_1513_);
lean_dec(v___f_1512_);
v___x_1523_ = lean_apply_4(v_toBind_1514_, lean_box(0), lean_box(0), v_getEnv_1515_, v___f_1516_);
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5___boxed(lean_object* v_modifiers_1524_, lean_object* v___f_1525_, lean_object* v_declName_1526_, lean_object* v_toBind_1527_, lean_object* v_getEnv_1528_, lean_object* v___f_1529_, lean_object* v_____do__lift_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Elab_applyVisibility___redArg___lam__5(v_modifiers_1524_, v___f_1525_, v_declName_1526_, v_toBind_1527_, v_getEnv_1528_, v___f_1529_, v_____do__lift_1530_);
lean_dec_ref(v_____do__lift_1530_);
lean_dec_ref(v_modifiers_1524_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg(lean_object* v_inst_1532_, lean_object* v_inst_1533_, lean_object* v_inst_1534_, lean_object* v_inst_1535_, lean_object* v_inst_1536_, lean_object* v_modifiers_1537_, lean_object* v_declName_1538_){
_start:
{
lean_object* v_toApplicative_1539_; lean_object* v_toBind_1540_; lean_object* v_getEnv_1541_; lean_object* v_modifyEnv_1542_; lean_object* v_toPure_1543_; lean_object* v___f_1544_; lean_object* v___f_1545_; lean_object* v___f_1546_; lean_object* v___x_1547_; 
v_toApplicative_1539_ = lean_ctor_get(v_inst_1532_, 0);
v_toBind_1540_ = lean_ctor_get(v_inst_1532_, 1);
lean_inc_n(v_toBind_1540_, 3);
v_getEnv_1541_ = lean_ctor_get(v_inst_1533_, 0);
lean_inc_n(v_getEnv_1541_, 2);
v_modifyEnv_1542_ = lean_ctor_get(v_inst_1533_, 1);
lean_inc(v_modifyEnv_1542_);
v_toPure_1543_ = lean_ctor_get(v_toApplicative_1539_, 1);
lean_inc(v_toPure_1543_);
lean_inc_ref(v_modifiers_1537_);
v___f_1544_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__3), 11, 9);
lean_closure_set(v___f_1544_, 0, v_toPure_1543_);
lean_closure_set(v___f_1544_, 1, v_modifiers_1537_);
lean_closure_set(v___f_1544_, 2, v_modifyEnv_1542_);
lean_closure_set(v___f_1544_, 3, v_toBind_1540_);
lean_closure_set(v___f_1544_, 4, v_inst_1532_);
lean_closure_set(v___f_1544_, 5, v_inst_1533_);
lean_closure_set(v___f_1544_, 6, v_inst_1534_);
lean_closure_set(v___f_1544_, 7, v_inst_1535_);
lean_closure_set(v___f_1544_, 8, v_inst_1536_);
lean_inc_ref(v___f_1544_);
lean_inc(v_declName_1538_);
v___f_1545_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_1545_, 0, v_declName_1538_);
lean_closure_set(v___f_1545_, 1, v___f_1544_);
v___f_1546_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1546_, 0, v_modifiers_1537_);
lean_closure_set(v___f_1546_, 1, v___f_1544_);
lean_closure_set(v___f_1546_, 2, v_declName_1538_);
lean_closure_set(v___f_1546_, 3, v_toBind_1540_);
lean_closure_set(v___f_1546_, 4, v_getEnv_1541_);
lean_closure_set(v___f_1546_, 5, v___f_1545_);
v___x_1547_ = lean_apply_4(v_toBind_1540_, lean_box(0), lean_box(0), v_getEnv_1541_, v___f_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility(lean_object* v_m_1548_, lean_object* v_inst_1549_, lean_object* v_inst_1550_, lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_modifiers_1554_, lean_object* v_declName_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1549_, v_inst_1550_, v_inst_1551_, v_inst_1552_, v_inst_1553_, v_modifiers_1554_, v_declName_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0(lean_object* v_toPure_1557_, lean_object* v_____s_1558_){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_apply_2(v_toPure_1557_, lean_box(0), v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1(lean_object* v___x_1561_, lean_object* v_toPure_1562_, lean_object* v_r_1563_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1561_);
v___x_1565_ = lean_apply_2(v_toPure_1562_, lean_box(0), v___x_1564_);
return v___x_1565_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0));
v___x_1568_ = l_Lean_stringToMessageData(v___x_1567_);
return v___x_1568_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2));
v___x_1571_ = l_Lean_stringToMessageData(v___x_1570_);
return v___x_1571_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4));
v___x_1574_ = l_Lean_stringToMessageData(v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2(lean_object* v_pre_1575_, lean_object* v_declName_1576_, lean_object* v___x_1577_, lean_object* v_toPure_1578_, lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_toBind_1581_, lean_object* v___f_1582_, lean_object* v_a_1583_, lean_object* v_x_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1586_; uint8_t v___x_1587_; 
lean_inc(v_a_1583_);
lean_inc(v_pre_1575_);
v___x_1586_ = l_Lean_Name_append(v_pre_1575_, v_a_1583_);
v___x_1587_ = lean_name_eq(v___x_1586_, v_declName_1576_);
lean_dec(v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec(v_a_1583_);
lean_dec(v___f_1582_);
lean_dec(v_toBind_1581_);
lean_dec_ref(v_inst_1580_);
lean_dec_ref(v_inst_1579_);
lean_dec(v_declName_1576_);
lean_dec(v_pre_1575_);
v___x_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1577_);
v___x_1589_ = lean_apply_2(v_toPure_1578_, lean_box(0), v___x_1588_);
return v___x_1589_;
}
else
{
lean_object* v___x_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec(v_toPure_1578_);
v___x_1590_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1591_ = 0;
v___x_1592_ = l_Lean_MessageData_ofConstName(v_declName_1576_, v___x_1591_);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1590_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = l_Lean_MessageData_ofName(v_pre_1575_);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_1599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = l_Lean_MessageData_ofName(v_a_1583_);
v___x_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = l_Lean_throwError___redArg(v_inst_1579_, v_inst_1580_, v___x_1603_);
v___x_1605_ = lean_apply_4(v_toBind_1581_, lean_box(0), lean_box(0), v___x_1604_, v___f_1582_);
return v___x_1605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(lean_object* v_pre_1606_, uint8_t v___x_1607_, lean_object* v_toPure_1608_, lean_object* v_declName_1609_, lean_object* v_inst_1610_, lean_object* v_inst_1611_, lean_object* v_toBind_1612_, lean_object* v___f_1613_, lean_object* v_____do__lift_1614_){
_start:
{
lean_object* v_fieldNames_1615_; lean_object* v___x_1616_; lean_object* v___f_1617_; lean_object* v___f_1618_; size_t v_sz_1619_; size_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_inc(v_pre_1606_);
v_fieldNames_1615_ = l_Lean_getStructureFieldsFlattened(v_____do__lift_1614_, v_pre_1606_, v___x_1607_);
v___x_1616_ = lean_box(0);
lean_inc(v_toPure_1608_);
v___f_1617_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1617_, 0, v___x_1616_);
lean_closure_set(v___f_1617_, 1, v_toPure_1608_);
lean_inc(v_toBind_1612_);
lean_inc_ref(v_inst_1610_);
v___f_1618_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2), 11, 8);
lean_closure_set(v___f_1618_, 0, v_pre_1606_);
lean_closure_set(v___f_1618_, 1, v_declName_1609_);
lean_closure_set(v___f_1618_, 2, v___x_1616_);
lean_closure_set(v___f_1618_, 3, v_toPure_1608_);
lean_closure_set(v___f_1618_, 4, v_inst_1610_);
lean_closure_set(v___f_1618_, 5, v_inst_1611_);
lean_closure_set(v___f_1618_, 6, v_toBind_1612_);
lean_closure_set(v___f_1618_, 7, v___f_1617_);
v_sz_1619_ = lean_array_size(v_fieldNames_1615_);
v___x_1620_ = ((size_t)0ULL);
v___x_1621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1610_, v_fieldNames_1615_, v___f_1618_, v_sz_1619_, v___x_1620_, v___x_1616_);
v___x_1622_ = lean_apply_4(v_toBind_1612_, lean_box(0), lean_box(0), v___x_1621_, v___f_1613_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed(lean_object* v_pre_1623_, lean_object* v___x_1624_, lean_object* v_toPure_1625_, lean_object* v_declName_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_toBind_1629_, lean_object* v___f_1630_, lean_object* v_____do__lift_1631_){
_start:
{
uint8_t v___x_672__boxed_1632_; lean_object* v_res_1633_; 
v___x_672__boxed_1632_ = lean_unbox(v___x_1624_);
v_res_1633_ = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(v_pre_1623_, v___x_672__boxed_1632_, v_toPure_1625_, v_declName_1626_, v_inst_1627_, v_inst_1628_, v_toBind_1629_, v___f_1630_, v_____do__lift_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4(lean_object* v_pre_1634_, lean_object* v_toPure_1635_, lean_object* v_declName_1636_, lean_object* v_inst_1637_, lean_object* v_inst_1638_, lean_object* v_toBind_1639_, lean_object* v___f_1640_, lean_object* v_getEnv_1641_, lean_object* v_____do__lift_1642_){
_start:
{
uint8_t v___x_1643_; 
lean_inc(v_pre_1634_);
v___x_1643_ = l_Lean_isStructure(v_____do__lift_1642_, v_pre_1634_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_dec(v_getEnv_1641_);
lean_dec(v___f_1640_);
lean_dec(v_toBind_1639_);
lean_dec_ref(v_inst_1638_);
lean_dec_ref(v_inst_1637_);
lean_dec(v_declName_1636_);
lean_dec(v_pre_1634_);
v___x_1644_ = lean_box(0);
v___x_1645_ = lean_apply_2(v_toPure_1635_, lean_box(0), v___x_1644_);
return v___x_1645_;
}
else
{
lean_object* v___x_1646_; lean_object* v___f_1647_; lean_object* v___x_1648_; 
v___x_1646_ = lean_box(v___x_1643_);
lean_inc(v_toBind_1639_);
v___f_1647_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1647_, 0, v_pre_1634_);
lean_closure_set(v___f_1647_, 1, v___x_1646_);
lean_closure_set(v___f_1647_, 2, v_toPure_1635_);
lean_closure_set(v___f_1647_, 3, v_declName_1636_);
lean_closure_set(v___f_1647_, 4, v_inst_1637_);
lean_closure_set(v___f_1647_, 5, v_inst_1638_);
lean_closure_set(v___f_1647_, 6, v_toBind_1639_);
lean_closure_set(v___f_1647_, 7, v___f_1640_);
v___x_1648_ = lean_apply_4(v_toBind_1639_, lean_box(0), lean_box(0), v_getEnv_1641_, v___f_1647_);
return v___x_1648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg(lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_inst_1651_, lean_object* v_declName_1652_){
_start:
{
if (lean_obj_tag(v_declName_1652_) == 1)
{
lean_object* v_toApplicative_1653_; lean_object* v_toBind_1654_; lean_object* v_toPure_1655_; lean_object* v_pre_1656_; lean_object* v_getEnv_1657_; lean_object* v___f_1658_; lean_object* v___f_1659_; lean_object* v___x_1660_; 
v_toApplicative_1653_ = lean_ctor_get(v_inst_1649_, 0);
v_toBind_1654_ = lean_ctor_get(v_inst_1649_, 1);
lean_inc_n(v_toBind_1654_, 2);
v_toPure_1655_ = lean_ctor_get(v_toApplicative_1653_, 1);
lean_inc_n(v_toPure_1655_, 2);
v_pre_1656_ = lean_ctor_get(v_declName_1652_, 0);
lean_inc(v_pre_1656_);
v_getEnv_1657_ = lean_ctor_get(v_inst_1650_, 0);
lean_inc_n(v_getEnv_1657_, 2);
lean_dec_ref(v_inst_1650_);
v___f_1658_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1658_, 0, v_toPure_1655_);
v___f_1659_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1659_, 0, v_pre_1656_);
lean_closure_set(v___f_1659_, 1, v_toPure_1655_);
lean_closure_set(v___f_1659_, 2, v_declName_1652_);
lean_closure_set(v___f_1659_, 3, v_inst_1649_);
lean_closure_set(v___f_1659_, 4, v_inst_1651_);
lean_closure_set(v___f_1659_, 5, v_toBind_1654_);
lean_closure_set(v___f_1659_, 6, v___f_1658_);
lean_closure_set(v___f_1659_, 7, v_getEnv_1657_);
v___x_1660_ = lean_apply_4(v_toBind_1654_, lean_box(0), lean_box(0), v_getEnv_1657_, v___f_1659_);
return v___x_1660_;
}
else
{
lean_object* v_toApplicative_1661_; lean_object* v_toPure_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_toApplicative_1661_ = lean_ctor_get(v_inst_1649_, 0);
lean_inc_ref(v_toApplicative_1661_);
lean_dec(v_declName_1652_);
lean_dec_ref(v_inst_1651_);
lean_dec_ref(v_inst_1650_);
lean_dec_ref(v_inst_1649_);
v_toPure_1662_ = lean_ctor_get(v_toApplicative_1661_, 1);
lean_inc(v_toPure_1662_);
lean_dec_ref(v_toApplicative_1661_);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_apply_2(v_toPure_1662_, lean_box(0), v___x_1663_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField(lean_object* v_m_1665_, lean_object* v_inst_1666_, lean_object* v_inst_1667_, lean_object* v_inst_1668_, lean_object* v_declName_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1666_, v_inst_1667_, v_inst_1668_, v_declName_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__0(lean_object* v_toApplicative_1671_, lean_object* v_declName_1672_, lean_object* v_shortName_1673_, lean_object* v_____r_1674_){
_start:
{
lean_object* v_toPure_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_toPure_1675_ = lean_ctor_get(v_toApplicative_1671_, 1);
lean_inc(v_toPure_1675_);
lean_dec_ref(v_toApplicative_1671_);
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v_declName_1672_);
lean_ctor_set(v___x_1676_, 1, v_shortName_1673_);
v___x_1677_ = lean_apply_2(v_toPure_1675_, lean_box(0), v___x_1676_);
return v___x_1677_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0));
v___x_1680_ = l_Lean_stringToMessageData(v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2(lean_object* v_modifiers_1681_, lean_object* v_toApplicative_1682_, lean_object* v_shortName_1683_, lean_object* v_currNamespace_1684_, lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v_toBind_1687_, lean_object* v_declName_1688_){
_start:
{
uint8_t v_isProtected_1689_; 
v_isProtected_1689_ = lean_ctor_get_uint8(v_modifiers_1681_, sizeof(void*)*3 + 1);
if (v_isProtected_1689_ == 0)
{
lean_object* v_toPure_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec(v_toBind_1687_);
lean_dec_ref(v_inst_1686_);
lean_dec_ref(v_inst_1685_);
lean_dec(v_currNamespace_1684_);
v_toPure_1690_ = lean_ctor_get(v_toApplicative_1682_, 1);
lean_inc(v_toPure_1690_);
lean_dec_ref(v_toApplicative_1682_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v_declName_1688_);
lean_ctor_set(v___x_1691_, 1, v_shortName_1683_);
v___x_1692_ = lean_apply_2(v_toPure_1690_, lean_box(0), v___x_1691_);
return v___x_1692_;
}
else
{
if (lean_obj_tag(v_currNamespace_1684_) == 1)
{
lean_object* v_str_1693_; lean_object* v_toPure_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_dec(v_toBind_1687_);
lean_dec_ref(v_inst_1686_);
lean_dec_ref(v_inst_1685_);
v_str_1693_ = lean_ctor_get(v_currNamespace_1684_, 1);
lean_inc_ref(v_str_1693_);
lean_dec_ref_known(v_currNamespace_1684_, 2);
v_toPure_1694_ = lean_ctor_get(v_toApplicative_1682_, 1);
lean_inc(v_toPure_1694_);
lean_dec_ref(v_toApplicative_1682_);
v___x_1695_ = lean_box(0);
v___x_1696_ = l_Lean_Name_str___override(v___x_1695_, v_str_1693_);
v___x_1697_ = l_Lean_Name_append(v___x_1696_, v_shortName_1683_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v_declName_1688_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_apply_2(v_toPure_1694_, lean_box(0), v___x_1698_);
return v___x_1699_;
}
else
{
lean_object* v___f_1700_; uint8_t v___x_1701_; 
lean_dec(v_currNamespace_1684_);
lean_inc(v_shortName_1683_);
lean_inc(v_declName_1688_);
lean_inc_ref(v_toApplicative_1682_);
v___f_1700_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1700_, 0, v_toApplicative_1682_);
lean_closure_set(v___f_1700_, 1, v_declName_1688_);
lean_closure_set(v___f_1700_, 2, v_shortName_1683_);
v___x_1701_ = l_Lean_Name_isAtomic(v_shortName_1683_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_dec_ref(v___f_1700_);
lean_dec(v_toBind_1687_);
lean_dec_ref(v_inst_1686_);
lean_dec_ref(v_inst_1685_);
v___x_1702_ = lean_box(0);
v___x_1703_ = l_Lean_Elab_mkDeclName___redArg___lam__0(v_toApplicative_1682_, v_declName_1688_, v_shortName_1683_, v___x_1702_);
return v___x_1703_;
}
else
{
lean_object* v___f_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec(v_declName_1688_);
lean_dec(v_shortName_1683_);
lean_dec_ref(v_toApplicative_1682_);
v___f_1704_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1704_, 0, v___f_1700_);
v___x_1705_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_1706_ = l_Lean_throwError___redArg(v_inst_1685_, v_inst_1686_, v___x_1705_);
v___x_1707_ = lean_apply_4(v_toBind_1687_, lean_box(0), lean_box(0), v___x_1706_, v___f_1704_);
return v___x_1707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2___boxed(lean_object* v_modifiers_1708_, lean_object* v_toApplicative_1709_, lean_object* v_shortName_1710_, lean_object* v_currNamespace_1711_, lean_object* v_inst_1712_, lean_object* v_inst_1713_, lean_object* v_toBind_1714_, lean_object* v_declName_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Elab_mkDeclName___redArg___lam__2(v_modifiers_1708_, v_toApplicative_1709_, v_shortName_1710_, v_currNamespace_1711_, v_inst_1712_, v_inst_1713_, v_toBind_1714_, v_declName_1715_);
lean_dec_ref(v_modifiers_1708_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__1(lean_object* v_inst_1717_, lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_modifiers_1722_, lean_object* v___y_1723_, lean_object* v_toBind_1724_, lean_object* v___f_1725_, lean_object* v_____r_1726_){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1717_, v_inst_1718_, v_inst_1719_, v_inst_1720_, v_inst_1721_, v_modifiers_1722_, v___y_1723_);
v___x_1728_ = lean_apply_4(v_toBind_1724_, lean_box(0), lean_box(0), v___x_1727_, v___f_1725_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3(lean_object* v_modifiers_1729_, lean_object* v_toApplicative_1730_, lean_object* v_inst_1731_, lean_object* v_inst_1732_, lean_object* v_toBind_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v___y_1737_, lean_object* v_____r_1738_, lean_object* v_shortName_1739_, lean_object* v_currNamespace_1740_){
_start:
{
lean_object* v___f_1741_; lean_object* v___f_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_inc_n(v_toBind_1733_, 2);
lean_inc_ref_n(v_inst_1732_, 2);
lean_inc_ref_n(v_inst_1731_, 2);
lean_inc_ref(v_modifiers_1729_);
v___f_1741_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1741_, 0, v_modifiers_1729_);
lean_closure_set(v___f_1741_, 1, v_toApplicative_1730_);
lean_closure_set(v___f_1741_, 2, v_shortName_1739_);
lean_closure_set(v___f_1741_, 3, v_currNamespace_1740_);
lean_closure_set(v___f_1741_, 4, v_inst_1731_);
lean_closure_set(v___f_1741_, 5, v_inst_1732_);
lean_closure_set(v___f_1741_, 6, v_toBind_1733_);
lean_inc(v___y_1737_);
lean_inc_ref(v_inst_1734_);
v___f_1742_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1742_, 0, v_inst_1731_);
lean_closure_set(v___f_1742_, 1, v_inst_1734_);
lean_closure_set(v___f_1742_, 2, v_inst_1732_);
lean_closure_set(v___f_1742_, 3, v_inst_1735_);
lean_closure_set(v___f_1742_, 4, v_inst_1736_);
lean_closure_set(v___f_1742_, 5, v_modifiers_1729_);
lean_closure_set(v___f_1742_, 6, v___y_1737_);
lean_closure_set(v___f_1742_, 7, v_toBind_1733_);
lean_closure_set(v___f_1742_, 8, v___f_1741_);
v___x_1743_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1731_, v_inst_1734_, v_inst_1732_, v___y_1737_);
v___x_1744_ = lean_apply_4(v_toBind_1733_, lean_box(0), lean_box(0), v___x_1743_, v___f_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__4(lean_object* v___f_1745_, lean_object* v_shortName_1746_, lean_object* v_currNamespace_1747_, lean_object* v_____r_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_apply_3(v___f_1745_, v_____r_1748_, v_shortName_1746_, v_currNamespace_1747_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5(lean_object* v_modifiers_1750_, lean_object* v_toApplicative_1751_, lean_object* v_inst_1752_, lean_object* v_inst_1753_, lean_object* v_toBind_1754_, lean_object* v_inst_1755_, lean_object* v_inst_1756_, lean_object* v_inst_1757_, uint8_t v_isRootName_1758_, lean_object* v_shortName_1759_, lean_object* v_currNamespace_1760_, lean_object* v_name_1761_, lean_object* v___x_1762_, lean_object* v_imported_1763_, lean_object* v_ctx_1764_, lean_object* v_scopes_1765_, lean_object* v_____r_1766_){
_start:
{
lean_object* v___y_1768_; 
if (v_isRootName_1758_ == 0)
{
lean_object* v___x_1787_; 
lean_dec(v_scopes_1765_);
lean_dec(v_ctx_1764_);
lean_dec(v_imported_1763_);
lean_inc(v_shortName_1759_);
lean_inc(v_currNamespace_1760_);
v___x_1787_ = l_Lean_Name_append(v_currNamespace_1760_, v_shortName_1759_);
v___y_1768_ = v___x_1787_;
goto v___jp_1767_;
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1788_ = lean_box(0);
lean_inc(v_name_1761_);
v___x_1789_ = l_Lean_Name_replacePrefix(v_name_1761_, v___x_1762_, v___x_1788_);
v___x_1790_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v_imported_1763_);
lean_ctor_set(v___x_1790_, 2, v_ctx_1764_);
lean_ctor_set(v___x_1790_, 3, v_scopes_1765_);
v___x_1791_ = l_Lean_MacroScopesView_review(v___x_1790_);
v___y_1768_ = v___x_1791_;
goto v___jp_1767_;
}
v___jp_1767_:
{
lean_object* v___f_1769_; 
lean_inc(v___y_1768_);
lean_inc_ref(v_inst_1757_);
lean_inc(v_inst_1756_);
lean_inc_ref(v_inst_1755_);
lean_inc(v_toBind_1754_);
lean_inc_ref(v_inst_1753_);
lean_inc_ref(v_inst_1752_);
lean_inc_ref(v_toApplicative_1751_);
lean_inc_ref(v_modifiers_1750_);
v___f_1769_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__3), 12, 9);
lean_closure_set(v___f_1769_, 0, v_modifiers_1750_);
lean_closure_set(v___f_1769_, 1, v_toApplicative_1751_);
lean_closure_set(v___f_1769_, 2, v_inst_1752_);
lean_closure_set(v___f_1769_, 3, v_inst_1753_);
lean_closure_set(v___f_1769_, 4, v_toBind_1754_);
lean_closure_set(v___f_1769_, 5, v_inst_1755_);
lean_closure_set(v___f_1769_, 6, v_inst_1756_);
lean_closure_set(v___f_1769_, 7, v_inst_1757_);
lean_closure_set(v___f_1769_, 8, v___y_1768_);
if (v_isRootName_1758_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec_ref(v___f_1769_);
lean_dec(v_name_1761_);
v___x_1770_ = lean_box(0);
v___x_1771_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1750_, v_toApplicative_1751_, v_inst_1752_, v_inst_1753_, v_toBind_1754_, v_inst_1755_, v_inst_1756_, v_inst_1757_, v___y_1768_, v___x_1770_, v_shortName_1759_, v_currNamespace_1760_);
return v___x_1771_;
}
else
{
if (lean_obj_tag(v_name_1761_) == 1)
{
lean_object* v_pre_1772_; lean_object* v_str_1773_; lean_object* v___x_1774_; lean_object* v_shortName_1775_; lean_object* v_currNamespace_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_dec_ref(v___f_1769_);
lean_dec(v_currNamespace_1760_);
lean_dec(v_shortName_1759_);
v_pre_1772_ = lean_ctor_get(v_name_1761_, 0);
lean_inc(v_pre_1772_);
v_str_1773_ = lean_ctor_get(v_name_1761_, 1);
lean_inc_ref(v_str_1773_);
lean_dec_ref_known(v_name_1761_, 2);
v___x_1774_ = lean_box(0);
v_shortName_1775_ = l_Lean_Name_str___override(v___x_1774_, v_str_1773_);
v_currNamespace_1776_ = l_Lean_Name_replacePrefix(v_pre_1772_, v___x_1762_, v___x_1774_);
v___x_1777_ = lean_box(0);
v___x_1778_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1750_, v_toApplicative_1751_, v_inst_1752_, v_inst_1753_, v_toBind_1754_, v_inst_1755_, v_inst_1756_, v_inst_1757_, v___y_1768_, v___x_1777_, v_shortName_1775_, v_currNamespace_1776_);
return v___x_1778_;
}
else
{
lean_object* v___f_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_dec(v___y_1768_);
lean_dec_ref(v_inst_1757_);
lean_dec(v_inst_1756_);
lean_dec_ref(v_inst_1755_);
lean_dec_ref(v_toApplicative_1751_);
lean_dec_ref(v_modifiers_1750_);
v___f_1779_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__4), 4, 3);
lean_closure_set(v___f_1779_, 0, v___f_1769_);
lean_closure_set(v___f_1779_, 1, v_shortName_1759_);
lean_closure_set(v___f_1779_, 2, v_currNamespace_1760_);
v___x_1780_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1781_ = l_Lean_MessageData_ofName(v_name_1761_);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = l_Lean_throwError___redArg(v_inst_1752_, v_inst_1753_, v___x_1784_);
v___x_1786_ = lean_apply_4(v_toBind_1754_, lean_box(0), lean_box(0), v___x_1785_, v___f_1779_);
return v___x_1786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_modifiers_1792_ = _args[0];
lean_object* v_toApplicative_1793_ = _args[1];
lean_object* v_inst_1794_ = _args[2];
lean_object* v_inst_1795_ = _args[3];
lean_object* v_toBind_1796_ = _args[4];
lean_object* v_inst_1797_ = _args[5];
lean_object* v_inst_1798_ = _args[6];
lean_object* v_inst_1799_ = _args[7];
lean_object* v_isRootName_1800_ = _args[8];
lean_object* v_shortName_1801_ = _args[9];
lean_object* v_currNamespace_1802_ = _args[10];
lean_object* v_name_1803_ = _args[11];
lean_object* v___x_1804_ = _args[12];
lean_object* v_imported_1805_ = _args[13];
lean_object* v_ctx_1806_ = _args[14];
lean_object* v_scopes_1807_ = _args[15];
lean_object* v_____r_1808_ = _args[16];
_start:
{
uint8_t v_isRootName_boxed_1809_; lean_object* v_res_1810_; 
v_isRootName_boxed_1809_ = lean_unbox(v_isRootName_1800_);
v_res_1810_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1792_, v_toApplicative_1793_, v_inst_1794_, v_inst_1795_, v_toBind_1796_, v_inst_1797_, v_inst_1798_, v_inst_1799_, v_isRootName_boxed_1809_, v_shortName_1801_, v_currNamespace_1802_, v_name_1803_, v___x_1804_, v_imported_1805_, v_ctx_1806_, v_scopes_1807_, v_____r_1808_);
lean_dec(v___x_1804_);
return v_res_1810_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___closed__3(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__2));
v___x_1816_ = l_Lean_stringToMessageData(v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg(lean_object* v_inst_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_inst_1821_, lean_object* v_currNamespace_1822_, lean_object* v_modifiers_1823_, lean_object* v_shortName_1824_){
_start:
{
lean_object* v_view_1825_; lean_object* v_name_1826_; lean_object* v_imported_1827_; lean_object* v_ctx_1828_; lean_object* v_scopes_1829_; lean_object* v_toApplicative_1830_; lean_object* v_toBind_1831_; lean_object* v___x_1832_; uint8_t v_isRootName_1833_; lean_object* v___x_1834_; lean_object* v___f_1835_; uint8_t v___x_1836_; 
lean_inc_n(v_shortName_1824_, 2);
v_view_1825_ = l_Lean_extractMacroScopes(v_shortName_1824_);
v_name_1826_ = lean_ctor_get(v_view_1825_, 0);
lean_inc_n(v_name_1826_, 2);
v_imported_1827_ = lean_ctor_get(v_view_1825_, 1);
lean_inc_n(v_imported_1827_, 2);
v_ctx_1828_ = lean_ctor_get(v_view_1825_, 2);
lean_inc_n(v_ctx_1828_, 2);
v_scopes_1829_ = lean_ctor_get(v_view_1825_, 3);
lean_inc_n(v_scopes_1829_, 2);
lean_dec_ref(v_view_1825_);
v_toApplicative_1830_ = lean_ctor_get(v_inst_1817_, 0);
v_toBind_1831_ = lean_ctor_get(v_inst_1817_, 1);
lean_inc_n(v_toBind_1831_, 2);
v___x_1832_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_1833_ = l_Lean_Name_isPrefixOf(v___x_1832_, v_name_1826_);
v___x_1834_ = lean_box(v_isRootName_1833_);
lean_inc(v_currNamespace_1822_);
lean_inc_ref(v_inst_1821_);
lean_inc(v_inst_1820_);
lean_inc_ref(v_inst_1818_);
lean_inc_ref(v_inst_1819_);
lean_inc_ref(v_inst_1817_);
lean_inc_ref(v_toApplicative_1830_);
lean_inc_ref(v_modifiers_1823_);
v___f_1835_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1835_, 0, v_modifiers_1823_);
lean_closure_set(v___f_1835_, 1, v_toApplicative_1830_);
lean_closure_set(v___f_1835_, 2, v_inst_1817_);
lean_closure_set(v___f_1835_, 3, v_inst_1819_);
lean_closure_set(v___f_1835_, 4, v_toBind_1831_);
lean_closure_set(v___f_1835_, 5, v_inst_1818_);
lean_closure_set(v___f_1835_, 6, v_inst_1820_);
lean_closure_set(v___f_1835_, 7, v_inst_1821_);
lean_closure_set(v___f_1835_, 8, v___x_1834_);
lean_closure_set(v___f_1835_, 9, v_shortName_1824_);
lean_closure_set(v___f_1835_, 10, v_currNamespace_1822_);
lean_closure_set(v___f_1835_, 11, v_name_1826_);
lean_closure_set(v___f_1835_, 12, v___x_1832_);
lean_closure_set(v___f_1835_, 13, v_imported_1827_);
lean_closure_set(v___f_1835_, 14, v_ctx_1828_);
lean_closure_set(v___f_1835_, 15, v_scopes_1829_);
v___x_1836_ = lean_name_eq(v_name_1826_, v___x_1832_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_inc_ref(v_toApplicative_1830_);
lean_dec_ref(v___f_1835_);
v___x_1837_ = lean_box(0);
v___x_1838_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1823_, v_toApplicative_1830_, v_inst_1817_, v_inst_1819_, v_toBind_1831_, v_inst_1818_, v_inst_1820_, v_inst_1821_, v_isRootName_1833_, v_shortName_1824_, v_currNamespace_1822_, v_name_1826_, v___x_1832_, v_imported_1827_, v_ctx_1828_, v_scopes_1829_, v___x_1837_);
return v___x_1838_;
}
else
{
lean_object* v___f_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_dec(v_scopes_1829_);
lean_dec(v_ctx_1828_);
lean_dec(v_imported_1827_);
lean_dec(v_name_1826_);
lean_dec(v_shortName_1824_);
lean_dec_ref(v_modifiers_1823_);
lean_dec(v_currNamespace_1822_);
lean_dec_ref(v_inst_1821_);
lean_dec(v_inst_1820_);
lean_dec_ref(v_inst_1818_);
v___f_1839_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1839_, 0, v___f_1835_);
v___x_1840_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_1841_ = l_Lean_throwError___redArg(v_inst_1817_, v_inst_1819_, v___x_1840_);
v___x_1842_ = lean_apply_4(v_toBind_1831_, lean_box(0), lean_box(0), v___x_1841_, v___f_1839_);
return v___x_1842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName(lean_object* v_m_1843_, lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_inst_1847_, lean_object* v_inst_1848_, lean_object* v_currNamespace_1849_, lean_object* v_modifiers_1850_, lean_object* v_shortName_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_Elab_mkDeclName___redArg(v_inst_1844_, v_inst_1845_, v_inst_1846_, v_inst_1847_, v_inst_1848_, v_currNamespace_1849_, v_modifiers_1850_, v_shortName_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore(lean_object* v_declId_1862_){
_start:
{
uint8_t v___x_1863_; 
v___x_1863_ = l_Lean_Syntax_isIdent(v_declId_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v_id_1866_; lean_object* v___x_1867_; lean_object* v_optUnivDeclStx_1868_; lean_object* v___x_1869_; 
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = l_Lean_Syntax_getArg(v_declId_1862_, v___x_1864_);
v_id_1866_ = l_Lean_Syntax_getId(v___x_1865_);
lean_dec(v___x_1865_);
v___x_1867_ = lean_unsigned_to_nat(1u);
v_optUnivDeclStx_1868_ = l_Lean_Syntax_getArg(v_declId_1862_, v___x_1867_);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v_id_1866_);
lean_ctor_set(v___x_1869_, 1, v_optUnivDeclStx_1868_);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1870_ = l_Lean_Syntax_getId(v_declId_1862_);
v___x_1871_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__3));
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore___boxed(lean_object* v_declId_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_Elab_expandDeclIdCore(v_declId_1873_);
lean_dec(v_declId_1873_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(lean_object* v_msgData_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; lean_object* v_env_1882_; lean_object* v___x_1883_; lean_object* v_mctx_1884_; lean_object* v_lctx_1885_; lean_object* v_options_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1881_ = lean_st_ref_get(v___y_1879_);
v_env_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc_ref(v_env_1882_);
lean_dec(v___x_1881_);
v___x_1883_ = lean_st_ref_get(v___y_1877_);
v_mctx_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc_ref(v_mctx_1884_);
lean_dec(v___x_1883_);
v_lctx_1885_ = lean_ctor_get(v___y_1876_, 2);
v_options_1886_ = lean_ctor_get(v___y_1878_, 2);
lean_inc_ref(v_options_1886_);
lean_inc_ref(v_lctx_1885_);
v___x_1887_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1887_, 0, v_env_1882_);
lean_ctor_set(v___x_1887_, 1, v_mctx_1884_);
lean_ctor_set(v___x_1887_, 2, v_lctx_1885_);
lean_ctor_set(v___x_1887_, 3, v_options_1886_);
v___x_1888_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v_msgData_1875_);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msgData_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
return v_res_1896_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(lean_object* v_opts_1897_, lean_object* v_opt_1898_){
_start:
{
lean_object* v_name_1899_; lean_object* v_defValue_1900_; lean_object* v_map_1901_; lean_object* v___x_1902_; 
v_name_1899_ = lean_ctor_get(v_opt_1898_, 0);
v_defValue_1900_ = lean_ctor_get(v_opt_1898_, 1);
v_map_1901_ = lean_ctor_get(v_opts_1897_, 0);
v___x_1902_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1901_, v_name_1899_);
if (lean_obj_tag(v___x_1902_) == 0)
{
uint8_t v___x_1903_; 
v___x_1903_ = lean_unbox(v_defValue_1900_);
return v___x_1903_;
}
else
{
lean_object* v_val_1904_; 
v_val_1904_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_val_1904_);
lean_dec_ref_known(v___x_1902_, 1);
if (lean_obj_tag(v_val_1904_) == 1)
{
uint8_t v_v_1905_; 
v_v_1905_ = lean_ctor_get_uint8(v_val_1904_, 0);
lean_dec_ref_known(v_val_1904_, 0);
return v_v_1905_;
}
else
{
uint8_t v___x_1906_; 
lean_dec(v_val_1904_);
v___x_1906_ = lean_unbox(v_defValue_1900_);
return v___x_1906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_opts_1907_, lean_object* v_opt_1908_){
_start:
{
uint8_t v_res_1909_; lean_object* v_r_1910_; 
v_res_1909_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_opts_1907_, v_opt_1908_);
lean_dec_ref(v_opt_1908_);
lean_dec_ref(v_opts_1907_);
v_r_1910_ = lean_box(v_res_1909_);
return v_r_1910_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0(void){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = lean_box(1);
v___x_1912_ = l_Lean_MessageData_ofFormat(v___x_1911_);
return v___x_1912_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2));
v___x_1917_ = l_Lean_MessageData_ofFormat(v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(lean_object* v_x_1918_, lean_object* v_x_1919_){
_start:
{
if (lean_obj_tag(v_x_1919_) == 0)
{
return v_x_1918_;
}
else
{
lean_object* v_head_1920_; lean_object* v_tail_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1943_; 
v_head_1920_ = lean_ctor_get(v_x_1919_, 0);
v_tail_1921_ = lean_ctor_get(v_x_1919_, 1);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_x_1919_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1923_ = v_x_1919_;
v_isShared_1924_ = v_isSharedCheck_1943_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_tail_1921_);
lean_inc(v_head_1920_);
lean_dec(v_x_1919_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1943_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v_before_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1941_; 
v_before_1925_ = lean_ctor_get(v_head_1920_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_head_1920_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v_head_1920_, 1);
lean_dec(v_unused_1942_);
v___x_1927_ = v_head_1920_;
v_isShared_1928_ = v_isSharedCheck_1941_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_before_1925_);
lean_dec(v_head_1920_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1941_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1929_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_1928_ == 0)
{
lean_ctor_set_tag(v___x_1927_, 7);
lean_ctor_set(v___x_1927_, 1, v___x_1929_);
lean_ctor_set(v___x_1927_, 0, v_x_1918_);
v___x_1931_ = v___x_1927_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_x_1918_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3);
if (v_isShared_1924_ == 0)
{
lean_ctor_set_tag(v___x_1923_, 7);
lean_ctor_set(v___x_1923_, 1, v___x_1932_);
lean_ctor_set(v___x_1923_, 0, v___x_1931_);
v___x_1934_ = v___x_1923_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = l_Lean_MessageData_ofSyntax(v_before_1925_);
v___x_1936_ = l_Lean_indentD(v___x_1935_);
v___x_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1934_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v_x_1918_ = v___x_1937_;
v_x_1919_ = v_tail_1921_;
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
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1));
v___x_1948_ = l_Lean_MessageData_ofFormat(v___x_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_1949_, lean_object* v_macroStack_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_options_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; uint8_t v___x_1956_; 
v_options_1953_ = lean_ctor_get(v___y_1951_, 2);
v___x_1954_ = l_Lean_Elab_pp_macroStack;
v___x_1955_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_options_1953_, v___x_1954_);
v___x_1956_ = lean_bool_not(v___x_1955_);
if (v___x_1956_ == 0)
{
if (lean_obj_tag(v_macroStack_1950_) == 0)
{
lean_object* v___x_1957_; 
v___x_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1957_, 0, v_msgData_1949_);
return v___x_1957_;
}
else
{
lean_object* v_head_1958_; lean_object* v_after_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1974_; 
v_head_1958_ = lean_ctor_get(v_macroStack_1950_, 0);
lean_inc(v_head_1958_);
v_after_1959_ = lean_ctor_get(v_head_1958_, 1);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_head_1958_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v_head_1958_, 0);
lean_dec(v_unused_1975_);
v___x_1961_ = v_head_1958_;
v_isShared_1962_ = v_isSharedCheck_1974_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_after_1959_);
lean_dec(v_head_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1974_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1963_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_1962_ == 0)
{
lean_ctor_set_tag(v___x_1961_, 7);
lean_ctor_set(v___x_1961_, 1, v___x_1963_);
lean_ctor_set(v___x_1961_, 0, v_msgData_1949_);
v___x_1965_ = v___x_1961_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_msgData_1949_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v_msgData_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1966_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_1967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1965_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = l_Lean_MessageData_ofSyntax(v_after_1959_);
v___x_1969_ = l_Lean_indentD(v___x_1968_);
v_msgData_1970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1970_, 0, v___x_1967_);
lean_ctor_set(v_msgData_1970_, 1, v___x_1969_);
v___x_1971_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(v_msgData_1970_, v_macroStack_1950_);
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
return v___x_1972_;
}
}
}
}
else
{
lean_object* v___x_1976_; 
lean_dec(v_macroStack_1950_);
v___x_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1976_, 0, v_msgData_1949_);
return v___x_1976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_1977_, lean_object* v_macroStack_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_1977_, v_macroStack_1978_, v___y_1979_);
lean_dec_ref(v___y_1979_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(lean_object* v_msg_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_ref_1990_; lean_object* v___x_1991_; lean_object* v_a_1992_; lean_object* v_macroStack_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2004_; 
v_ref_1990_ = lean_ctor_get(v___y_1987_, 5);
v___x_1991_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msg_1982_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref(v___x_1991_);
v_macroStack_1993_ = lean_ctor_get(v___y_1983_, 1);
v___x_1994_ = l_Lean_Elab_getBetterRef(v_ref_1990_, v_macroStack_1993_);
lean_inc(v_macroStack_1993_);
v___x_1995_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_a_1992_, v_macroStack_1993_, v___y_1987_);
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1994_);
lean_ctor_set(v___x_2000_, 1, v_a_1996_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set_tag(v___x_1998_, 1);
lean_ctor_set(v___x_1998_, 0, v___x_2000_);
v___x_2002_ = v___x_1998_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg___boxed(lean_object* v_msg_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(lean_object* v_env_2014_, lean_object* v_declName_2015_, lean_object* v___f_2016_, lean_object* v_addInfo_2017_, lean_object* v_____r_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; uint8_t v___x_2027_; uint8_t v___x_2028_; 
lean_inc(v_declName_2015_);
v___x_2026_ = l_Lean_mkPrivateName(v_env_2014_, v_declName_2015_);
v___x_2027_ = 1;
lean_inc(v___x_2026_);
v___x_2028_ = l_Lean_Environment_contains(v_env_2014_, v___x_2026_, v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
lean_dec(v___x_2026_);
lean_dec_ref(v_addInfo_2017_);
lean_dec(v_declName_2015_);
v___x_2029_ = lean_box(0);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
lean_inc(v___y_2022_);
lean_inc_ref(v___y_2021_);
lean_inc(v___y_2020_);
lean_inc_ref(v___y_2019_);
v___x_2030_ = lean_apply_8(v___f_2016_, v___x_2029_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, lean_box(0));
return v___x_2030_;
}
else
{
lean_object* v___x_2031_; 
lean_dec_ref(v___f_2016_);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
lean_inc(v___y_2022_);
lean_inc_ref(v___y_2021_);
lean_inc(v___y_2020_);
lean_inc_ref(v___y_2019_);
v___x_2031_ = lean_apply_8(v_addInfo_2017_, v___x_2026_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, lean_box(0));
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec_ref_known(v___x_2031_, 1);
v___x_2032_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1);
v___x_2033_ = l_Lean_MessageData_ofConstName(v_declName_2015_, v___x_2027_);
v___x_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2034_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2036_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2037_;
}
else
{
lean_dec(v_declName_2015_);
return v___x_2031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed(lean_object* v_env_2038_, lean_object* v_declName_2039_, lean_object* v___f_2040_, lean_object* v_addInfo_2041_, lean_object* v_____r_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(v_env_2038_, v_declName_2039_, v___f_2040_, v_addInfo_2041_, v_____r_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(lean_object* v___f_2051_, lean_object* v_declName_2052_, uint8_t v___x_2053_, lean_object* v_env_2054_, lean_object* v_____do__lift_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
uint8_t v___y_2064_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
lean_inc(v_declName_2052_);
v___x_2073_ = l_Lean_privateToUserName(v_declName_2052_);
lean_inc_ref(v_env_2054_);
v___x_2074_ = lean_is_reserved_name(v_env_2054_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
lean_inc(v_declName_2052_);
v___x_2075_ = l_Lean_mkPrivateName(v_____do__lift_2055_, v_declName_2052_);
v___x_2076_ = lean_is_reserved_name(v_env_2054_, v___x_2075_);
v___y_2064_ = v___x_2076_;
goto v___jp_2063_;
}
else
{
lean_dec_ref(v_env_2054_);
v___y_2064_ = v___x_2074_;
goto v___jp_2063_;
}
v___jp_2063_:
{
if (v___y_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec(v_declName_2052_);
v___x_2065_ = lean_box(0);
lean_inc(v___y_2061_);
lean_inc_ref(v___y_2060_);
lean_inc(v___y_2059_);
lean_inc_ref(v___y_2058_);
lean_inc(v___y_2057_);
lean_inc_ref(v___y_2056_);
v___x_2066_ = lean_apply_8(v___f_2051_, v___x_2065_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, lean_box(0));
return v___x_2066_;
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_dec_ref(v___f_2051_);
v___x_2067_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2068_ = l_Lean_MessageData_ofConstName(v_declName_2052_, v___x_2053_);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2071_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
return v___x_2072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed(lean_object* v___f_2077_, lean_object* v_declName_2078_, lean_object* v___x_2079_, lean_object* v_env_2080_, lean_object* v_____do__lift_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
uint8_t v___x_17544__boxed_2089_; lean_object* v_res_2090_; 
v___x_17544__boxed_2089_ = lean_unbox(v___x_2079_);
v_res_2090_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(v___f_2077_, v_declName_2078_, v___x_17544__boxed_2089_, v_env_2080_, v_____do__lift_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec_ref(v_____do__lift_2081_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(lean_object* v_t_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2094_; lean_object* v_infoState_2095_; uint8_t v_enabled_2096_; 
v___x_2094_ = lean_st_ref_get(v___y_2092_);
v_infoState_2095_ = lean_ctor_get(v___x_2094_, 7);
lean_inc_ref(v_infoState_2095_);
lean_dec(v___x_2094_);
v_enabled_2096_ = lean_ctor_get_uint8(v_infoState_2095_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2095_);
if (v_enabled_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_dec_ref(v_t_2091_);
v___x_2097_ = lean_box(0);
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
return v___x_2098_;
}
else
{
lean_object* v___x_2099_; lean_object* v_infoState_2100_; lean_object* v_env_2101_; lean_object* v_nextMacroScope_2102_; lean_object* v_ngen_2103_; lean_object* v_auxDeclNGen_2104_; lean_object* v_traceState_2105_; lean_object* v_cache_2106_; lean_object* v_messages_2107_; lean_object* v_snapshotTasks_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2130_; 
v___x_2099_ = lean_st_ref_take(v___y_2092_);
v_infoState_2100_ = lean_ctor_get(v___x_2099_, 7);
v_env_2101_ = lean_ctor_get(v___x_2099_, 0);
v_nextMacroScope_2102_ = lean_ctor_get(v___x_2099_, 1);
v_ngen_2103_ = lean_ctor_get(v___x_2099_, 2);
v_auxDeclNGen_2104_ = lean_ctor_get(v___x_2099_, 3);
v_traceState_2105_ = lean_ctor_get(v___x_2099_, 4);
v_cache_2106_ = lean_ctor_get(v___x_2099_, 5);
v_messages_2107_ = lean_ctor_get(v___x_2099_, 6);
v_snapshotTasks_2108_ = lean_ctor_get(v___x_2099_, 8);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2110_ = v___x_2099_;
v_isShared_2111_ = v_isSharedCheck_2130_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_snapshotTasks_2108_);
lean_inc(v_infoState_2100_);
lean_inc(v_messages_2107_);
lean_inc(v_cache_2106_);
lean_inc(v_traceState_2105_);
lean_inc(v_auxDeclNGen_2104_);
lean_inc(v_ngen_2103_);
lean_inc(v_nextMacroScope_2102_);
lean_inc(v_env_2101_);
lean_dec(v___x_2099_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2130_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
uint8_t v_enabled_2112_; lean_object* v_assignment_2113_; lean_object* v_lazyAssignment_2114_; lean_object* v_trees_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2129_; 
v_enabled_2112_ = lean_ctor_get_uint8(v_infoState_2100_, sizeof(void*)*3);
v_assignment_2113_ = lean_ctor_get(v_infoState_2100_, 0);
v_lazyAssignment_2114_ = lean_ctor_get(v_infoState_2100_, 1);
v_trees_2115_ = lean_ctor_get(v_infoState_2100_, 2);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_infoState_2100_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2117_ = v_infoState_2100_;
v_isShared_2118_ = v_isSharedCheck_2129_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_trees_2115_);
lean_inc(v_lazyAssignment_2114_);
lean_inc(v_assignment_2113_);
lean_dec(v_infoState_2100_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2129_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2119_ = l_Lean_PersistentArray_push___redArg(v_trees_2115_, v_t_2091_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 2, v___x_2119_);
v___x_2121_ = v___x_2117_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_assignment_2113_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_lazyAssignment_2114_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v___x_2119_);
lean_ctor_set_uint8(v_reuseFailAlloc_2128_, sizeof(void*)*3, v_enabled_2112_);
v___x_2121_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2123_; 
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 7, v___x_2121_);
v___x_2123_ = v___x_2110_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_env_2101_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_nextMacroScope_2102_);
lean_ctor_set(v_reuseFailAlloc_2127_, 2, v_ngen_2103_);
lean_ctor_set(v_reuseFailAlloc_2127_, 3, v_auxDeclNGen_2104_);
lean_ctor_set(v_reuseFailAlloc_2127_, 4, v_traceState_2105_);
lean_ctor_set(v_reuseFailAlloc_2127_, 5, v_cache_2106_);
lean_ctor_set(v_reuseFailAlloc_2127_, 6, v_messages_2107_);
lean_ctor_set(v_reuseFailAlloc_2127_, 7, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2127_, 8, v_snapshotTasks_2108_);
v___x_2123_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = lean_st_ref_set(v___y_2092_, v___x_2123_);
v___x_2125_ = lean_box(0);
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
return v___x_2126_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg___boxed(lean_object* v_t_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_2131_, v___y_2132_);
lean_dec(v___y_2132_);
return v_res_2134_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = lean_unsigned_to_nat(32u);
v___x_2136_ = lean_mk_empty_array_with_capacity(v___x_2135_);
v___x_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
return v___x_2137_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1(void){
_start:
{
size_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2138_ = ((size_t)5ULL);
v___x_2139_ = lean_unsigned_to_nat(0u);
v___x_2140_ = lean_unsigned_to_nat(32u);
v___x_2141_ = lean_mk_empty_array_with_capacity(v___x_2140_);
v___x_2142_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0);
v___x_2143_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v___x_2141_);
lean_ctor_set(v___x_2143_, 2, v___x_2139_);
lean_ctor_set(v___x_2143_, 3, v___x_2139_);
lean_ctor_set_usize(v___x_2143_, 4, v___x_2138_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(lean_object* v_t_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; lean_object* v_infoState_2153_; uint8_t v_enabled_2154_; 
v___x_2152_ = lean_st_ref_get(v___y_2150_);
v_infoState_2153_ = lean_ctor_get(v___x_2152_, 7);
lean_inc_ref(v_infoState_2153_);
lean_dec(v___x_2152_);
v_enabled_2154_ = lean_ctor_get_uint8(v_infoState_2153_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2153_);
if (v_enabled_2154_ == 0)
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
lean_dec_ref(v_t_2144_);
v___x_2155_ = lean_box(0);
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
return v___x_2156_;
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1);
v___x_2158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2158_, 0, v_t_2144_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v___x_2158_, v___y_2150_);
return v___x_2159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___boxed(lean_object* v_t_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v_t_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
if (lean_obj_tag(v_a_2169_) == 0)
{
lean_object* v___x_2171_; 
v___x_2171_ = l_List_reverse___redArg(v_a_2170_);
return v___x_2171_;
}
else
{
lean_object* v_head_2172_; lean_object* v_tail_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2182_; 
v_head_2172_ = lean_ctor_get(v_a_2169_, 0);
v_tail_2173_ = lean_ctor_get(v_a_2169_, 1);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_a_2169_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2175_ = v_a_2169_;
v_isShared_2176_ = v_isSharedCheck_2182_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_tail_2173_);
lean_inc(v_head_2172_);
lean_dec(v_a_2169_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2182_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2177_ = l_Lean_mkLevelParam(v_head_2172_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 1, v_a_2170_);
lean_ctor_set(v___x_2175_, 0, v___x_2177_);
v___x_2179_ = v___x_2175_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2177_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_a_2170_);
v___x_2179_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
v_a_2169_ = v_tail_2173_;
v_a_2170_ = v___x_2179_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0(void){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
return v___x_2185_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
v___x_2187_ = lean_unsigned_to_nat(0u);
v___x_2188_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
lean_ctor_set(v___x_2188_, 2, v___x_2187_);
lean_ctor_set(v___x_2188_, 3, v___x_2187_);
lean_ctor_set(v___x_2188_, 4, v___x_2186_);
lean_ctor_set(v___x_2188_, 5, v___x_2186_);
lean_ctor_set(v___x_2188_, 6, v___x_2186_);
lean_ctor_set(v___x_2188_, 7, v___x_2186_);
lean_ctor_set(v___x_2188_, 8, v___x_2186_);
lean_ctor_set(v___x_2188_, 9, v___x_2186_);
return v___x_2188_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2189_ = lean_box(1);
v___x_2190_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3);
v___x_2191_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
v___x_2192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set(v___x_2192_, 1, v___x_2190_);
lean_ctor_set(v___x_2192_, 2, v___x_2189_);
return v___x_2192_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4));
v___x_2195_ = l_Lean_stringToMessageData(v___x_2194_);
return v___x_2195_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6));
v___x_2198_ = l_Lean_stringToMessageData(v___x_2197_);
return v___x_2198_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8));
v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10));
v___x_2204_ = l_Lean_stringToMessageData(v___x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12));
v___x_2207_ = l_Lean_stringToMessageData(v___x_2206_);
return v___x_2207_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14));
v___x_2210_ = l_Lean_stringToMessageData(v___x_2209_);
return v___x_2210_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16));
v___x_2213_ = l_Lean_stringToMessageData(v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(lean_object* v_msg_2214_, lean_object* v_declHint_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v___x_2218_; lean_object* v_env_2219_; uint8_t v___y_2221_; uint8_t v___x_2277_; uint8_t v___x_2278_; 
v___x_2218_ = lean_st_ref_get(v___y_2216_);
v_env_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc_ref(v_env_2219_);
lean_dec(v___x_2218_);
v___x_2277_ = l_Lean_Name_isAnonymous(v_declHint_2215_);
v___x_2278_ = lean_bool_not(v___x_2277_);
if (v___x_2278_ == 0)
{
v___y_2221_ = v___x_2278_;
goto v___jp_2220_;
}
else
{
uint8_t v_isExporting_2279_; 
v_isExporting_2279_ = lean_ctor_get_uint8(v_env_2219_, sizeof(void*)*8);
v___y_2221_ = v_isExporting_2279_;
goto v___jp_2220_;
}
v___jp_2220_:
{
if (v___y_2221_ == 0)
{
lean_object* v___x_2222_; 
lean_dec_ref(v_env_2219_);
lean_dec(v_declHint_2215_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_msg_2214_);
return v___x_2222_;
}
else
{
uint8_t v___x_2223_; lean_object* v___x_2224_; uint8_t v___x_2225_; 
v___x_2223_ = 0;
lean_inc_ref(v_env_2219_);
v___x_2224_ = l_Lean_Environment_setExporting(v_env_2219_, v___x_2223_);
lean_inc(v_declHint_2215_);
lean_inc_ref(v___x_2224_);
v___x_2225_ = l_Lean_Environment_contains(v___x_2224_, v_declHint_2215_, v___y_2221_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
lean_dec_ref(v___x_2224_);
lean_dec_ref(v_env_2219_);
lean_dec(v_declHint_2215_);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_msg_2214_);
return v___x_2226_;
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v_c_2232_; lean_object* v___x_2233_; 
v___x_2227_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2);
v___x_2228_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3);
v___x_2229_ = l_Lean_Options_empty;
v___x_2230_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2224_);
lean_ctor_set(v___x_2230_, 1, v___x_2227_);
lean_ctor_set(v___x_2230_, 2, v___x_2228_);
lean_ctor_set(v___x_2230_, 3, v___x_2229_);
lean_inc(v_declHint_2215_);
v___x_2231_ = l_Lean_MessageData_ofConstName(v_declHint_2215_, v___x_2223_);
v_c_2232_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2232_, 0, v___x_2230_);
lean_ctor_set(v_c_2232_, 1, v___x_2231_);
v___x_2233_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2219_, v_declHint_2215_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec_ref(v_env_2219_);
lean_dec(v_declHint_2215_);
v___x_2234_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5);
v___x_2235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
lean_ctor_set(v___x_2235_, 1, v_c_2232_);
v___x_2236_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7);
v___x_2237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = l_Lean_MessageData_note(v___x_2237_);
v___x_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2239_, 0, v_msg_2214_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
else
{
lean_object* v_val_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2276_; 
v_val_2241_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2243_ = v___x_2233_;
v_isShared_2244_ = v_isSharedCheck_2276_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_val_2241_);
lean_dec(v___x_2233_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2276_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v_mod_2248_; uint8_t v___x_2249_; 
v___x_2245_ = lean_box(0);
v___x_2246_ = l_Lean_Environment_header(v_env_2219_);
lean_dec_ref(v_env_2219_);
v___x_2247_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2246_);
v_mod_2248_ = lean_array_get(v___x_2245_, v___x_2247_, v_val_2241_);
lean_dec(v_val_2241_);
lean_dec_ref(v___x_2247_);
v___x_2249_ = l_Lean_isPrivateName(v_declHint_2215_);
lean_dec(v_declHint_2215_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9);
v___x_2251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
lean_ctor_set(v___x_2251_, 1, v_c_2232_);
v___x_2252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11);
v___x_2253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2251_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = l_Lean_MessageData_ofName(v_mod_2248_);
v___x_2255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13);
v___x_2257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2255_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = l_Lean_MessageData_note(v___x_2257_);
v___x_2259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2259_, 0, v_msg_2214_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set_tag(v___x_2243_, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2259_);
v___x_2261_ = v___x_2243_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2263_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5);
v___x_2264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set(v___x_2264_, 1, v_c_2232_);
v___x_2265_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15);
v___x_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = l_Lean_MessageData_ofName(v_mod_2248_);
v___x_2268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2266_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v___x_2269_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17);
v___x_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = l_Lean_MessageData_note(v___x_2270_);
v___x_2272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2272_, 0, v_msg_2214_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set_tag(v___x_2243_, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2272_);
v___x_2274_ = v___x_2243_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___boxed(lean_object* v_msg_2280_, lean_object* v_declHint_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2280_, v_declHint_2281_, v___y_2282_);
lean_dec(v___y_2282_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(lean_object* v_msg_2285_, lean_object* v_declHint_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2304_; 
v___x_2294_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2285_, v_declHint_2286_, v___y_2292_);
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2304_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2304_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2299_ = l_Lean_unknownIdentifierMessageTag;
v___x_2300_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v_a_2295_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2300_);
v___x_2302_ = v___x_2297_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23___boxed(lean_object* v_msg_2305_, lean_object* v_declHint_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2305_, v_declHint_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(lean_object* v_ref_2315_, lean_object* v_msg_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_fileName_2324_; lean_object* v_fileMap_2325_; lean_object* v_options_2326_; lean_object* v_currRecDepth_2327_; lean_object* v_maxRecDepth_2328_; lean_object* v_ref_2329_; lean_object* v_currNamespace_2330_; lean_object* v_openDecls_2331_; lean_object* v_initHeartbeats_2332_; lean_object* v_maxHeartbeats_2333_; lean_object* v_quotContext_2334_; lean_object* v_currMacroScope_2335_; uint8_t v_diag_2336_; lean_object* v_cancelTk_x3f_2337_; uint8_t v_suppressElabErrors_2338_; lean_object* v_inheritedTraceOptions_2339_; lean_object* v_ref_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_fileName_2324_ = lean_ctor_get(v___y_2321_, 0);
v_fileMap_2325_ = lean_ctor_get(v___y_2321_, 1);
v_options_2326_ = lean_ctor_get(v___y_2321_, 2);
v_currRecDepth_2327_ = lean_ctor_get(v___y_2321_, 3);
v_maxRecDepth_2328_ = lean_ctor_get(v___y_2321_, 4);
v_ref_2329_ = lean_ctor_get(v___y_2321_, 5);
v_currNamespace_2330_ = lean_ctor_get(v___y_2321_, 6);
v_openDecls_2331_ = lean_ctor_get(v___y_2321_, 7);
v_initHeartbeats_2332_ = lean_ctor_get(v___y_2321_, 8);
v_maxHeartbeats_2333_ = lean_ctor_get(v___y_2321_, 9);
v_quotContext_2334_ = lean_ctor_get(v___y_2321_, 10);
v_currMacroScope_2335_ = lean_ctor_get(v___y_2321_, 11);
v_diag_2336_ = lean_ctor_get_uint8(v___y_2321_, sizeof(void*)*14);
v_cancelTk_x3f_2337_ = lean_ctor_get(v___y_2321_, 12);
v_suppressElabErrors_2338_ = lean_ctor_get_uint8(v___y_2321_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2339_ = lean_ctor_get(v___y_2321_, 13);
v_ref_2340_ = l_Lean_replaceRef(v_ref_2315_, v_ref_2329_);
lean_inc_ref(v_inheritedTraceOptions_2339_);
lean_inc(v_cancelTk_x3f_2337_);
lean_inc(v_currMacroScope_2335_);
lean_inc(v_quotContext_2334_);
lean_inc(v_maxHeartbeats_2333_);
lean_inc(v_initHeartbeats_2332_);
lean_inc(v_openDecls_2331_);
lean_inc(v_currNamespace_2330_);
lean_inc(v_maxRecDepth_2328_);
lean_inc(v_currRecDepth_2327_);
lean_inc_ref(v_options_2326_);
lean_inc_ref(v_fileMap_2325_);
lean_inc_ref(v_fileName_2324_);
v___x_2341_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2341_, 0, v_fileName_2324_);
lean_ctor_set(v___x_2341_, 1, v_fileMap_2325_);
lean_ctor_set(v___x_2341_, 2, v_options_2326_);
lean_ctor_set(v___x_2341_, 3, v_currRecDepth_2327_);
lean_ctor_set(v___x_2341_, 4, v_maxRecDepth_2328_);
lean_ctor_set(v___x_2341_, 5, v_ref_2340_);
lean_ctor_set(v___x_2341_, 6, v_currNamespace_2330_);
lean_ctor_set(v___x_2341_, 7, v_openDecls_2331_);
lean_ctor_set(v___x_2341_, 8, v_initHeartbeats_2332_);
lean_ctor_set(v___x_2341_, 9, v_maxHeartbeats_2333_);
lean_ctor_set(v___x_2341_, 10, v_quotContext_2334_);
lean_ctor_set(v___x_2341_, 11, v_currMacroScope_2335_);
lean_ctor_set(v___x_2341_, 12, v_cancelTk_x3f_2337_);
lean_ctor_set(v___x_2341_, 13, v_inheritedTraceOptions_2339_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*14, v_diag_2336_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*14 + 1, v_suppressElabErrors_2338_);
v___x_2342_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___x_2341_, v___y_2322_);
lean_dec_ref_known(v___x_2341_, 14);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg___boxed(lean_object* v_ref_2343_, lean_object* v_msg_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2343_, v_msg_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v_ref_2343_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(lean_object* v_ref_2353_, lean_object* v_msg_2354_, lean_object* v_declHint_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___x_2363_; lean_object* v_a_2364_; lean_object* v___x_2365_; 
v___x_2363_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2354_, v_declHint_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref(v___x_2363_);
v___x_2365_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2353_, v_a_2364_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg___boxed(lean_object* v_ref_2366_, lean_object* v_msg_2367_, lean_object* v_declHint_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2366_, v_msg_2367_, v_declHint_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v_ref_2366_);
return v_res_2376_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0));
v___x_2379_ = l_Lean_stringToMessageData(v___x_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(lean_object* v_ref_2380_, lean_object* v_constName_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2389_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1);
v___x_2390_ = 0;
lean_inc(v_constName_2381_);
v___x_2391_ = l_Lean_MessageData_ofConstName(v_constName_2381_, v___x_2390_);
v___x_2392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2389_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2380_, v___x_2394_, v_constName_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___boxed(lean_object* v_ref_2396_, lean_object* v_constName_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2396_, v_constName_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v_ref_2396_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(lean_object* v_constName_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_ref_2414_; lean_object* v___x_2415_; 
v_ref_2414_ = lean_ctor_get(v___y_2411_, 5);
v___x_2415_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2414_, v_constName_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_constName_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(lean_object* v_constName_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; lean_object* v_env_2434_; uint8_t v___x_2435_; lean_object* v___x_2436_; 
v___x_2433_ = lean_st_ref_get(v___y_2431_);
v_env_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc_ref(v_env_2434_);
lean_dec(v___x_2433_);
v___x_2435_ = 0;
lean_inc(v_constName_2425_);
v___x_2436_ = l_Lean_Environment_findConstVal_x3f(v_env_2434_, v_constName_2425_, v___x_2435_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
return v___x_2437_;
}
else
{
lean_object* v_val_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_dec(v_constName_2425_);
v_val_2438_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2436_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_val_2438_);
lean_dec(v___x_2436_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set_tag(v___x_2440_, 0);
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_val_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14___boxed(lean_object* v_constName_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(lean_object* v_constName_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___x_2463_; 
lean_inc(v_constName_2455_);
v___x_2463_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2475_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2475_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2475_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v_levelParams_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; 
v_levelParams_2468_ = lean_ctor_get(v_a_2464_, 1);
lean_inc(v_levelParams_2468_);
lean_dec(v_a_2464_);
v___x_2469_ = lean_box(0);
v___x_2470_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(v_levelParams_2468_, v___x_2469_);
v___x_2471_ = l_Lean_mkConst(v_constName_2455_, v___x_2470_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2471_);
v___x_2473_ = v___x_2466_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec(v_constName_2455_);
v_a_2476_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2463_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2463_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_constName_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_constName_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(uint8_t v___x_2493_, lean_object* v_declName_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_ref_2502_; lean_object* v___x_2503_; 
v_ref_2502_ = lean_ctor_get(v___y_2499_, 5);
v___x_2503_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_declName_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2503_, 1);
v___x_2505_ = lean_box(0);
lean_inc(v_ref_2502_);
v___x_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
lean_ctor_set(v___x_2506_, 1, v_ref_2502_);
v___x_2507_ = lean_unsigned_to_nat(32u);
v___x_2508_ = lean_mk_empty_array_with_capacity(v___x_2507_);
lean_dec_ref(v___x_2508_);
v___x_2509_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4);
v___x_2510_ = lean_box(0);
v___x_2511_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2511_, 0, v___x_2506_);
lean_ctor_set(v___x_2511_, 1, v___x_2509_);
lean_ctor_set(v___x_2511_, 2, v___x_2510_);
lean_ctor_set(v___x_2511_, 3, v_a_2504_);
lean_ctor_set_uint8(v___x_2511_, sizeof(void*)*4, v___x_2493_);
lean_ctor_set_uint8(v___x_2511_, sizeof(void*)*4 + 1, v___x_2493_);
v___x_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
v___x_2513_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v___x_2512_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
return v___x_2513_;
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
v_a_2514_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2503_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2503_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v___x_2522_, lean_object* v_declName_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
uint8_t v___x_18279__boxed_2531_; lean_object* v_res_2532_; 
v___x_18279__boxed_2531_ = lean_unbox(v___x_2522_);
v_res_2532_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(v___x_18279__boxed_2531_, v_declName_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(lean_object* v___f_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; lean_object* v_env_2542_; lean_object* v___x_2543_; 
v___x_2541_ = lean_st_ref_get(v___y_2539_);
v_env_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc_ref(v_env_2542_);
lean_dec(v___x_2541_);
v___x_2543_ = lean_apply_8(v___f_2533_, v_env_2542_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, lean_box(0));
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed(lean_object* v___f_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(v___f_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
return v_res_2552_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2553_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
return v___x_2557_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
v___x_2559_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
lean_ctor_set(v___x_2559_, 2, v___x_2558_);
lean_ctor_set(v___x_2559_, 3, v___x_2558_);
lean_ctor_set(v___x_2559_, 4, v___x_2558_);
lean_ctor_set(v___x_2559_, 5, v___x_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(lean_object* v_env_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; lean_object* v_nextMacroScope_2565_; lean_object* v_ngen_2566_; lean_object* v_auxDeclNGen_2567_; lean_object* v_traceState_2568_; lean_object* v_messages_2569_; lean_object* v_infoState_2570_; lean_object* v_snapshotTasks_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2597_; 
v___x_2564_ = lean_st_ref_take(v___y_2562_);
v_nextMacroScope_2565_ = lean_ctor_get(v___x_2564_, 1);
v_ngen_2566_ = lean_ctor_get(v___x_2564_, 2);
v_auxDeclNGen_2567_ = lean_ctor_get(v___x_2564_, 3);
v_traceState_2568_ = lean_ctor_get(v___x_2564_, 4);
v_messages_2569_ = lean_ctor_get(v___x_2564_, 6);
v_infoState_2570_ = lean_ctor_get(v___x_2564_, 7);
v_snapshotTasks_2571_ = lean_ctor_get(v___x_2564_, 8);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; lean_object* v_unused_2599_; 
v_unused_2598_ = lean_ctor_get(v___x_2564_, 5);
lean_dec(v_unused_2598_);
v_unused_2599_ = lean_ctor_get(v___x_2564_, 0);
lean_dec(v_unused_2599_);
v___x_2573_ = v___x_2564_;
v_isShared_2574_ = v_isSharedCheck_2597_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_snapshotTasks_2571_);
lean_inc(v_infoState_2570_);
lean_inc(v_messages_2569_);
lean_inc(v_traceState_2568_);
lean_inc(v_auxDeclNGen_2567_);
lean_inc(v_ngen_2566_);
lean_inc(v_nextMacroScope_2565_);
lean_dec(v___x_2564_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2597_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 5, v___x_2575_);
lean_ctor_set(v___x_2573_, 0, v_env_2560_);
v___x_2577_ = v___x_2573_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_env_2560_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_nextMacroScope_2565_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_ngen_2566_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v_auxDeclNGen_2567_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v_traceState_2568_);
lean_ctor_set(v_reuseFailAlloc_2596_, 5, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2596_, 6, v_messages_2569_);
lean_ctor_set(v_reuseFailAlloc_2596_, 7, v_infoState_2570_);
lean_ctor_set(v_reuseFailAlloc_2596_, 8, v_snapshotTasks_2571_);
v___x_2577_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v_mctx_2580_; lean_object* v_zetaDeltaFVarIds_2581_; lean_object* v_postponed_2582_; lean_object* v_diag_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2594_; 
v___x_2578_ = lean_st_ref_set(v___y_2562_, v___x_2577_);
v___x_2579_ = lean_st_ref_take(v___y_2561_);
v_mctx_2580_ = lean_ctor_get(v___x_2579_, 0);
v_zetaDeltaFVarIds_2581_ = lean_ctor_get(v___x_2579_, 2);
v_postponed_2582_ = lean_ctor_get(v___x_2579_, 3);
v_diag_2583_ = lean_ctor_get(v___x_2579_, 4);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; 
v_unused_2595_ = lean_ctor_get(v___x_2579_, 1);
lean_dec(v_unused_2595_);
v___x_2585_ = v___x_2579_;
v_isShared_2586_ = v_isSharedCheck_2594_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_diag_2583_);
lean_inc(v_postponed_2582_);
lean_inc(v_zetaDeltaFVarIds_2581_);
lean_inc(v_mctx_2580_);
lean_dec(v___x_2579_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2594_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2587_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 1, v___x_2587_);
v___x_2589_ = v___x_2585_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_mctx_2580_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2593_, 2, v_zetaDeltaFVarIds_2581_);
lean_ctor_set(v_reuseFailAlloc_2593_, 3, v_postponed_2582_);
lean_ctor_set(v_reuseFailAlloc_2593_, 4, v_diag_2583_);
v___x_2589_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = lean_st_ref_set(v___y_2561_, v___x_2589_);
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
return v___x_2592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___boxed(lean_object* v_env_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec(v___y_2601_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(lean_object* v_env_2605_, lean_object* v_x_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___x_2614_; lean_object* v_env_2615_; lean_object* v_a_2617_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2614_ = lean_st_ref_get(v___y_2612_);
v_env_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc_ref(v_env_2615_);
lean_dec(v___x_2614_);
v___x_2627_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2605_, v___y_2610_, v___y_2612_);
lean_dec_ref(v___x_2627_);
lean_inc(v___y_2612_);
lean_inc_ref(v___y_2611_);
lean_inc(v___y_2610_);
lean_inc_ref(v___y_2609_);
lean_inc(v___y_2608_);
lean_inc_ref(v___y_2607_);
v___x_2628_ = lean_apply_7(v_x_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, lean_box(0));
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2628_, 1);
v___x_2630_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2615_, v___y_2610_, v___y_2612_);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; 
v_unused_2638_ = lean_ctor_get(v___x_2630_, 0);
lean_dec(v_unused_2638_);
v___x_2632_ = v___x_2630_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_dec(v___x_2630_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 0, v_a_2629_);
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2629_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
else
{
lean_object* v_a_2639_; 
v_a_2639_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2628_, 1);
v_a_2617_ = v_a_2639_;
goto v___jp_2616_;
}
v___jp_2616_:
{
lean_object* v___x_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
v___x_2618_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2615_, v___y_2610_, v___y_2612_);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; 
v_unused_2626_ = lean_ctor_get(v___x_2618_, 0);
lean_dec(v_unused_2626_);
v___x_2620_ = v___x_2618_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_dec(v___x_2618_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
lean_ctor_set_tag(v___x_2620_, 1);
lean_ctor_set(v___x_2620_, 0, v_a_2617_);
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2617_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_env_2640_, lean_object* v_x_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2640_, v_x_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(lean_object* v_declName_2650_, lean_object* v_env_2651_, lean_object* v_addInfo_2652_, lean_object* v_____r_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_privateToUserName_x3f(v_declName_2650_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
lean_dec_ref(v_addInfo_2652_);
lean_dec_ref(v_env_2651_);
v___x_2662_ = lean_box(0);
v___x_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
return v___x_2663_;
}
else
{
lean_object* v_val_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2681_; 
v_val_2664_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2666_ = v___x_2661_;
v_isShared_2667_ = v_isSharedCheck_2681_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_val_2664_);
lean_dec(v___x_2661_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2681_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
uint8_t v___x_2668_; uint8_t v___x_2669_; 
v___x_2668_ = 1;
lean_inc(v_val_2664_);
v___x_2669_ = l_Lean_Environment_contains(v_env_2651_, v_val_2664_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; lean_object* v___x_2672_; 
lean_dec(v_val_2664_);
lean_dec_ref(v_addInfo_2652_);
v___x_2670_ = lean_box(0);
if (v_isShared_2667_ == 0)
{
lean_ctor_set_tag(v___x_2666_, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2670_);
v___x_2672_ = v___x_2666_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
else
{
lean_object* v___x_2674_; 
lean_del_object(v___x_2666_);
lean_inc(v___y_2659_);
lean_inc_ref(v___y_2658_);
lean_inc(v___y_2657_);
lean_inc_ref(v___y_2656_);
lean_inc(v___y_2655_);
lean_inc_ref(v___y_2654_);
lean_inc(v_val_2664_);
v___x_2674_ = lean_apply_8(v_addInfo_2652_, v_val_2664_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, lean_box(0));
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
lean_dec_ref_known(v___x_2674_, 1);
v___x_2675_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
v___x_2676_ = l_Lean_MessageData_ofConstName(v_val_2664_, v___x_2668_);
v___x_2677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2675_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
v___x_2678_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2677_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2679_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
return v___x_2680_;
}
else
{
lean_dec(v_val_2664_);
return v___x_2674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed(lean_object* v_declName_2682_, lean_object* v_env_2683_, lean_object* v_addInfo_2684_, lean_object* v_____r_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(v_declName_2682_, v_env_2683_, v_addInfo_2684_, v_____r_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(lean_object* v_addInfo_2694_, lean_object* v_declName_2695_, uint8_t v___x_2696_, lean_object* v___f_2697_, uint8_t v___x_2698_, lean_object* v_env_2699_, lean_object* v___f_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___x_2708_; 
lean_inc(v___y_2706_);
lean_inc_ref(v___y_2705_);
lean_inc(v___y_2704_);
lean_inc_ref(v___y_2703_);
lean_inc(v___y_2702_);
lean_inc_ref(v___y_2701_);
lean_inc(v_declName_2695_);
v___x_2708_ = lean_apply_8(v_addInfo_2694_, v_declName_2695_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, lean_box(0));
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v___x_2709_; 
lean_dec_ref_known(v___x_2708_, 1);
lean_inc(v_declName_2695_);
v___x_2709_ = l_Lean_privateToUserName_x3f(v_declName_2695_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2710_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2711_ = l_Lean_MessageData_ofConstName(v_declName_2695_, v___x_2696_);
v___x_2712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2710_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2712_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
v___x_2715_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2714_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
return v___x_2715_;
}
else
{
lean_object* v_val_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_dec(v_declName_2695_);
v_val_2716_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_val_2716_);
lean_dec_ref_known(v___x_2709_, 1);
v___x_2717_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1);
v___x_2718_ = l_Lean_MessageData_ofConstName(v_val_2716_, v___x_2696_);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2717_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2719_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2721_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
return v___x_2722_;
}
}
else
{
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v_declName_2695_);
return v___x_2708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed(lean_object* v_addInfo_2723_, lean_object* v_declName_2724_, lean_object* v___x_2725_, lean_object* v___f_2726_, lean_object* v___x_2727_, lean_object* v_env_2728_, lean_object* v___f_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
uint8_t v___x_18633__boxed_2737_; uint8_t v___x_18635__boxed_2738_; lean_object* v_res_2739_; 
v___x_18633__boxed_2737_ = lean_unbox(v___x_2725_);
v___x_18635__boxed_2738_ = lean_unbox(v___x_2727_);
v_res_2739_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(v_addInfo_2723_, v_declName_2724_, v___x_18633__boxed_2737_, v___f_2726_, v___x_18635__boxed_2738_, v_env_2728_, v___f_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec_ref(v___f_2729_);
lean_dec_ref(v_env_2728_);
lean_dec_ref(v___f_2726_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(lean_object* v_declName_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v___x_2751_; lean_object* v_env_2752_; uint8_t v___x_2753_; lean_object* v_addInfo_2754_; lean_object* v_env_2755_; lean_object* v___f_2756_; lean_object* v___f_2757_; lean_object* v___x_2758_; lean_object* v___f_2759_; uint8_t v___x_2760_; uint8_t v___x_2761_; 
v___x_2751_ = lean_st_ref_get(v___y_2749_);
v_env_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc_ref(v_env_2752_);
lean_dec(v___x_2751_);
v___x_2753_ = 0;
v_addInfo_2754_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0));
v_env_2755_ = l_Lean_Environment_setExporting(v_env_2752_, v___x_2753_);
lean_inc_ref_n(v_env_2755_, 4);
lean_inc_n(v_declName_2743_, 4);
v___f_2756_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed), 11, 3);
lean_closure_set(v___f_2756_, 0, v_declName_2743_);
lean_closure_set(v___f_2756_, 1, v_env_2755_);
lean_closure_set(v___f_2756_, 2, v_addInfo_2754_);
v___f_2757_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2757_, 0, v_env_2755_);
lean_closure_set(v___f_2757_, 1, v_declName_2743_);
lean_closure_set(v___f_2757_, 2, v___f_2756_);
lean_closure_set(v___f_2757_, 3, v_addInfo_2754_);
v___x_2758_ = lean_box(v___x_2753_);
lean_inc_ref(v___f_2757_);
v___f_2759_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed), 12, 4);
lean_closure_set(v___f_2759_, 0, v___f_2757_);
lean_closure_set(v___f_2759_, 1, v_declName_2743_);
lean_closure_set(v___f_2759_, 2, v___x_2758_);
lean_closure_set(v___f_2759_, 3, v_env_2755_);
v___x_2760_ = 1;
v___x_2761_ = l_Lean_Environment_contains(v_env_2755_, v_declName_2743_, v___x_2760_);
if (v___x_2761_ == 0)
{
lean_object* v___f_2762_; lean_object* v___x_2763_; 
lean_dec_ref(v___f_2757_);
lean_dec(v_declName_2743_);
v___f_2762_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed), 8, 1);
lean_closure_set(v___f_2762_, 0, v___f_2759_);
v___x_2763_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2755_, v___f_2762_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
return v___x_2763_;
}
else
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___f_2766_; lean_object* v___x_2767_; 
v___x_2764_ = lean_box(v___x_2760_);
v___x_2765_ = lean_box(v___x_2753_);
lean_inc_ref(v_env_2755_);
v___f_2766_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed), 14, 7);
lean_closure_set(v___f_2766_, 0, v_addInfo_2754_);
lean_closure_set(v___f_2766_, 1, v_declName_2743_);
lean_closure_set(v___f_2766_, 2, v___x_2764_);
lean_closure_set(v___f_2766_, 3, v___f_2757_);
lean_closure_set(v___f_2766_, 4, v___x_2765_);
lean_closure_set(v___f_2766_, 5, v_env_2755_);
lean_closure_set(v___f_2766_, 6, v___f_2759_);
v___x_2767_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2755_, v___f_2766_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
return v___x_2767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___boxed(lean_object* v_declName_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(lean_object* v_modifiers_2777_, lean_object* v_declName_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v___x_2786_; lean_object* v_env_2787_; uint8_t v_visibility_2788_; uint8_t v_isProtected_2789_; lean_object* v_declName_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; uint8_t v___x_2853_; uint8_t v___x_2854_; 
v___x_2786_ = lean_st_ref_get(v___y_2784_);
v_env_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc_ref(v_env_2787_);
lean_dec(v___x_2786_);
v_visibility_2788_ = lean_ctor_get_uint8(v_modifiers_2777_, sizeof(void*)*3);
v_isProtected_2789_ = lean_ctor_get_uint8(v_modifiers_2777_, sizeof(void*)*3 + 1);
v___x_2853_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_2787_, v_visibility_2788_);
lean_dec_ref(v_env_2787_);
v___x_2854_ = lean_bool_not(v___x_2853_);
if (v___x_2854_ == 0)
{
v_declName_2791_ = v_declName_2778_;
v___y_2792_ = v___y_2779_;
v___y_2793_ = v___y_2780_;
v___y_2794_ = v___y_2781_;
v___y_2795_ = v___y_2782_;
v___y_2796_ = v___y_2783_;
v___y_2797_ = v___y_2784_;
goto v___jp_2790_;
}
else
{
lean_object* v___x_2855_; lean_object* v_env_2856_; lean_object* v_declName_2857_; 
v___x_2855_ = lean_st_ref_get(v___y_2784_);
v_env_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc_ref(v_env_2856_);
lean_dec(v___x_2855_);
v_declName_2857_ = l_Lean_mkPrivateName(v_env_2856_, v_declName_2778_);
lean_dec_ref(v_env_2856_);
v_declName_2791_ = v_declName_2857_;
v___y_2792_ = v___y_2779_;
v___y_2793_ = v___y_2780_;
v___y_2794_ = v___y_2781_;
v___y_2795_ = v___y_2782_;
v___y_2796_ = v___y_2783_;
v___y_2797_ = v___y_2784_;
goto v___jp_2790_;
}
v___jp_2790_:
{
lean_object* v___x_2798_; 
lean_inc(v_declName_2791_);
v___x_2798_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2843_; 
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v___x_2798_, 0);
lean_dec(v_unused_2844_);
v___x_2800_ = v___x_2798_;
v_isShared_2801_ = v_isSharedCheck_2843_;
goto v_resetjp_2799_;
}
else
{
lean_dec(v___x_2798_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2843_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
if (v_isProtected_2789_ == 0)
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v_declName_2791_);
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_declName_2791_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
else
{
lean_object* v___x_2805_; lean_object* v_env_2806_; lean_object* v_nextMacroScope_2807_; lean_object* v_ngen_2808_; lean_object* v_auxDeclNGen_2809_; lean_object* v_traceState_2810_; lean_object* v_messages_2811_; lean_object* v_infoState_2812_; lean_object* v_snapshotTasks_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2841_; 
v___x_2805_ = lean_st_ref_take(v___y_2797_);
v_env_2806_ = lean_ctor_get(v___x_2805_, 0);
v_nextMacroScope_2807_ = lean_ctor_get(v___x_2805_, 1);
v_ngen_2808_ = lean_ctor_get(v___x_2805_, 2);
v_auxDeclNGen_2809_ = lean_ctor_get(v___x_2805_, 3);
v_traceState_2810_ = lean_ctor_get(v___x_2805_, 4);
v_messages_2811_ = lean_ctor_get(v___x_2805_, 6);
v_infoState_2812_ = lean_ctor_get(v___x_2805_, 7);
v_snapshotTasks_2813_ = lean_ctor_get(v___x_2805_, 8);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; 
v_unused_2842_ = lean_ctor_get(v___x_2805_, 5);
lean_dec(v_unused_2842_);
v___x_2815_ = v___x_2805_;
v_isShared_2816_ = v_isSharedCheck_2841_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_snapshotTasks_2813_);
lean_inc(v_infoState_2812_);
lean_inc(v_messages_2811_);
lean_inc(v_traceState_2810_);
lean_inc(v_auxDeclNGen_2809_);
lean_inc(v_ngen_2808_);
lean_inc(v_nextMacroScope_2807_);
lean_inc(v_env_2806_);
lean_dec(v___x_2805_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2841_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2820_; 
lean_inc(v_declName_2791_);
v___x_2817_ = l_Lean_addProtected(v_env_2806_, v_declName_2791_);
v___x_2818_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 5, v___x_2818_);
lean_ctor_set(v___x_2815_, 0, v___x_2817_);
v___x_2820_ = v___x_2815_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_nextMacroScope_2807_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_ngen_2808_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_auxDeclNGen_2809_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v_traceState_2810_);
lean_ctor_set(v_reuseFailAlloc_2840_, 5, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2840_, 6, v_messages_2811_);
lean_ctor_set(v_reuseFailAlloc_2840_, 7, v_infoState_2812_);
lean_ctor_set(v_reuseFailAlloc_2840_, 8, v_snapshotTasks_2813_);
v___x_2820_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v_mctx_2823_; lean_object* v_zetaDeltaFVarIds_2824_; lean_object* v_postponed_2825_; lean_object* v_diag_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2838_; 
v___x_2821_ = lean_st_ref_set(v___y_2797_, v___x_2820_);
v___x_2822_ = lean_st_ref_take(v___y_2795_);
v_mctx_2823_ = lean_ctor_get(v___x_2822_, 0);
v_zetaDeltaFVarIds_2824_ = lean_ctor_get(v___x_2822_, 2);
v_postponed_2825_ = lean_ctor_get(v___x_2822_, 3);
v_diag_2826_ = lean_ctor_get(v___x_2822_, 4);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2838_ == 0)
{
lean_object* v_unused_2839_; 
v_unused_2839_ = lean_ctor_get(v___x_2822_, 1);
lean_dec(v_unused_2839_);
v___x_2828_ = v___x_2822_;
v_isShared_2829_ = v_isSharedCheck_2838_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_diag_2826_);
lean_inc(v_postponed_2825_);
lean_inc(v_zetaDeltaFVarIds_2824_);
lean_inc(v_mctx_2823_);
lean_dec(v___x_2822_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2838_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2830_; lean_object* v___x_2832_; 
v___x_2830_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 1, v___x_2830_);
v___x_2832_ = v___x_2828_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_mctx_2823_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v___x_2830_);
lean_ctor_set(v_reuseFailAlloc_2837_, 2, v_zetaDeltaFVarIds_2824_);
lean_ctor_set(v_reuseFailAlloc_2837_, 3, v_postponed_2825_);
lean_ctor_set(v_reuseFailAlloc_2837_, 4, v_diag_2826_);
v___x_2832_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2833_ = lean_st_ref_set(v___y_2795_, v___x_2832_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v_declName_2791_);
v___x_2835_ = v___x_2800_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_declName_2791_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
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
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec(v_declName_2791_);
v_a_2845_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2798_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2798_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4___boxed(lean_object* v_modifiers_2858_, lean_object* v_declName_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2858_, v_declName_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec_ref(v_modifiers_2858_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(lean_object* v_pre_2868_, lean_object* v_declName_2869_, lean_object* v_as_2870_, size_t v_sz_2871_, size_t v_i_2872_, lean_object* v_b_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_a_2882_; uint8_t v___x_2886_; 
v___x_2886_ = lean_usize_dec_lt(v_i_2872_, v_sz_2871_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; 
lean_dec(v_declName_2869_);
lean_dec(v_pre_2868_);
v___x_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2887_, 0, v_b_2873_);
return v___x_2887_;
}
else
{
lean_object* v___x_2888_; lean_object* v_a_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; 
v___x_2888_ = lean_box(0);
v_a_2889_ = lean_array_uget_borrowed(v_as_2870_, v_i_2872_);
lean_inc(v_a_2889_);
lean_inc(v_pre_2868_);
v___x_2890_ = l_Lean_Name_append(v_pre_2868_, v_a_2889_);
v___x_2891_ = lean_name_eq(v___x_2890_, v_declName_2869_);
lean_dec(v___x_2890_);
if (v___x_2891_ == 0)
{
v_a_2882_ = v___x_2888_;
goto v___jp_2881_;
}
else
{
lean_object* v___x_2892_; uint8_t v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2892_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_2893_ = 0;
lean_inc(v_declName_2869_);
v___x_2894_ = l_Lean_MessageData_ofConstName(v_declName_2869_, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2892_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_2897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2895_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
lean_inc(v_pre_2868_);
v___x_2898_ = l_Lean_MessageData_ofName(v_pre_2868_);
v___x_2899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2897_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
v___x_2900_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
lean_inc(v_a_2889_);
v___x_2902_ = l_Lean_MessageData_ofName(v_a_2889_);
v___x_2903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2905_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_dec_ref_known(v___x_2906_, 1);
v_a_2882_ = v___x_2888_;
goto v___jp_2881_;
}
else
{
lean_dec(v_declName_2869_);
lean_dec(v_pre_2868_);
return v___x_2906_;
}
}
}
v___jp_2881_:
{
size_t v___x_2883_; size_t v___x_2884_; 
v___x_2883_ = ((size_t)1ULL);
v___x_2884_ = lean_usize_add(v_i_2872_, v___x_2883_);
v_i_2872_ = v___x_2884_;
v_b_2873_ = v_a_2882_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6___boxed(lean_object* v_pre_2907_, lean_object* v_declName_2908_, lean_object* v_as_2909_, lean_object* v_sz_2910_, lean_object* v_i_2911_, lean_object* v_b_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
size_t v_sz_boxed_2920_; size_t v_i_boxed_2921_; lean_object* v_res_2922_; 
v_sz_boxed_2920_ = lean_unbox_usize(v_sz_2910_);
lean_dec(v_sz_2910_);
v_i_boxed_2921_ = lean_unbox_usize(v_i_2911_);
lean_dec(v_i_2911_);
v_res_2922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2907_, v_declName_2908_, v_as_2909_, v_sz_boxed_2920_, v_i_boxed_2921_, v_b_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec_ref(v_as_2909_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(lean_object* v_declName_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
if (lean_obj_tag(v_declName_2923_) == 1)
{
lean_object* v_pre_2931_; lean_object* v___x_2932_; lean_object* v_env_2933_; uint8_t v___x_2934_; 
v_pre_2931_ = lean_ctor_get(v_declName_2923_, 0);
lean_inc_n(v_pre_2931_, 2);
v___x_2932_ = lean_st_ref_get(v___y_2929_);
v_env_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc_ref(v_env_2933_);
lean_dec(v___x_2932_);
v___x_2934_ = l_Lean_isStructure(v_env_2933_, v_pre_2931_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
lean_dec(v_pre_2931_);
lean_dec_ref_known(v_declName_2923_, 2);
v___x_2935_ = lean_box(0);
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
return v___x_2936_;
}
else
{
lean_object* v___x_2937_; lean_object* v_env_2938_; lean_object* v_fieldNames_2939_; lean_object* v___x_2940_; size_t v_sz_2941_; size_t v___x_2942_; lean_object* v___x_2943_; 
v___x_2937_ = lean_st_ref_get(v___y_2929_);
v_env_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc_ref(v_env_2938_);
lean_dec(v___x_2937_);
lean_inc(v_pre_2931_);
v_fieldNames_2939_ = l_Lean_getStructureFieldsFlattened(v_env_2938_, v_pre_2931_, v___x_2934_);
v___x_2940_ = lean_box(0);
v_sz_2941_ = lean_array_size(v_fieldNames_2939_);
v___x_2942_ = ((size_t)0ULL);
v___x_2943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2931_, v_declName_2923_, v_fieldNames_2939_, v_sz_2941_, v___x_2942_, v___x_2940_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec_ref(v_fieldNames_2939_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2950_ == 0)
{
lean_object* v_unused_2951_; 
v_unused_2951_ = lean_ctor_get(v___x_2943_, 0);
lean_dec(v_unused_2951_);
v___x_2945_ = v___x_2943_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_dec(v___x_2943_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___x_2940_);
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2940_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
else
{
return v___x_2943_;
}
}
}
else
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
lean_dec(v_declName_2923_);
v___x_2952_ = lean_box(0);
v___x_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
return v___x_2953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3___boxed(lean_object* v_declName_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v_declName_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(lean_object* v_currNamespace_2963_, lean_object* v_modifiers_2964_, lean_object* v_shortName_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2979_; lean_object* v_shortName_2980_; lean_object* v_currNamespace_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v_view_3041_; lean_object* v_name_3042_; lean_object* v_imported_3043_; lean_object* v_ctx_3044_; lean_object* v_scopes_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3103_; 
lean_inc(v_shortName_2965_);
v_view_3041_ = l_Lean_extractMacroScopes(v_shortName_2965_);
v_name_3042_ = lean_ctor_get(v_view_3041_, 0);
v_imported_3043_ = lean_ctor_get(v_view_3041_, 1);
v_ctx_3044_ = lean_ctor_get(v_view_3041_, 2);
v_scopes_3045_ = lean_ctor_get(v_view_3041_, 3);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_view_3041_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3047_ = v_view_3041_;
v_isShared_3048_ = v_isSharedCheck_3103_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_scopes_3045_);
lean_inc(v_ctx_3044_);
lean_inc(v_imported_3043_);
lean_inc(v_name_3042_);
lean_dec(v_view_3041_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3103_;
goto v_resetjp_3046_;
}
v___jp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___y_2975_);
lean_ctor_set(v___x_2976_, 1, v___y_2974_);
v___x_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
return v___x_2977_;
}
v___jp_2978_:
{
lean_object* v___x_2988_; 
lean_inc(v___y_2979_);
v___x_2988_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v___y_2979_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v___x_2989_; 
lean_dec_ref_known(v___x_2988_, 1);
v___x_2989_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2964_, v___y_2979_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
if (lean_obj_tag(v___x_2989_) == 0)
{
uint8_t v_isProtected_2990_; 
v_isProtected_2990_ = lean_ctor_get_uint8(v_modifiers_2964_, sizeof(void*)*3 + 1);
if (v_isProtected_2990_ == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2999_; 
lean_dec(v_currNamespace_2981_);
v_a_2991_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2993_ = v___x_2989_;
v_isShared_2994_ = v_isSharedCheck_2999_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2989_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2999_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; lean_object* v___x_2997_; 
v___x_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2995_, 0, v_a_2991_);
lean_ctor_set(v___x_2995_, 1, v_shortName_2980_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v___x_2995_);
v___x_2997_ = v___x_2993_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
else
{
if (lean_obj_tag(v_currNamespace_2981_) == 1)
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3012_; 
v_a_3000_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3002_ = v___x_2989_;
v_isShared_3003_ = v_isSharedCheck_3012_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2989_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3012_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v_str_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3010_; 
v_str_3004_ = lean_ctor_get(v_currNamespace_2981_, 1);
lean_inc_ref(v_str_3004_);
lean_dec_ref_known(v_currNamespace_2981_, 2);
v___x_3005_ = lean_box(0);
v___x_3006_ = l_Lean_Name_str___override(v___x_3005_, v_str_3004_);
v___x_3007_ = l_Lean_Name_append(v___x_3006_, v_shortName_2980_);
v___x_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3008_, 0, v_a_3000_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v___x_3008_);
v___x_3010_ = v___x_3002_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
else
{
lean_object* v_a_3013_; uint8_t v___x_3014_; 
lean_dec(v_currNamespace_2981_);
v_a_3013_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_2989_, 1);
v___x_3014_ = l_Lean_Name_isAtomic(v_shortName_2980_);
if (v___x_3014_ == 0)
{
v___y_2974_ = v_shortName_2980_;
v___y_2975_ = v_a_3013_;
goto v___jp_2973_;
}
else
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec(v_a_3013_);
lean_dec(v_shortName_2980_);
v___x_3015_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_3016_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3015_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3016_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3016_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec(v_currNamespace_2981_);
lean_dec(v_shortName_2980_);
v_a_3025_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2989_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2989_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec(v_currNamespace_2981_);
lean_dec(v_shortName_2980_);
lean_dec(v___y_2979_);
v_a_3033_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_2988_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_2988_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; uint8_t v_isRootName_3050_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; uint8_t v___x_3092_; 
v___x_3049_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_3050_ = l_Lean_Name_isPrefixOf(v___x_3049_, v_name_3042_);
v___x_3092_ = lean_name_eq(v_name_3042_, v___x_3049_);
if (v___x_3092_ == 0)
{
v___y_3079_ = v___y_2966_;
v___y_3080_ = v___y_2967_;
v___y_3081_ = v___y_2968_;
v___y_3082_ = v___y_2969_;
v___y_3083_ = v___y_2970_;
v___y_3084_ = v___y_2971_;
goto v___jp_3078_;
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_del_object(v___x_3047_);
lean_dec(v_scopes_3045_);
lean_dec(v_ctx_3044_);
lean_dec(v_imported_3043_);
lean_dec(v_name_3042_);
lean_dec(v_shortName_2965_);
lean_dec(v_currNamespace_2963_);
v___x_3093_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_3094_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3093_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
v___jp_3051_:
{
if (v_isRootName_3050_ == 0)
{
lean_dec(v_name_3042_);
v___y_2979_ = v___y_3058_;
v_shortName_2980_ = v_shortName_2965_;
v_currNamespace_2981_ = v_currNamespace_2963_;
v___y_2982_ = v___y_3054_;
v___y_2983_ = v___y_3052_;
v___y_2984_ = v___y_3057_;
v___y_2985_ = v___y_3053_;
v___y_2986_ = v___y_3056_;
v___y_2987_ = v___y_3055_;
goto v___jp_2978_;
}
else
{
lean_dec(v_shortName_2965_);
lean_dec(v_currNamespace_2963_);
if (lean_obj_tag(v_name_3042_) == 1)
{
lean_object* v_pre_3059_; lean_object* v_str_3060_; lean_object* v___x_3061_; lean_object* v_shortName_3062_; lean_object* v_currNamespace_3063_; 
v_pre_3059_ = lean_ctor_get(v_name_3042_, 0);
lean_inc(v_pre_3059_);
v_str_3060_ = lean_ctor_get(v_name_3042_, 1);
lean_inc_ref(v_str_3060_);
lean_dec_ref_known(v_name_3042_, 2);
v___x_3061_ = lean_box(0);
v_shortName_3062_ = l_Lean_Name_str___override(v___x_3061_, v_str_3060_);
v_currNamespace_3063_ = l_Lean_Name_replacePrefix(v_pre_3059_, v___x_3049_, v___x_3061_);
v___y_2979_ = v___y_3058_;
v_shortName_2980_ = v_shortName_3062_;
v_currNamespace_2981_ = v_currNamespace_3063_;
v___y_2982_ = v___y_3054_;
v___y_2983_ = v___y_3052_;
v___y_2984_ = v___y_3057_;
v___y_2985_ = v___y_3053_;
v___y_2986_ = v___y_3056_;
v___y_2987_ = v___y_3055_;
goto v___jp_2978_;
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec(v___y_3058_);
v___x_3064_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_3065_ = l_Lean_MessageData_ofName(v_name_3042_);
v___x_3066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3064_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_3068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3066_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3068_, v___y_3054_, v___y_3052_, v___y_3057_, v___y_3053_, v___y_3056_, v___y_3055_);
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
}
v___jp_3078_:
{
if (v_isRootName_3050_ == 0)
{
lean_object* v___x_3085_; 
lean_del_object(v___x_3047_);
lean_dec(v_scopes_3045_);
lean_dec(v_ctx_3044_);
lean_dec(v_imported_3043_);
lean_inc(v_shortName_2965_);
lean_inc(v_currNamespace_2963_);
v___x_3085_ = l_Lean_Name_append(v_currNamespace_2963_, v_shortName_2965_);
v___y_3052_ = v___y_3080_;
v___y_3053_ = v___y_3082_;
v___y_3054_ = v___y_3079_;
v___y_3055_ = v___y_3084_;
v___y_3056_ = v___y_3083_;
v___y_3057_ = v___y_3081_;
v___y_3058_ = v___x_3085_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3089_; 
v___x_3086_ = lean_box(0);
lean_inc(v_name_3042_);
v___x_3087_ = l_Lean_Name_replacePrefix(v_name_3042_, v___x_3049_, v___x_3086_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3087_);
v___x_3089_ = v___x_3047_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3087_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_imported_3043_);
lean_ctor_set(v_reuseFailAlloc_3091_, 2, v_ctx_3044_);
lean_ctor_set(v_reuseFailAlloc_3091_, 3, v_scopes_3045_);
v___x_3089_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Lean_MacroScopesView_review(v___x_3089_);
v___y_3052_ = v___y_3080_;
v___y_3053_ = v___y_3082_;
v___y_3054_ = v___y_3079_;
v___y_3055_ = v___y_3084_;
v___y_3056_ = v___y_3083_;
v___y_3057_ = v___y_3081_;
v___y_3058_ = v___x_3090_;
goto v___jp_3051_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2___boxed(lean_object* v_currNamespace_3104_, lean_object* v_modifiers_3105_, lean_object* v_shortName_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3104_, v_modifiers_3105_, v_shortName_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec_ref(v_modifiers_3105_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(uint8_t v___x_3115_, lean_object* v_as_3116_, size_t v_i_3117_, size_t v_stop_3118_, lean_object* v_b_3119_){
_start:
{
lean_object* v___y_3121_; uint8_t v___x_3125_; 
v___x_3125_ = lean_usize_dec_eq(v_i_3117_, v_stop_3118_);
if (v___x_3125_ == 0)
{
lean_object* v_fst_3126_; uint8_t v___x_3127_; 
v_fst_3126_ = lean_ctor_get(v_b_3119_, 0);
v___x_3127_ = lean_unbox(v_fst_3126_);
if (v___x_3127_ == 0)
{
lean_object* v_snd_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3137_; 
v_snd_3128_ = lean_ctor_get(v_b_3119_, 1);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_b_3119_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; 
v_unused_3138_ = lean_ctor_get(v_b_3119_, 0);
lean_dec(v_unused_3138_);
v___x_3130_ = v_b_3119_;
v_isShared_3131_ = v_isSharedCheck_3137_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_snd_3128_);
lean_dec(v_b_3119_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3137_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
uint8_t v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
v___x_3132_ = 1;
v___x_3133_ = lean_box(v___x_3132_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3133_);
v___x_3135_ = v___x_3130_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_snd_3128_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
v___y_3121_ = v___x_3135_;
goto v___jp_3120_;
}
}
}
else
{
lean_object* v_snd_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3149_; 
v_snd_3139_ = lean_ctor_get(v_b_3119_, 1);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_b_3119_);
if (v_isSharedCheck_3149_ == 0)
{
lean_object* v_unused_3150_; 
v_unused_3150_ = lean_ctor_get(v_b_3119_, 0);
lean_dec(v_unused_3150_);
v___x_3141_ = v_b_3119_;
v_isShared_3142_ = v_isSharedCheck_3149_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_snd_3139_);
lean_dec(v_b_3119_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3149_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3147_; 
v___x_3143_ = lean_array_uget_borrowed(v_as_3116_, v_i_3117_);
lean_inc(v___x_3143_);
v___x_3144_ = lean_array_push(v_snd_3139_, v___x_3143_);
v___x_3145_ = lean_box(v___x_3115_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 1, v___x_3144_);
lean_ctor_set(v___x_3141_, 0, v___x_3145_);
v___x_3147_ = v___x_3141_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3145_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v___x_3144_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
v___y_3121_ = v___x_3147_;
goto v___jp_3120_;
}
}
}
}
else
{
return v_b_3119_;
}
v___jp_3120_:
{
size_t v___x_3122_; size_t v___x_3123_; 
v___x_3122_ = ((size_t)1ULL);
v___x_3123_ = lean_usize_add(v_i_3117_, v___x_3122_);
v_i_3117_ = v___x_3123_;
v_b_3119_ = v___y_3121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4___boxed(lean_object* v___x_3151_, lean_object* v_as_3152_, lean_object* v_i_3153_, lean_object* v_stop_3154_, lean_object* v_b_3155_){
_start:
{
uint8_t v___x_19344__boxed_3156_; size_t v_i_boxed_3157_; size_t v_stop_boxed_3158_; lean_object* v_res_3159_; 
v___x_19344__boxed_3156_ = lean_unbox(v___x_3151_);
v_i_boxed_3157_ = lean_unbox_usize(v_i_3153_);
lean_dec(v_i_3153_);
v_stop_boxed_3158_ = lean_unbox_usize(v_stop_3154_);
lean_dec(v_stop_3154_);
v_res_3159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_19344__boxed_3156_, v_as_3152_, v_i_boxed_3157_, v_stop_boxed_3158_, v_b_3155_);
lean_dec_ref(v_as_3152_);
return v_res_3159_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(lean_object* v_a_3160_, lean_object* v_x_3161_){
_start:
{
if (lean_obj_tag(v_x_3161_) == 0)
{
uint8_t v___x_3162_; 
v___x_3162_ = 0;
return v___x_3162_;
}
else
{
lean_object* v_head_3163_; lean_object* v_tail_3164_; uint8_t v___x_3165_; 
v_head_3163_ = lean_ctor_get(v_x_3161_, 0);
v_tail_3164_ = lean_ctor_get(v_x_3161_, 1);
v___x_3165_ = lean_name_eq(v_a_3160_, v_head_3163_);
if (v___x_3165_ == 0)
{
v_x_3161_ = v_tail_3164_;
goto _start;
}
else
{
return v___x_3165_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_expandDeclId_spec__0___boxed(lean_object* v_a_3167_, lean_object* v_x_3168_){
_start:
{
uint8_t v_res_3169_; lean_object* v_r_3170_; 
v_res_3169_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_a_3167_, v_x_3168_);
lean_dec(v_x_3168_);
lean_dec(v_a_3167_);
v_r_3170_ = lean_box(v_res_3169_);
return v_r_3170_;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = ((lean_object*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0));
v___x_3173_ = l_Lean_stringToMessageData(v___x_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(lean_object* v_u_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3182_ = lean_obj_once(&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1, &l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1);
v___x_3183_ = l_Lean_MessageData_ofName(v_u_3174_);
v___x_3184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3182_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
v___x_3185_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_3186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3184_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3186_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___boxed(lean_object* v_u_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(lean_object* v_as_3197_, size_t v_i_3198_, size_t v_stop_3199_, lean_object* v_b_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v_a_3209_; uint8_t v___x_3213_; 
v___x_3213_ = lean_usize_dec_eq(v_i_3198_, v_stop_3199_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; lean_object* v_id_3215_; uint8_t v___x_3216_; 
v___x_3214_ = lean_array_uget_borrowed(v_as_3197_, v_i_3198_);
v_id_3215_ = l_Lean_Syntax_getId(v___x_3214_);
v___x_3216_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_id_3215_, v_b_3200_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3217_, 0, v_id_3215_);
lean_ctor_set(v___x_3217_, 1, v_b_3200_);
v_a_3209_ = v___x_3217_;
goto v___jp_3208_;
}
else
{
lean_object* v_fileName_3218_; lean_object* v_fileMap_3219_; lean_object* v_options_3220_; lean_object* v_currRecDepth_3221_; lean_object* v_maxRecDepth_3222_; lean_object* v_ref_3223_; lean_object* v_currNamespace_3224_; lean_object* v_openDecls_3225_; lean_object* v_initHeartbeats_3226_; lean_object* v_maxHeartbeats_3227_; lean_object* v_quotContext_3228_; lean_object* v_currMacroScope_3229_; uint8_t v_diag_3230_; lean_object* v_cancelTk_x3f_3231_; uint8_t v_suppressElabErrors_3232_; lean_object* v_inheritedTraceOptions_3233_; lean_object* v_ref_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
lean_dec(v_b_3200_);
v_fileName_3218_ = lean_ctor_get(v___y_3205_, 0);
v_fileMap_3219_ = lean_ctor_get(v___y_3205_, 1);
v_options_3220_ = lean_ctor_get(v___y_3205_, 2);
v_currRecDepth_3221_ = lean_ctor_get(v___y_3205_, 3);
v_maxRecDepth_3222_ = lean_ctor_get(v___y_3205_, 4);
v_ref_3223_ = lean_ctor_get(v___y_3205_, 5);
v_currNamespace_3224_ = lean_ctor_get(v___y_3205_, 6);
v_openDecls_3225_ = lean_ctor_get(v___y_3205_, 7);
v_initHeartbeats_3226_ = lean_ctor_get(v___y_3205_, 8);
v_maxHeartbeats_3227_ = lean_ctor_get(v___y_3205_, 9);
v_quotContext_3228_ = lean_ctor_get(v___y_3205_, 10);
v_currMacroScope_3229_ = lean_ctor_get(v___y_3205_, 11);
v_diag_3230_ = lean_ctor_get_uint8(v___y_3205_, sizeof(void*)*14);
v_cancelTk_x3f_3231_ = lean_ctor_get(v___y_3205_, 12);
v_suppressElabErrors_3232_ = lean_ctor_get_uint8(v___y_3205_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3233_ = lean_ctor_get(v___y_3205_, 13);
v_ref_3234_ = l_Lean_replaceRef(v___x_3214_, v_ref_3223_);
lean_inc_ref(v_inheritedTraceOptions_3233_);
lean_inc(v_cancelTk_x3f_3231_);
lean_inc(v_currMacroScope_3229_);
lean_inc(v_quotContext_3228_);
lean_inc(v_maxHeartbeats_3227_);
lean_inc(v_initHeartbeats_3226_);
lean_inc(v_openDecls_3225_);
lean_inc(v_currNamespace_3224_);
lean_inc(v_maxRecDepth_3222_);
lean_inc(v_currRecDepth_3221_);
lean_inc_ref(v_options_3220_);
lean_inc_ref(v_fileMap_3219_);
lean_inc_ref(v_fileName_3218_);
v___x_3235_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3235_, 0, v_fileName_3218_);
lean_ctor_set(v___x_3235_, 1, v_fileMap_3219_);
lean_ctor_set(v___x_3235_, 2, v_options_3220_);
lean_ctor_set(v___x_3235_, 3, v_currRecDepth_3221_);
lean_ctor_set(v___x_3235_, 4, v_maxRecDepth_3222_);
lean_ctor_set(v___x_3235_, 5, v_ref_3234_);
lean_ctor_set(v___x_3235_, 6, v_currNamespace_3224_);
lean_ctor_set(v___x_3235_, 7, v_openDecls_3225_);
lean_ctor_set(v___x_3235_, 8, v_initHeartbeats_3226_);
lean_ctor_set(v___x_3235_, 9, v_maxHeartbeats_3227_);
lean_ctor_set(v___x_3235_, 10, v_quotContext_3228_);
lean_ctor_set(v___x_3235_, 11, v_currMacroScope_3229_);
lean_ctor_set(v___x_3235_, 12, v_cancelTk_x3f_3231_);
lean_ctor_set(v___x_3235_, 13, v_inheritedTraceOptions_3233_);
lean_ctor_set_uint8(v___x_3235_, sizeof(void*)*14, v_diag_3230_);
lean_ctor_set_uint8(v___x_3235_, sizeof(void*)*14 + 1, v_suppressElabErrors_3232_);
v___x_3236_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_id_3215_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___x_3235_, v___y_3206_);
lean_dec_ref_known(v___x_3235_, 14);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
lean_dec_ref_known(v___x_3236_, 1);
v_a_3209_ = v_a_3237_;
goto v___jp_3208_;
}
else
{
return v___x_3236_;
}
}
}
else
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3238_, 0, v_b_3200_);
return v___x_3238_;
}
v___jp_3208_:
{
size_t v___x_3210_; size_t v___x_3211_; 
v___x_3210_ = ((size_t)1ULL);
v___x_3211_ = lean_usize_add(v_i_3198_, v___x_3210_);
v_i_3198_ = v___x_3211_;
v_b_3200_ = v_a_3209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3___boxed(lean_object* v_as_3239_, lean_object* v_i_3240_, lean_object* v_stop_3241_, lean_object* v_b_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
size_t v_i_boxed_3250_; size_t v_stop_boxed_3251_; lean_object* v_res_3252_; 
v_i_boxed_3250_ = lean_unbox_usize(v_i_3240_);
lean_dec(v_i_3240_);
v_stop_boxed_3251_ = lean_unbox_usize(v_stop_3241_);
lean_dec(v_stop_3241_);
v_res_3252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v_as_3239_, v_i_boxed_3250_, v_stop_boxed_3251_, v_b_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec_ref(v_as_3239_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId(lean_object* v_currNamespace_3253_, lean_object* v_currLevelNames_3254_, lean_object* v_declId_3255_, lean_object* v_modifiers_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v___x_3264_; lean_object* v_fst_3265_; lean_object* v_snd_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3361_; 
v___x_3264_ = l_Lean_Elab_expandDeclIdCore(v_declId_3255_);
v_fst_3265_ = lean_ctor_get(v___x_3264_, 0);
v_snd_3266_ = lean_ctor_get(v___x_3264_, 1);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3268_ = v___x_3264_;
v_isShared_3269_ = v_isSharedCheck_3361_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_snd_3266_);
lean_inc(v_fst_3265_);
lean_dec(v___x_3264_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3361_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v_levelNames_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3318_; lean_object* v___y_3329_; uint8_t v___x_3340_; 
v___x_3340_ = l_Lean_Syntax_isNone(v_snd_3266_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v___x_3341_ = lean_unsigned_to_nat(1u);
v___x_3342_ = l_Lean_Syntax_getArg(v_snd_3266_, v___x_3341_);
lean_dec(v_snd_3266_);
v___x_3343_ = l_Lean_Syntax_getArgs(v___x_3342_);
lean_dec(v___x_3342_);
v___x_3344_ = lean_unsigned_to_nat(0u);
v___x_3345_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__0));
v___x_3346_ = lean_array_get_size(v___x_3343_);
v___x_3347_ = lean_nat_dec_lt(v___x_3344_, v___x_3346_);
if (v___x_3347_ == 0)
{
lean_dec_ref(v___x_3343_);
lean_del_object(v___x_3268_);
v___y_3329_ = v___x_3345_;
goto v___jp_3328_;
}
else
{
lean_object* v___x_3348_; lean_object* v___x_3350_; 
v___x_3348_ = lean_box(v___x_3347_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 1, v___x_3345_);
lean_ctor_set(v___x_3268_, 0, v___x_3348_);
v___x_3350_ = v___x_3268_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3348_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v___x_3345_);
v___x_3350_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
uint8_t v___x_3351_; 
v___x_3351_ = lean_nat_dec_le(v___x_3346_, v___x_3346_);
if (v___x_3351_ == 0)
{
if (v___x_3347_ == 0)
{
lean_dec_ref(v___x_3350_);
lean_dec_ref(v___x_3343_);
v___y_3329_ = v___x_3345_;
goto v___jp_3328_;
}
else
{
size_t v___x_3352_; size_t v___x_3353_; lean_object* v___x_3354_; lean_object* v_snd_3355_; 
v___x_3352_ = ((size_t)0ULL);
v___x_3353_ = lean_usize_of_nat(v___x_3346_);
v___x_3354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3340_, v___x_3343_, v___x_3352_, v___x_3353_, v___x_3350_);
lean_dec_ref(v___x_3343_);
v_snd_3355_ = lean_ctor_get(v___x_3354_, 1);
lean_inc(v_snd_3355_);
lean_dec_ref(v___x_3354_);
v___y_3329_ = v_snd_3355_;
goto v___jp_3328_;
}
}
else
{
size_t v___x_3356_; size_t v___x_3357_; lean_object* v___x_3358_; lean_object* v_snd_3359_; 
v___x_3356_ = ((size_t)0ULL);
v___x_3357_ = lean_usize_of_nat(v___x_3346_);
v___x_3358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3340_, v___x_3343_, v___x_3356_, v___x_3357_, v___x_3350_);
lean_dec_ref(v___x_3343_);
v_snd_3359_ = lean_ctor_get(v___x_3358_, 1);
lean_inc(v_snd_3359_);
lean_dec_ref(v___x_3358_);
v___y_3329_ = v_snd_3359_;
goto v___jp_3328_;
}
}
}
}
else
{
lean_del_object(v___x_3268_);
lean_dec(v_snd_3266_);
v_levelNames_3271_ = v_currLevelNames_3254_;
v___y_3272_ = v_a_3257_;
v___y_3273_ = v_a_3258_;
v___y_3274_ = v_a_3259_;
v___y_3275_ = v_a_3260_;
v___y_3276_ = v_a_3261_;
v___y_3277_ = v_a_3262_;
goto v___jp_3270_;
}
v___jp_3270_:
{
lean_object* v_fileName_3278_; lean_object* v_fileMap_3279_; lean_object* v_options_3280_; lean_object* v_currRecDepth_3281_; lean_object* v_maxRecDepth_3282_; lean_object* v_ref_3283_; lean_object* v_currNamespace_3284_; lean_object* v_openDecls_3285_; lean_object* v_initHeartbeats_3286_; lean_object* v_maxHeartbeats_3287_; lean_object* v_quotContext_3288_; lean_object* v_currMacroScope_3289_; uint8_t v_diag_3290_; lean_object* v_cancelTk_x3f_3291_; uint8_t v_suppressElabErrors_3292_; lean_object* v_inheritedTraceOptions_3293_; lean_object* v_ref_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_fileName_3278_ = lean_ctor_get(v___y_3276_, 0);
v_fileMap_3279_ = lean_ctor_get(v___y_3276_, 1);
v_options_3280_ = lean_ctor_get(v___y_3276_, 2);
v_currRecDepth_3281_ = lean_ctor_get(v___y_3276_, 3);
v_maxRecDepth_3282_ = lean_ctor_get(v___y_3276_, 4);
v_ref_3283_ = lean_ctor_get(v___y_3276_, 5);
v_currNamespace_3284_ = lean_ctor_get(v___y_3276_, 6);
v_openDecls_3285_ = lean_ctor_get(v___y_3276_, 7);
v_initHeartbeats_3286_ = lean_ctor_get(v___y_3276_, 8);
v_maxHeartbeats_3287_ = lean_ctor_get(v___y_3276_, 9);
v_quotContext_3288_ = lean_ctor_get(v___y_3276_, 10);
v_currMacroScope_3289_ = lean_ctor_get(v___y_3276_, 11);
v_diag_3290_ = lean_ctor_get_uint8(v___y_3276_, sizeof(void*)*14);
v_cancelTk_x3f_3291_ = lean_ctor_get(v___y_3276_, 12);
v_suppressElabErrors_3292_ = lean_ctor_get_uint8(v___y_3276_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3293_ = lean_ctor_get(v___y_3276_, 13);
v_ref_3294_ = l_Lean_replaceRef(v_declId_3255_, v_ref_3283_);
lean_inc_ref(v_inheritedTraceOptions_3293_);
lean_inc(v_cancelTk_x3f_3291_);
lean_inc(v_currMacroScope_3289_);
lean_inc(v_quotContext_3288_);
lean_inc(v_maxHeartbeats_3287_);
lean_inc(v_initHeartbeats_3286_);
lean_inc(v_openDecls_3285_);
lean_inc(v_currNamespace_3284_);
lean_inc(v_maxRecDepth_3282_);
lean_inc(v_currRecDepth_3281_);
lean_inc_ref(v_options_3280_);
lean_inc_ref(v_fileMap_3279_);
lean_inc_ref(v_fileName_3278_);
v___x_3295_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3295_, 0, v_fileName_3278_);
lean_ctor_set(v___x_3295_, 1, v_fileMap_3279_);
lean_ctor_set(v___x_3295_, 2, v_options_3280_);
lean_ctor_set(v___x_3295_, 3, v_currRecDepth_3281_);
lean_ctor_set(v___x_3295_, 4, v_maxRecDepth_3282_);
lean_ctor_set(v___x_3295_, 5, v_ref_3294_);
lean_ctor_set(v___x_3295_, 6, v_currNamespace_3284_);
lean_ctor_set(v___x_3295_, 7, v_openDecls_3285_);
lean_ctor_set(v___x_3295_, 8, v_initHeartbeats_3286_);
lean_ctor_set(v___x_3295_, 9, v_maxHeartbeats_3287_);
lean_ctor_set(v___x_3295_, 10, v_quotContext_3288_);
lean_ctor_set(v___x_3295_, 11, v_currMacroScope_3289_);
lean_ctor_set(v___x_3295_, 12, v_cancelTk_x3f_3291_);
lean_ctor_set(v___x_3295_, 13, v_inheritedTraceOptions_3293_);
lean_ctor_set_uint8(v___x_3295_, sizeof(void*)*14, v_diag_3290_);
lean_ctor_set_uint8(v___x_3295_, sizeof(void*)*14 + 1, v_suppressElabErrors_3292_);
v___x_3296_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3253_, v_modifiers_3256_, v_fst_3265_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___x_3295_, v___y_3277_);
lean_dec_ref_known(v___x_3295_, 14);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3308_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3299_ = v___x_3296_;
v_isShared_3300_ = v_isSharedCheck_3308_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3296_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3308_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v_fst_3301_; lean_object* v_snd_3302_; lean_object* v_docString_x3f_3303_; lean_object* v___x_3304_; lean_object* v___x_3306_; 
v_fst_3301_ = lean_ctor_get(v_a_3297_, 0);
lean_inc(v_fst_3301_);
v_snd_3302_ = lean_ctor_get(v_a_3297_, 1);
lean_inc(v_snd_3302_);
lean_dec(v_a_3297_);
v_docString_x3f_3303_ = lean_ctor_get(v_modifiers_3256_, 1);
lean_inc(v_docString_x3f_3303_);
v___x_3304_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3304_, 0, v_snd_3302_);
lean_ctor_set(v___x_3304_, 1, v_fst_3301_);
lean_ctor_set(v___x_3304_, 2, v_levelNames_3271_);
lean_ctor_set(v___x_3304_, 3, v_docString_x3f_3303_);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 0, v___x_3304_);
v___x_3306_ = v___x_3299_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3304_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec(v_levelNames_3271_);
v_a_3309_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3296_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3296_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
v___jp_3317_:
{
if (lean_obj_tag(v___y_3318_) == 0)
{
lean_object* v_a_3319_; 
v_a_3319_ = lean_ctor_get(v___y_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___y_3318_, 1);
v_levelNames_3271_ = v_a_3319_;
v___y_3272_ = v_a_3257_;
v___y_3273_ = v_a_3258_;
v___y_3274_ = v_a_3259_;
v___y_3275_ = v_a_3260_;
v___y_3276_ = v_a_3261_;
v___y_3277_ = v_a_3262_;
goto v___jp_3270_;
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec(v_fst_3265_);
lean_dec(v_currNamespace_3253_);
v_a_3320_ = lean_ctor_get(v___y_3318_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___y_3318_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___y_3318_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___y_3318_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
v___jp_3328_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; uint8_t v___x_3332_; 
v___x_3330_ = lean_unsigned_to_nat(0u);
v___x_3331_ = lean_array_get_size(v___y_3329_);
v___x_3332_ = lean_nat_dec_lt(v___x_3330_, v___x_3331_);
if (v___x_3332_ == 0)
{
lean_dec_ref(v___y_3329_);
v_levelNames_3271_ = v_currLevelNames_3254_;
v___y_3272_ = v_a_3257_;
v___y_3273_ = v_a_3258_;
v___y_3274_ = v_a_3259_;
v___y_3275_ = v_a_3260_;
v___y_3276_ = v_a_3261_;
v___y_3277_ = v_a_3262_;
goto v___jp_3270_;
}
else
{
uint8_t v___x_3333_; 
v___x_3333_ = lean_nat_dec_le(v___x_3331_, v___x_3331_);
if (v___x_3333_ == 0)
{
if (v___x_3332_ == 0)
{
lean_dec_ref(v___y_3329_);
v_levelNames_3271_ = v_currLevelNames_3254_;
v___y_3272_ = v_a_3257_;
v___y_3273_ = v_a_3258_;
v___y_3274_ = v_a_3259_;
v___y_3275_ = v_a_3260_;
v___y_3276_ = v_a_3261_;
v___y_3277_ = v_a_3262_;
goto v___jp_3270_;
}
else
{
size_t v___x_3334_; size_t v___x_3335_; lean_object* v___x_3336_; 
v___x_3334_ = ((size_t)0ULL);
v___x_3335_ = lean_usize_of_nat(v___x_3331_);
v___x_3336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3329_, v___x_3334_, v___x_3335_, v_currLevelNames_3254_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_);
lean_dec_ref(v___y_3329_);
v___y_3318_ = v___x_3336_;
goto v___jp_3317_;
}
}
else
{
size_t v___x_3337_; size_t v___x_3338_; lean_object* v___x_3339_; 
v___x_3337_ = ((size_t)0ULL);
v___x_3338_ = lean_usize_of_nat(v___x_3331_);
v___x_3339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3329_, v___x_3337_, v___x_3338_, v_currLevelNames_3254_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_);
lean_dec_ref(v___y_3329_);
v___y_3318_ = v___x_3339_;
goto v___jp_3317_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___boxed(lean_object* v_currNamespace_3362_, lean_object* v_currLevelNames_3363_, lean_object* v_declId_3364_, lean_object* v_modifiers_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Lean_Elab_expandDeclId(v_currNamespace_3362_, v_currLevelNames_3363_, v_declId_3364_, v_modifiers_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_);
lean_dec(v_a_3371_);
lean_dec_ref(v_a_3370_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
lean_dec_ref(v_modifiers_3365_);
lean_dec(v_declId_3364_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(lean_object* v_00_u03b1_3374_, lean_object* v_u_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___x_3383_; 
v___x_3383_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___boxed(lean_object* v_00_u03b1_3384_, lean_object* v_u_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(v_00_u03b1_3384_, v_u_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(lean_object* v_00_u03b1_3394_, lean_object* v_msg_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3404_, lean_object* v_msg_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(v_00_u03b1_3404_, v_msg_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(lean_object* v_msgData_3414_, lean_object* v_macroStack_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_3414_, v_macroStack_3415_, v___y_3420_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_3424_, lean_object* v_macroStack_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(v_msgData_3424_, v_macroStack_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(lean_object* v_t_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_3434_, v___y_3440_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___boxed(lean_object* v_t_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(v_t_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(lean_object* v_env_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_3452_, v___y_3456_, v___y_3458_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___boxed(lean_object* v_env_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
lean_object* v_res_3469_; 
v_res_3469_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(v_env_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(lean_object* v_00_u03b1_3470_, lean_object* v_env_3471_, lean_object* v_x_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_3471_, v_x_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3481_, lean_object* v_env_3482_, lean_object* v_x_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(v_00_u03b1_3481_, v_env_3482_, v_x_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(lean_object* v_00_u03b1_3492_, lean_object* v_constName_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___boxed(lean_object* v_00_u03b1_3502_, lean_object* v_constName_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(v_00_u03b1_3502_, v_constName_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(lean_object* v_00_u03b1_3512_, lean_object* v_ref_3513_, lean_object* v_constName_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v___x_3522_; 
v___x_3522_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_3513_, v_constName_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___boxed(lean_object* v_00_u03b1_3523_, lean_object* v_ref_3524_, lean_object* v_constName_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(v_00_u03b1_3523_, v_ref_3524_, v_constName_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v_ref_3524_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(lean_object* v_00_u03b1_3534_, lean_object* v_ref_3535_, lean_object* v_msg_3536_, lean_object* v_declHint_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_3535_, v_msg_3536_, v_declHint_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___boxed(lean_object* v_00_u03b1_3546_, lean_object* v_ref_3547_, lean_object* v_msg_3548_, lean_object* v_declHint_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(v_00_u03b1_3546_, v_ref_3547_, v_msg_3548_, v_declHint_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v_ref_3547_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(lean_object* v_msg_3558_, lean_object* v_declHint_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
lean_object* v___x_3567_; 
v___x_3567_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_3558_, v_declHint_3559_, v___y_3565_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___boxed(lean_object* v_msg_3568_, lean_object* v_declHint_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(v_msg_3568_, v_declHint_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(lean_object* v_00_u03b1_3578_, lean_object* v_ref_3579_, lean_object* v_msg_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_3579_, v_msg_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___boxed(lean_object* v_00_u03b1_3589_, lean_object* v_ref_3590_, lean_object* v_msg_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(v_00_u03b1_3589_, v_ref_3590_, v_msg_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v_ref_3590_);
return v_res_3599_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(lean_object* v_x_3603_){
_start:
{
lean_object* v_name_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; 
v_name_3604_ = lean_ctor_get(v_x_3603_, 0);
v___x_3605_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__1));
v___x_3606_ = lean_name_eq(v_name_3604_, v___x_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___boxed(lean_object* v_x_3607_){
_start:
{
uint8_t v_res_3608_; lean_object* v_r_3609_; 
v_res_3608_ = l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(v_x_3607_);
lean_dec_ref(v_x_3607_);
v_r_3609_ = lean_box(v_res_3608_);
return v_r_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__1(lean_object* v_ctx_3610_){
_start:
{
lean_object* v_declName_x3f_3611_; lean_object* v_macroStack_3612_; uint8_t v_mayPostpone_3613_; uint8_t v_errToSorry_3614_; lean_object* v_autoBoundImplicitContext_3615_; lean_object* v_autoBoundImplicitForbidden_3616_; lean_object* v_sectionVars_3617_; lean_object* v_sectionFVars_3618_; uint8_t v_implicitLambda_3619_; uint8_t v_heedElabAsElim_3620_; uint8_t v_isNoncomputableSection_3621_; uint8_t v_isMetaSection_3622_; uint8_t v_ignoreTCFailures_3623_; uint8_t v_inPattern_3624_; lean_object* v_tacSnap_x3f_3625_; uint8_t v_saveRecAppSyntax_3626_; uint8_t v_holesAsSyntheticOpaque_3627_; lean_object* v_fixedTermElabs_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3636_; 
v_declName_x3f_3611_ = lean_ctor_get(v_ctx_3610_, 0);
v_macroStack_3612_ = lean_ctor_get(v_ctx_3610_, 1);
v_mayPostpone_3613_ = lean_ctor_get_uint8(v_ctx_3610_, sizeof(void*)*8);
v_errToSorry_3614_ = lean_ctor_get_uint8(v_ctx_3610_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_3615_ = lean_ctor_get(v_ctx_3610_, 2);
v_autoBoundImplicitForbidden_3616_ = lean_ctor_get(v_ctx_3610_, 3);
v_sectionVars_3617_ = lean_ctor_get(v_ctx_3610_, 4);
v_sectionFVars_3618_ = lean_ctor_get(v_ctx_3610_, 5);
v_implicitLambda_3619_ = lean_ctor_get_uint8(v_ctx_3610_, sizeof(void*)*8 + 2);
v_heedElabAsElim_3620_ = lean_ctor_get_uint8(v_ctx_3610_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_3621_ = lean_ctor_get_uint8(v_ctx_3610_, sizeof(void*)*8 + 4);
v_isMetaSection_3622_ = lean_ctor_get_uint8(v_ctx_3610_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_3623_ = lean_ctor_get_uint8(v_ctx_3610_, sizeof(void*)*8 + 6);
v_inPattern_3624_ = lean_ctor_get_uint8(v_ctx_3610_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_3625_ = lean_ctor_get(v_ctx_3610_, 6);
v_saveRecAppSyntax_3626_ = lean_ctor_get_uint8(v_ctx_3610_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_3627_ = lean_ctor_get_uint8(v_ctx_3610_, sizeof(void*)*8 + 9);
v_fixedTermElabs_3628_ = lean_ctor_get(v_ctx_3610_, 7);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_ctx_3610_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3630_ = v_ctx_3610_;
v_isShared_3631_ = v_isSharedCheck_3636_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_fixedTermElabs_3628_);
lean_inc(v_tacSnap_x3f_3625_);
lean_inc(v_sectionFVars_3618_);
lean_inc(v_sectionVars_3617_);
lean_inc(v_autoBoundImplicitForbidden_3616_);
lean_inc(v_autoBoundImplicitContext_3615_);
lean_inc(v_macroStack_3612_);
lean_inc(v_declName_x3f_3611_);
lean_dec(v_ctx_3610_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3636_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
uint8_t v___x_3632_; lean_object* v___x_3634_; 
v___x_3632_ = 0;
if (v_isShared_3631_ == 0)
{
v___x_3634_ = v___x_3630_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_declName_x3f_3611_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_macroStack_3612_);
lean_ctor_set(v_reuseFailAlloc_3635_, 2, v_autoBoundImplicitContext_3615_);
lean_ctor_set(v_reuseFailAlloc_3635_, 3, v_autoBoundImplicitForbidden_3616_);
lean_ctor_set(v_reuseFailAlloc_3635_, 4, v_sectionVars_3617_);
lean_ctor_set(v_reuseFailAlloc_3635_, 5, v_sectionFVars_3618_);
lean_ctor_set(v_reuseFailAlloc_3635_, 6, v_tacSnap_x3f_3625_);
lean_ctor_set(v_reuseFailAlloc_3635_, 7, v_fixedTermElabs_3628_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*8, v_mayPostpone_3613_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*8 + 1, v_errToSorry_3614_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*8 + 2, v_implicitLambda_3619_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*8 + 3, v_heedElabAsElim_3620_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*8 + 4, v_isNoncomputableSection_3621_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*8 + 5, v_isMetaSection_3622_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*8 + 6, v_ignoreTCFailures_3623_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*8 + 7, v_inPattern_3624_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_3626_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_3627_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
lean_ctor_set_uint8(v___x_3634_, sizeof(void*)*8 + 10, v___x_3632_);
return v___x_3634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg(lean_object* v_inst_3658_, lean_object* v_attrs_3659_, lean_object* v_a_3660_){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; uint8_t v___x_3664_; 
v___x_3661_ = lean_unsigned_to_nat(0u);
v___x_3662_ = lean_array_get_size(v_attrs_3659_);
v___x_3663_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9));
v___x_3664_ = lean_nat_dec_lt(v___x_3661_, v___x_3662_);
if (v___x_3664_ == 0)
{
lean_dec_ref(v_attrs_3659_);
lean_dec(v_inst_3658_);
return v_a_3660_;
}
else
{
if (v___x_3664_ == 0)
{
lean_dec_ref(v_attrs_3659_);
lean_dec(v_inst_3658_);
return v_a_3660_;
}
else
{
lean_object* v___f_3665_; size_t v___x_3666_; size_t v___x_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
v___f_3665_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10));
v___x_3666_ = ((size_t)0ULL);
v___x_3667_ = lean_usize_of_nat(v___x_3662_);
v___x_3668_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_3663_, v___f_3665_, v_attrs_3659_, v___x_3666_, v___x_3667_);
v___x_3669_ = lean_unbox(v___x_3668_);
lean_dec(v___x_3668_);
if (v___x_3669_ == 0)
{
lean_dec(v_inst_3658_);
return v_a_3660_;
}
else
{
lean_object* v___f_3670_; lean_object* v___x_3671_; 
v___f_3670_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11));
v___x_3671_ = lean_apply_3(v_inst_3658_, lean_box(0), v___f_3670_, v_a_3660_);
return v___x_3671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs(lean_object* v_m_3672_, lean_object* v_00_u03b1_3673_, lean_object* v_inst_3674_, lean_object* v_attrs_3675_, lean_object* v_a_3676_){
_start:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; uint8_t v___x_3680_; 
v___x_3677_ = lean_unsigned_to_nat(0u);
v___x_3678_ = lean_array_get_size(v_attrs_3675_);
v___x_3679_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9));
v___x_3680_ = lean_nat_dec_lt(v___x_3677_, v___x_3678_);
if (v___x_3680_ == 0)
{
lean_dec_ref(v_attrs_3675_);
lean_dec(v_inst_3674_);
return v_a_3676_;
}
else
{
if (v___x_3680_ == 0)
{
lean_dec_ref(v_attrs_3675_);
lean_dec(v_inst_3674_);
return v_a_3676_;
}
else
{
lean_object* v___f_3681_; size_t v___x_3682_; size_t v___x_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; 
v___f_3681_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10));
v___x_3682_ = ((size_t)0ULL);
v___x_3683_ = lean_usize_of_nat(v___x_3678_);
v___x_3684_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_3679_, v___f_3681_, v_attrs_3675_, v___x_3682_, v___x_3683_);
v___x_3685_ = lean_unbox(v___x_3684_);
lean_dec(v___x_3684_);
if (v___x_3685_ == 0)
{
lean_dec(v_inst_3674_);
return v_a_3676_;
}
else
{
lean_object* v___f_3686_; lean_object* v___x_3687_; 
v___f_3686_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11));
v___x_3687_ = lean_apply_3(v_inst_3674_, lean_box(0), v___f_3686_, v_a_3676_);
return v___x_3687_;
}
}
}
}
}
lean_object* runtime_initialize_Lean_DocString_Add(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeclModifiers(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
