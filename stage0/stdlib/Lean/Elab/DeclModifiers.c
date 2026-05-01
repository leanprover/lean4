// Lean compiler output
// Module: Lean.Elab.DeclModifiers
// Imports: public import Lean.DocString.Add public import Lean.Linter.Basic import Lean.Linter.EnvLinter.Nolint meta import Lean.Parser.Command
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
lean_object* lean_private_to_user_name(lean_object*);
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
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Linter_logLintIf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
extern lean_object* l_Lean_doc_verso;
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__33 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__33_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__34 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__34_value;
static lean_once_cell_t l_Lean_Elab_instToFormatModifiers___lam__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__35;
static lean_once_cell_t l_Lean_Elab_instToFormatModifiers___lam__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__36;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__33_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__37 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__37_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__34_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__38 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__38_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-/"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__39 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__39_value;
static const lean_ctor_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__39_value)}};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__40 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__40_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__41 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__41_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__1___closed__42 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__42_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2___boxed(lean_object**);
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
v___x_168_ = lean_private_to_user_name(v_declName_160_);
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
lean_dec_ref(v___x_168_);
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
v___x_284_ = lean_private_to_user_name(v_declName_276_);
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
lean_dec_ref(v___x_284_);
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
uint8_t v___y_459_; uint8_t v_isExporting_462_; 
v_isExporting_462_ = lean_ctor_get_uint8(v_env_456_, sizeof(void*)*8);
if (v_isExporting_462_ == 0)
{
lean_object* v___x_463_; uint8_t v_isModule_464_; 
v___x_463_ = l_Lean_Environment_header(v_env_456_);
v_isModule_464_ = lean_ctor_get_uint8(v___x_463_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_463_);
if (v_isModule_464_ == 0)
{
uint8_t v___x_465_; 
v___x_465_ = 1;
v___y_459_ = v___x_465_;
goto v___jp_458_;
}
else
{
uint8_t v___x_466_; 
v___x_466_ = l_Lean_Elab_Visibility_isPublic(v_v_457_);
return v___x_466_;
}
}
else
{
v___y_459_ = v_isExporting_462_;
goto v___jp_458_;
}
v___jp_458_:
{
uint8_t v___x_460_; 
v___x_460_ = l_Lean_Elab_Visibility_isPrivate(v_v_457_);
if (v___x_460_ == 0)
{
return v___y_459_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isInferredPublic___boxed(lean_object* v_env_467_, lean_object* v_v_468_){
_start:
{
uint8_t v_v_boxed_469_; uint8_t v_res_470_; lean_object* v_r_471_; 
v_v_boxed_469_ = lean_unbox(v_v_468_);
v_res_470_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_467_, v_v_boxed_469_);
lean_dec_ref(v_env_467_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__0(lean_object* v_toPure_472_, lean_object* v_____r_473_){
_start:
{
uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = 2;
v___x_475_ = lean_box(v___x_474_);
v___x_476_ = lean_apply_2(v_toPure_472_, lean_box(0), v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__2(lean_object* v_toPure_477_, lean_object* v_____r_478_){
_start:
{
uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = 1;
v___x_480_ = lean_box(v___x_479_);
v___x_481_ = lean_apply_2(v_toPure_477_, lean_box(0), v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__0));
v___x_484_ = l_Lean_stringToMessageData(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__2));
v___x_487_ = l_Lean_stringToMessageData(v___x_486_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__10));
v___x_504_ = l_Lean_stringToMessageData(v___x_503_);
return v___x_504_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__12));
v___x_507_ = l_Lean_stringToMessageData(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3(lean_object* v_vis_x3f_508_, lean_object* v_toPure_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_toBind_516_, lean_object* v___f_517_, lean_object* v___f_518_, lean_object* v___f_519_, lean_object* v___f_520_, lean_object* v_env_521_){
_start:
{
if (lean_obj_tag(v_vis_x3f_508_) == 0)
{
uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v___f_520_);
lean_dec(v___f_519_);
lean_dec(v___f_518_);
lean_dec(v___f_517_);
lean_dec(v_toBind_516_);
lean_dec_ref(v_inst_515_);
lean_dec(v_inst_514_);
lean_dec(v_inst_513_);
lean_dec_ref(v_inst_512_);
lean_dec_ref(v_inst_511_);
lean_dec_ref(v_inst_510_);
v___x_525_ = 0;
v___x_526_ = lean_box(v___x_525_);
v___x_527_ = lean_apply_2(v_toPure_509_, lean_box(0), v___x_526_);
return v___x_527_;
}
else
{
lean_object* v_val_528_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___x_552_; uint8_t v___x_553_; 
lean_dec(v_toPure_509_);
v_val_528_ = lean_ctor_get(v_vis_x3f_508_, 0);
lean_inc_n(v_val_528_, 2);
lean_dec_ref(v_vis_x3f_508_);
v___x_552_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8));
v___x_553_ = l_Lean_Syntax_isOfKind(v_val_528_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; uint8_t v___x_555_; 
lean_dec(v___f_520_);
lean_dec(v___f_519_);
v___x_554_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9));
lean_inc(v_val_528_);
v___x_555_ = l_Lean_Syntax_isOfKind(v_val_528_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec(v___f_518_);
lean_dec(v___f_517_);
lean_dec(v_toBind_516_);
lean_dec_ref(v_inst_515_);
lean_dec(v_inst_514_);
lean_dec(v_inst_513_);
lean_dec_ref(v_inst_512_);
v___x_556_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11);
v___x_557_ = l_Lean_throwErrorAt___redArg(v_inst_510_, v_inst_511_, v_val_528_, v___x_556_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; 
lean_dec_ref(v_inst_511_);
v___x_558_ = l_Lean_Syntax_getHeadInfo(v_val_528_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_dec_ref(v___x_558_);
goto v___jp_546_;
}
else
{
lean_dec(v___x_558_);
if (v___x_553_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v_val_528_);
lean_dec(v___f_517_);
lean_dec(v_toBind_516_);
lean_dec_ref(v_inst_515_);
lean_dec(v_inst_514_);
lean_dec(v_inst_513_);
lean_dec_ref(v_inst_512_);
lean_dec_ref(v_inst_510_);
v___x_559_ = lean_box(0);
v___x_560_ = lean_apply_1(v___f_518_, v___x_559_);
return v___x_560_;
}
else
{
goto v___jp_546_;
}
}
}
}
else
{
lean_object* v___x_561_; 
lean_dec(v___f_518_);
lean_dec(v___f_517_);
lean_dec_ref(v_inst_511_);
v___x_561_ = l_Lean_Syntax_getHeadInfo(v_val_528_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_562_; uint8_t v_isModule_563_; 
lean_dec_ref(v___x_561_);
v___x_562_ = l_Lean_Environment_header(v_env_521_);
v_isModule_563_ = lean_ctor_get_uint8(v___x_562_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_562_);
if (v_isModule_563_ == 0)
{
lean_dec(v_val_528_);
lean_dec(v___f_520_);
lean_dec(v_toBind_516_);
lean_dec_ref(v_inst_515_);
lean_dec(v_inst_514_);
lean_dec(v_inst_513_);
lean_dec_ref(v_inst_512_);
lean_dec_ref(v_inst_510_);
goto v___jp_522_;
}
else
{
uint8_t v_isExporting_564_; 
v_isExporting_564_ = lean_ctor_get_uint8(v_env_521_, sizeof(void*)*8);
if (v_isExporting_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v___f_519_);
v___x_565_ = l_Lean_linter_redundantVisibility;
v___x_566_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13);
v___x_567_ = l_Lean_Linter_logLintIf___redArg(v_inst_510_, v_inst_512_, v_inst_513_, v_inst_514_, v_inst_515_, v___x_565_, v_val_528_, v___x_566_);
v___x_568_ = lean_apply_4(v_toBind_516_, lean_box(0), lean_box(0), v___x_567_, v___f_520_);
return v___x_568_;
}
else
{
lean_dec(v_val_528_);
lean_dec(v___f_520_);
lean_dec(v_toBind_516_);
lean_dec_ref(v_inst_515_);
lean_dec(v_inst_514_);
lean_dec(v_inst_513_);
lean_dec_ref(v_inst_512_);
lean_dec_ref(v_inst_510_);
goto v___jp_522_;
}
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v___x_561_);
lean_dec(v_val_528_);
lean_dec(v___f_520_);
lean_dec(v_toBind_516_);
lean_dec_ref(v_inst_515_);
lean_dec(v_inst_514_);
lean_dec(v_inst_513_);
lean_dec_ref(v_inst_512_);
lean_dec_ref(v_inst_510_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_apply_1(v___f_519_, v___x_569_);
return v___x_570_;
}
}
v___jp_529_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
lean_inc_ref(v___y_532_);
v___x_533_ = l_Lean_stringToMessageData(v___y_532_);
lean_inc_ref(v___y_530_);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___y_530_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
lean_inc_ref(v___y_531_);
v___x_537_ = l_Lean_Linter_logLintIf___redArg(v_inst_510_, v_inst_512_, v_inst_513_, v_inst_514_, v_inst_515_, v___y_531_, v_val_528_, v___x_536_);
v___x_538_ = lean_apply_4(v_toBind_516_, lean_box(0), lean_box(0), v___x_537_, v___f_517_);
return v___x_538_;
}
v___jp_539_:
{
lean_object* v___x_540_; uint8_t v_isModule_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_540_ = l_Lean_Environment_header(v_env_521_);
v_isModule_541_ = lean_ctor_get_uint8(v___x_540_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_540_);
v___x_542_ = l_Lean_linter_redundantVisibility;
v___x_543_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3);
if (v_isModule_541_ == 0)
{
lean_object* v___x_544_; 
v___x_544_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4));
v___y_530_ = v___x_543_;
v___y_531_ = v___x_542_;
v___y_532_ = v___x_544_;
goto v___jp_529_;
}
else
{
lean_object* v___x_545_; 
v___x_545_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__5));
v___y_530_ = v___x_543_;
v___y_531_ = v___x_542_;
v___y_532_ = v___x_545_;
goto v___jp_529_;
}
}
v___jp_546_:
{
uint8_t v_isExporting_547_; 
v_isExporting_547_ = lean_ctor_get_uint8(v_env_521_, sizeof(void*)*8);
if (v_isExporting_547_ == 0)
{
lean_object* v___x_548_; uint8_t v_isModule_549_; 
v___x_548_ = l_Lean_Environment_header(v_env_521_);
v_isModule_549_ = lean_ctor_get_uint8(v___x_548_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_548_);
if (v_isModule_549_ == 0)
{
lean_dec(v___f_518_);
goto v___jp_539_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v_val_528_);
lean_dec(v___f_517_);
lean_dec(v_toBind_516_);
lean_dec_ref(v_inst_515_);
lean_dec(v_inst_514_);
lean_dec(v_inst_513_);
lean_dec_ref(v_inst_512_);
lean_dec_ref(v_inst_510_);
v___x_550_ = lean_box(0);
v___x_551_ = lean_apply_1(v___f_518_, v___x_550_);
return v___x_551_;
}
}
else
{
lean_dec(v___f_518_);
goto v___jp_539_;
}
}
}
v___jp_522_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_box(0);
v___x_524_ = lean_apply_1(v___f_519_, v___x_523_);
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___boxed(lean_object* v_vis_x3f_571_, lean_object* v_toPure_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_toBind_579_, lean_object* v___f_580_, lean_object* v___f_581_, lean_object* v___f_582_, lean_object* v___f_583_, lean_object* v_env_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Elab_elabVisibility___redArg___lam__3(v_vis_x3f_571_, v_toPure_572_, v_inst_573_, v_inst_574_, v_inst_575_, v_inst_576_, v_inst_577_, v_inst_578_, v_toBind_579_, v___f_580_, v___f_581_, v___f_582_, v___f_583_, v_env_584_);
lean_dec_ref(v_env_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg(lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_vis_x3f_592_){
_start:
{
lean_object* v_toApplicative_593_; lean_object* v_toBind_594_; lean_object* v_getEnv_595_; lean_object* v_toPure_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___x_602_; 
v_toApplicative_593_ = lean_ctor_get(v_inst_586_, 0);
v_toBind_594_ = lean_ctor_get(v_inst_586_, 1);
lean_inc_n(v_toBind_594_, 2);
v_getEnv_595_ = lean_ctor_get(v_inst_588_, 0);
lean_inc(v_getEnv_595_);
v_toPure_596_ = lean_ctor_get(v_toApplicative_593_, 1);
lean_inc_n(v_toPure_596_, 3);
v___f_597_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__0), 2, 1);
lean_closure_set(v___f_597_, 0, v_toPure_596_);
lean_inc_ref(v___f_597_);
v___f_598_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_598_, 0, v___f_597_);
v___f_599_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__2), 2, 1);
lean_closure_set(v___f_599_, 0, v_toPure_596_);
lean_inc_ref(v___f_599_);
v___f_600_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_600_, 0, v___f_599_);
v___f_601_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__3___boxed), 14, 13);
lean_closure_set(v___f_601_, 0, v_vis_x3f_592_);
lean_closure_set(v___f_601_, 1, v_toPure_596_);
lean_closure_set(v___f_601_, 2, v_inst_586_);
lean_closure_set(v___f_601_, 3, v_inst_587_);
lean_closure_set(v___f_601_, 4, v_inst_590_);
lean_closure_set(v___f_601_, 5, v_inst_591_);
lean_closure_set(v___f_601_, 6, v_inst_589_);
lean_closure_set(v___f_601_, 7, v_inst_588_);
lean_closure_set(v___f_601_, 8, v_toBind_594_);
lean_closure_set(v___f_601_, 9, v___f_598_);
lean_closure_set(v___f_601_, 10, v___f_597_);
lean_closure_set(v___f_601_, 11, v___f_599_);
lean_closure_set(v___f_601_, 12, v___f_600_);
v___x_602_ = lean_apply_4(v_toBind_594_, lean_box(0), lean_box(0), v_getEnv_595_, v___f_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility(lean_object* v_m_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_vis_x3f_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Elab_elabVisibility___redArg(v_inst_604_, v_inst_605_, v_inst_606_, v_inst_607_, v_inst_608_, v_inst_609_, v_vis_x3f_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx(uint8_t v_x_612_){
_start:
{
switch(v_x_612_)
{
case 0:
{
lean_object* v___x_613_; 
v___x_613_ = lean_unsigned_to_nat(0u);
return v___x_613_;
}
case 1:
{
lean_object* v___x_614_; 
v___x_614_ = lean_unsigned_to_nat(1u);
return v___x_614_;
}
default: 
{
lean_object* v___x_615_; 
v___x_615_ = lean_unsigned_to_nat(2u);
return v___x_615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___boxed(lean_object* v_x_616_){
_start:
{
uint8_t v_x_boxed_617_; lean_object* v_res_618_; 
v_x_boxed_617_ = lean_unbox(v_x_616_);
v_res_618_ = l_Lean_Elab_RecKind_ctorIdx(v_x_boxed_617_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx(uint8_t v_x_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_Elab_RecKind_ctorIdx(v_x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx___boxed(lean_object* v_x_621_){
_start:
{
uint8_t v_x_4__boxed_622_; lean_object* v_res_623_; 
v_x_4__boxed_622_ = lean_unbox(v_x_621_);
v_res_623_ = l_Lean_Elab_RecKind_toCtorIdx(v_x_4__boxed_622_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg(lean_object* v_k_624_){
_start:
{
lean_inc(v_k_624_);
return v_k_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg___boxed(lean_object* v_k_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Elab_RecKind_ctorElim___redArg(v_k_625_);
lean_dec(v_k_625_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim(lean_object* v_motive_627_, lean_object* v_ctorIdx_628_, uint8_t v_t_629_, lean_object* v_h_630_, lean_object* v_k_631_){
_start:
{
lean_inc(v_k_631_);
return v_k_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___boxed(lean_object* v_motive_632_, lean_object* v_ctorIdx_633_, lean_object* v_t_634_, lean_object* v_h_635_, lean_object* v_k_636_){
_start:
{
uint8_t v_t_boxed_637_; lean_object* v_res_638_; 
v_t_boxed_637_ = lean_unbox(v_t_634_);
v_res_638_ = l_Lean_Elab_RecKind_ctorElim(v_motive_632_, v_ctorIdx_633_, v_t_boxed_637_, v_h_635_, v_k_636_);
lean_dec(v_k_636_);
lean_dec(v_ctorIdx_633_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg(lean_object* v_partial_639_){
_start:
{
lean_inc(v_partial_639_);
return v_partial_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg___boxed(lean_object* v_partial_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Elab_RecKind_partial_elim___redArg(v_partial_640_);
lean_dec(v_partial_640_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim(lean_object* v_motive_642_, uint8_t v_t_643_, lean_object* v_h_644_, lean_object* v_partial_645_){
_start:
{
lean_inc(v_partial_645_);
return v_partial_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___boxed(lean_object* v_motive_646_, lean_object* v_t_647_, lean_object* v_h_648_, lean_object* v_partial_649_){
_start:
{
uint8_t v_t_boxed_650_; lean_object* v_res_651_; 
v_t_boxed_650_ = lean_unbox(v_t_647_);
v_res_651_ = l_Lean_Elab_RecKind_partial_elim(v_motive_646_, v_t_boxed_650_, v_h_648_, v_partial_649_);
lean_dec(v_partial_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg(lean_object* v_nonrec_652_){
_start:
{
lean_inc(v_nonrec_652_);
return v_nonrec_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg___boxed(lean_object* v_nonrec_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Elab_RecKind_nonrec_elim___redArg(v_nonrec_653_);
lean_dec(v_nonrec_653_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim(lean_object* v_motive_655_, uint8_t v_t_656_, lean_object* v_h_657_, lean_object* v_nonrec_658_){
_start:
{
lean_inc(v_nonrec_658_);
return v_nonrec_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___boxed(lean_object* v_motive_659_, lean_object* v_t_660_, lean_object* v_h_661_, lean_object* v_nonrec_662_){
_start:
{
uint8_t v_t_boxed_663_; lean_object* v_res_664_; 
v_t_boxed_663_ = lean_unbox(v_t_660_);
v_res_664_ = l_Lean_Elab_RecKind_nonrec_elim(v_motive_659_, v_t_boxed_663_, v_h_661_, v_nonrec_662_);
lean_dec(v_nonrec_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg(lean_object* v_default_665_){
_start:
{
lean_inc(v_default_665_);
return v_default_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg___boxed(lean_object* v_default_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Elab_RecKind_default_elim___redArg(v_default_666_);
lean_dec(v_default_666_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim(lean_object* v_motive_668_, uint8_t v_t_669_, lean_object* v_h_670_, lean_object* v_default_671_){
_start:
{
lean_inc(v_default_671_);
return v_default_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___boxed(lean_object* v_motive_672_, lean_object* v_t_673_, lean_object* v_h_674_, lean_object* v_default_675_){
_start:
{
uint8_t v_t_boxed_676_; lean_object* v_res_677_; 
v_t_boxed_676_ = lean_unbox(v_t_673_);
v_res_677_ = l_Lean_Elab_RecKind_default_elim(v_motive_672_, v_t_boxed_676_, v_h_674_, v_default_675_);
lean_dec(v_default_675_);
return v_res_677_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind_default(void){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = 0;
return v___x_678_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind(void){
_start:
{
uint8_t v___x_679_; 
v___x_679_ = 0;
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx(uint8_t v_x_680_){
_start:
{
switch(v_x_680_)
{
case 0:
{
lean_object* v___x_681_; 
v___x_681_ = lean_unsigned_to_nat(0u);
return v___x_681_;
}
case 1:
{
lean_object* v___x_682_; 
v___x_682_ = lean_unsigned_to_nat(1u);
return v___x_682_;
}
default: 
{
lean_object* v___x_683_; 
v___x_683_ = lean_unsigned_to_nat(2u);
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___boxed(lean_object* v_x_684_){
_start:
{
uint8_t v_x_boxed_685_; lean_object* v_res_686_; 
v_x_boxed_685_ = lean_unbox(v_x_684_);
v_res_686_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_boxed_685_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_toCtorIdx(uint8_t v_x_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_toCtorIdx___boxed(lean_object* v_x_689_){
_start:
{
uint8_t v_x_4__boxed_690_; lean_object* v_res_691_; 
v_x_4__boxed_690_ = lean_unbox(v_x_689_);
v_res_691_ = l_Lean_Elab_ComputeKind_toCtorIdx(v_x_4__boxed_690_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg(lean_object* v_k_692_){
_start:
{
lean_inc(v_k_692_);
return v_k_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg___boxed(lean_object* v_k_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Elab_ComputeKind_ctorElim___redArg(v_k_693_);
lean_dec(v_k_693_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim(lean_object* v_motive_695_, lean_object* v_ctorIdx_696_, uint8_t v_t_697_, lean_object* v_h_698_, lean_object* v_k_699_){
_start:
{
lean_inc(v_k_699_);
return v_k_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___boxed(lean_object* v_motive_700_, lean_object* v_ctorIdx_701_, lean_object* v_t_702_, lean_object* v_h_703_, lean_object* v_k_704_){
_start:
{
uint8_t v_t_boxed_705_; lean_object* v_res_706_; 
v_t_boxed_705_ = lean_unbox(v_t_702_);
v_res_706_ = l_Lean_Elab_ComputeKind_ctorElim(v_motive_700_, v_ctorIdx_701_, v_t_boxed_705_, v_h_703_, v_k_704_);
lean_dec(v_k_704_);
lean_dec(v_ctorIdx_701_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg(lean_object* v_regular_707_){
_start:
{
lean_inc(v_regular_707_);
return v_regular_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg___boxed(lean_object* v_regular_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Elab_ComputeKind_regular_elim___redArg(v_regular_708_);
lean_dec(v_regular_708_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim(lean_object* v_motive_710_, uint8_t v_t_711_, lean_object* v_h_712_, lean_object* v_regular_713_){
_start:
{
lean_inc(v_regular_713_);
return v_regular_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___boxed(lean_object* v_motive_714_, lean_object* v_t_715_, lean_object* v_h_716_, lean_object* v_regular_717_){
_start:
{
uint8_t v_t_boxed_718_; lean_object* v_res_719_; 
v_t_boxed_718_ = lean_unbox(v_t_715_);
v_res_719_ = l_Lean_Elab_ComputeKind_regular_elim(v_motive_714_, v_t_boxed_718_, v_h_716_, v_regular_717_);
lean_dec(v_regular_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg(lean_object* v_meta_720_){
_start:
{
lean_inc(v_meta_720_);
return v_meta_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg___boxed(lean_object* v_meta_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Elab_ComputeKind_meta_elim___redArg(v_meta_721_);
lean_dec(v_meta_721_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim(lean_object* v_motive_723_, uint8_t v_t_724_, lean_object* v_h_725_, lean_object* v_meta_726_){
_start:
{
lean_inc(v_meta_726_);
return v_meta_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___boxed(lean_object* v_motive_727_, lean_object* v_t_728_, lean_object* v_h_729_, lean_object* v_meta_730_){
_start:
{
uint8_t v_t_boxed_731_; lean_object* v_res_732_; 
v_t_boxed_731_ = lean_unbox(v_t_728_);
v_res_732_ = l_Lean_Elab_ComputeKind_meta_elim(v_motive_727_, v_t_boxed_731_, v_h_729_, v_meta_730_);
lean_dec(v_meta_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(lean_object* v_noncomputable_733_){
_start:
{
lean_inc(v_noncomputable_733_);
return v_noncomputable_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg___boxed(lean_object* v_noncomputable_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(v_noncomputable_734_);
lean_dec(v_noncomputable_734_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim(lean_object* v_motive_736_, uint8_t v_t_737_, lean_object* v_h_738_, lean_object* v_noncomputable_739_){
_start:
{
lean_inc(v_noncomputable_739_);
return v_noncomputable_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___boxed(lean_object* v_motive_740_, lean_object* v_t_741_, lean_object* v_h_742_, lean_object* v_noncomputable_743_){
_start:
{
uint8_t v_t_boxed_744_; lean_object* v_res_745_; 
v_t_boxed_744_ = lean_unbox(v_t_741_);
v_res_745_ = l_Lean_Elab_ComputeKind_noncomputable_elim(v_motive_740_, v_t_boxed_744_, v_h_742_, v_noncomputable_743_);
lean_dec(v_noncomputable_743_);
return v_res_745_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind_default(void){
_start:
{
uint8_t v___x_746_; 
v___x_746_ = 0;
return v___x_746_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind(void){
_start:
{
uint8_t v___x_747_; 
v___x_747_ = 0;
return v___x_747_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqComputeKind_beq(uint8_t v_x_748_, uint8_t v_y_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_748_);
v___x_751_ = l_Lean_Elab_ComputeKind_ctorIdx(v_y_749_);
v___x_752_ = lean_nat_dec_eq(v___x_750_, v___x_751_);
lean_dec(v___x_751_);
lean_dec(v___x_750_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqComputeKind_beq___boxed(lean_object* v_x_753_, lean_object* v_y_754_){
_start:
{
uint8_t v_x_17__boxed_755_; uint8_t v_y_18__boxed_756_; uint8_t v_res_757_; lean_object* v_r_758_; 
v_x_17__boxed_755_ = lean_unbox(v_x_753_);
v_y_18__boxed_756_ = lean_unbox(v_y_754_);
v_res_757_ = l_Lean_Elab_instBEqComputeKind_beq(v_x_17__boxed_755_, v_y_18__boxed_756_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
static lean_object* _init_l_Lean_Elab_instReprComputeKind_repr___closed__6(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_unsigned_to_nat(2u);
v___x_771_ = lean_nat_to_int(v___x_770_);
return v___x_771_;
}
}
static lean_object* _init_l_Lean_Elab_instReprComputeKind_repr___closed__7(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = lean_nat_to_int(v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprComputeKind_repr(uint8_t v_x_774_, lean_object* v_prec_775_){
_start:
{
lean_object* v___y_777_; lean_object* v___y_784_; lean_object* v___y_791_; 
switch(v_x_774_)
{
case 0:
{
lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(1024u);
v___x_798_ = lean_nat_dec_le(v___x_797_, v_prec_775_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
v___x_799_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_777_ = v___x_799_;
goto v___jp_776_;
}
else
{
lean_object* v___x_800_; 
v___x_800_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_777_ = v___x_800_;
goto v___jp_776_;
}
}
case 1:
{
lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_801_ = lean_unsigned_to_nat(1024u);
v___x_802_ = lean_nat_dec_le(v___x_801_, v_prec_775_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; 
v___x_803_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_784_ = v___x_803_;
goto v___jp_783_;
}
else
{
lean_object* v___x_804_; 
v___x_804_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_784_ = v___x_804_;
goto v___jp_783_;
}
}
default: 
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = lean_unsigned_to_nat(1024u);
v___x_806_ = lean_nat_dec_le(v___x_805_, v_prec_775_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
v___x_807_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_791_ = v___x_807_;
goto v___jp_790_;
}
else
{
lean_object* v___x_808_; 
v___x_808_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_791_ = v___x_808_;
goto v___jp_790_;
}
}
}
v___jp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_778_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__1));
lean_inc(v___y_777_);
v___x_779_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_779_, 0, v___y_777_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = 0;
v___x_781_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*1, v___x_780_);
v___x_782_ = l_Repr_addAppParen(v___x_781_, v_prec_775_);
return v___x_782_;
}
v___jp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_785_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__3));
lean_inc(v___y_784_);
v___x_786_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_786_, 0, v___y_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = 0;
v___x_788_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*1, v___x_787_);
v___x_789_ = l_Repr_addAppParen(v___x_788_, v_prec_775_);
return v___x_789_;
}
v___jp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_792_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__5));
lean_inc(v___y_791_);
v___x_793_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_793_, 0, v___y_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = 0;
v___x_795_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set_uint8(v___x_795_, sizeof(void*)*1, v___x_794_);
v___x_796_ = l_Repr_addAppParen(v___x_795_, v_prec_775_);
return v___x_796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprComputeKind_repr___boxed(lean_object* v_x_809_, lean_object* v_prec_810_){
_start:
{
uint8_t v_x_177__boxed_811_; lean_object* v_res_812_; 
v_x_177__boxed_811_ = lean_unbox(v_x_809_);
v_res_812_ = l_Lean_Elab_instReprComputeKind_repr(v_x_177__boxed_811_, v_prec_810_);
lean_dec(v_prec_810_);
return v_res_812_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object* v_m_827_){
_start:
{
uint8_t v_visibility_828_; uint8_t v___x_829_; 
v_visibility_828_ = lean_ctor_get_uint8(v_m_827_, sizeof(void*)*3);
v___x_829_ = l_Lean_Elab_Visibility_isPrivate(v_visibility_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPrivate___boxed(lean_object* v_m_830_){
_start:
{
uint8_t v_res_831_; lean_object* v_r_832_; 
v_res_831_ = l_Lean_Elab_Modifiers_isPrivate(v_m_830_);
lean_dec_ref(v_m_830_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPublic(lean_object* v_m_833_){
_start:
{
uint8_t v_visibility_834_; uint8_t v___x_835_; 
v_visibility_834_ = lean_ctor_get_uint8(v_m_833_, sizeof(void*)*3);
v___x_835_ = l_Lean_Elab_Visibility_isPublic(v_visibility_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPublic___boxed(lean_object* v_m_836_){
_start:
{
uint8_t v_res_837_; lean_object* v_r_838_; 
v_res_837_ = l_Lean_Elab_Modifiers_isPublic(v_m_836_);
lean_dec_ref(v_m_836_);
v_r_838_ = lean_box(v_res_837_);
return v_r_838_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isInferredPublic(lean_object* v_env_839_, lean_object* v_m_840_){
_start:
{
uint8_t v_visibility_841_; uint8_t v___x_842_; 
v_visibility_841_ = lean_ctor_get_uint8(v_m_840_, sizeof(void*)*3);
v___x_842_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_839_, v_visibility_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isInferredPublic___boxed(lean_object* v_env_843_, lean_object* v_m_844_){
_start:
{
uint8_t v_res_845_; lean_object* v_r_846_; 
v_res_845_ = l_Lean_Elab_Modifiers_isInferredPublic(v_env_843_, v_m_844_);
lean_dec_ref(v_m_844_);
lean_dec_ref(v_env_843_);
v_r_846_ = lean_box(v_res_845_);
return v_r_846_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object* v_x_847_){
_start:
{
uint8_t v_recKind_848_; 
v_recKind_848_ = lean_ctor_get_uint8(v_x_847_, sizeof(void*)*3 + 3);
if (v_recKind_848_ == 0)
{
uint8_t v___x_849_; 
v___x_849_ = 1;
return v___x_849_;
}
else
{
uint8_t v___x_850_; 
v___x_850_ = 0;
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPartial___boxed(lean_object* v_x_851_){
_start:
{
uint8_t v_res_852_; lean_object* v_r_853_; 
v_res_852_ = l_Lean_Elab_Modifiers_isPartial(v_x_851_);
lean_dec_ref(v_x_851_);
v_r_853_ = lean_box(v_res_852_);
return v_r_853_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNonrec(lean_object* v_x_854_){
_start:
{
uint8_t v_recKind_855_; 
v_recKind_855_ = lean_ctor_get_uint8(v_x_854_, sizeof(void*)*3 + 3);
if (v_recKind_855_ == 1)
{
uint8_t v___x_856_; 
v___x_856_ = 1;
return v___x_856_;
}
else
{
uint8_t v___x_857_; 
v___x_857_ = 0;
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNonrec___boxed(lean_object* v_x_858_){
_start:
{
uint8_t v_res_859_; lean_object* v_r_860_; 
v_res_859_ = l_Lean_Elab_Modifiers_isNonrec(v_x_858_);
lean_dec_ref(v_x_858_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isMeta(lean_object* v_m_861_){
_start:
{
uint8_t v_computeKind_862_; 
v_computeKind_862_ = lean_ctor_get_uint8(v_m_861_, sizeof(void*)*3 + 2);
if (v_computeKind_862_ == 1)
{
uint8_t v___x_863_; 
v___x_863_ = 1;
return v___x_863_;
}
else
{
uint8_t v___x_864_; 
v___x_864_ = 0;
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isMeta___boxed(lean_object* v_m_865_){
_start:
{
uint8_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l_Lean_Elab_Modifiers_isMeta(v_m_865_);
lean_dec_ref(v_m_865_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNoncomputable(lean_object* v_m_868_){
_start:
{
uint8_t v_computeKind_869_; 
v_computeKind_869_ = lean_ctor_get_uint8(v_m_868_, sizeof(void*)*3 + 2);
if (v_computeKind_869_ == 2)
{
uint8_t v___x_870_; 
v___x_870_ = 1;
return v___x_870_;
}
else
{
uint8_t v___x_871_; 
v___x_871_ = 0;
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNoncomputable___boxed(lean_object* v_m_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l_Lean_Elab_Modifiers_isNoncomputable(v_m_872_);
lean_dec_ref(v_m_872_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addAttr(lean_object* v_modifiers_875_, lean_object* v_attr_876_){
_start:
{
lean_object* v_stx_877_; lean_object* v_docString_x3f_878_; uint8_t v_visibility_879_; uint8_t v_isProtected_880_; uint8_t v_computeKind_881_; uint8_t v_recKind_882_; uint8_t v_isUnsafe_883_; lean_object* v_attrs_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_892_; 
v_stx_877_ = lean_ctor_get(v_modifiers_875_, 0);
v_docString_x3f_878_ = lean_ctor_get(v_modifiers_875_, 1);
v_visibility_879_ = lean_ctor_get_uint8(v_modifiers_875_, sizeof(void*)*3);
v_isProtected_880_ = lean_ctor_get_uint8(v_modifiers_875_, sizeof(void*)*3 + 1);
v_computeKind_881_ = lean_ctor_get_uint8(v_modifiers_875_, sizeof(void*)*3 + 2);
v_recKind_882_ = lean_ctor_get_uint8(v_modifiers_875_, sizeof(void*)*3 + 3);
v_isUnsafe_883_ = lean_ctor_get_uint8(v_modifiers_875_, sizeof(void*)*3 + 4);
v_attrs_884_ = lean_ctor_get(v_modifiers_875_, 2);
v_isSharedCheck_892_ = !lean_is_exclusive(v_modifiers_875_);
if (v_isSharedCheck_892_ == 0)
{
v___x_886_ = v_modifiers_875_;
v_isShared_887_ = v_isSharedCheck_892_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_attrs_884_);
lean_inc(v_docString_x3f_878_);
lean_inc(v_stx_877_);
lean_dec(v_modifiers_875_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_892_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_888_ = lean_array_push(v_attrs_884_, v_attr_876_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 2, v___x_888_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_stx_877_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_docString_x3f_878_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v___x_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, sizeof(void*)*3, v_visibility_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, sizeof(void*)*3 + 1, v_isProtected_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, sizeof(void*)*3 + 2, v_computeKind_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, sizeof(void*)*3 + 3, v_recKind_882_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, sizeof(void*)*3 + 4, v_isUnsafe_883_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addFirstAttr(lean_object* v_modifiers_893_, lean_object* v_attr_894_){
_start:
{
lean_object* v_stx_895_; lean_object* v_docString_x3f_896_; uint8_t v_visibility_897_; uint8_t v_isProtected_898_; uint8_t v_computeKind_899_; uint8_t v_recKind_900_; uint8_t v_isUnsafe_901_; lean_object* v_attrs_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_913_; 
v_stx_895_ = lean_ctor_get(v_modifiers_893_, 0);
v_docString_x3f_896_ = lean_ctor_get(v_modifiers_893_, 1);
v_visibility_897_ = lean_ctor_get_uint8(v_modifiers_893_, sizeof(void*)*3);
v_isProtected_898_ = lean_ctor_get_uint8(v_modifiers_893_, sizeof(void*)*3 + 1);
v_computeKind_899_ = lean_ctor_get_uint8(v_modifiers_893_, sizeof(void*)*3 + 2);
v_recKind_900_ = lean_ctor_get_uint8(v_modifiers_893_, sizeof(void*)*3 + 3);
v_isUnsafe_901_ = lean_ctor_get_uint8(v_modifiers_893_, sizeof(void*)*3 + 4);
v_attrs_902_ = lean_ctor_get(v_modifiers_893_, 2);
v_isSharedCheck_913_ = !lean_is_exclusive(v_modifiers_893_);
if (v_isSharedCheck_913_ == 0)
{
v___x_904_ = v_modifiers_893_;
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_attrs_902_);
lean_inc(v_docString_x3f_896_);
lean_inc(v_stx_895_);
lean_dec(v_modifiers_893_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_906_ = lean_unsigned_to_nat(1u);
v___x_907_ = lean_mk_empty_array_with_capacity(v___x_906_);
v___x_908_ = lean_array_push(v___x_907_, v_attr_894_);
v___x_909_ = l_Array_append___redArg(v___x_908_, v_attrs_902_);
lean_dec_ref(v_attrs_902_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 2, v___x_909_);
v___x_911_ = v___x_904_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_stx_895_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_docString_x3f_896_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v___x_909_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3, v_visibility_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3 + 1, v_isProtected_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3 + 2, v_computeKind_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3 + 3, v_recKind_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3 + 4, v_isUnsafe_901_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(lean_object* v_p_914_, lean_object* v_as_915_, size_t v_i_916_, size_t v_stop_917_, lean_object* v_b_918_){
_start:
{
lean_object* v___y_920_; uint8_t v___x_924_; 
v___x_924_ = lean_usize_dec_eq(v_i_916_, v_stop_917_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_925_ = lean_array_uget_borrowed(v_as_915_, v_i_916_);
lean_inc_ref(v_p_914_);
lean_inc(v___x_925_);
v___x_926_ = lean_apply_1(v_p_914_, v___x_925_);
v___x_927_ = lean_unbox(v___x_926_);
if (v___x_927_ == 0)
{
v___y_920_ = v_b_918_;
goto v___jp_919_;
}
else
{
lean_object* v___x_928_; 
lean_inc(v___x_925_);
v___x_928_ = lean_array_push(v_b_918_, v___x_925_);
v___y_920_ = v___x_928_;
goto v___jp_919_;
}
}
else
{
lean_dec_ref(v_p_914_);
return v_b_918_;
}
v___jp_919_:
{
size_t v___x_921_; size_t v___x_922_; 
v___x_921_ = ((size_t)1ULL);
v___x_922_ = lean_usize_add(v_i_916_, v___x_921_);
v_i_916_ = v___x_922_;
v_b_918_ = v___y_920_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0___boxed(lean_object* v_p_929_, lean_object* v_as_930_, lean_object* v_i_931_, lean_object* v_stop_932_, lean_object* v_b_933_){
_start:
{
size_t v_i_boxed_934_; size_t v_stop_boxed_935_; lean_object* v_res_936_; 
v_i_boxed_934_ = lean_unbox_usize(v_i_931_);
lean_dec(v_i_931_);
v_stop_boxed_935_ = lean_unbox_usize(v_stop_932_);
lean_dec(v_stop_932_);
v_res_936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_929_, v_as_930_, v_i_boxed_934_, v_stop_boxed_935_, v_b_933_);
lean_dec_ref(v_as_930_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object* v_modifiers_937_, lean_object* v_p_938_){
_start:
{
lean_object* v_stx_939_; lean_object* v_docString_x3f_940_; uint8_t v_visibility_941_; uint8_t v_isProtected_942_; uint8_t v_computeKind_943_; uint8_t v_recKind_944_; uint8_t v_isUnsafe_945_; lean_object* v_attrs_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_973_; 
v_stx_939_ = lean_ctor_get(v_modifiers_937_, 0);
v_docString_x3f_940_ = lean_ctor_get(v_modifiers_937_, 1);
v_visibility_941_ = lean_ctor_get_uint8(v_modifiers_937_, sizeof(void*)*3);
v_isProtected_942_ = lean_ctor_get_uint8(v_modifiers_937_, sizeof(void*)*3 + 1);
v_computeKind_943_ = lean_ctor_get_uint8(v_modifiers_937_, sizeof(void*)*3 + 2);
v_recKind_944_ = lean_ctor_get_uint8(v_modifiers_937_, sizeof(void*)*3 + 3);
v_isUnsafe_945_ = lean_ctor_get_uint8(v_modifiers_937_, sizeof(void*)*3 + 4);
v_attrs_946_ = lean_ctor_get(v_modifiers_937_, 2);
v_isSharedCheck_973_ = !lean_is_exclusive(v_modifiers_937_);
if (v_isSharedCheck_973_ == 0)
{
v___x_948_ = v_modifiers_937_;
v_isShared_949_ = v_isSharedCheck_973_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_attrs_946_);
lean_inc(v_docString_x3f_940_);
lean_inc(v_stx_939_);
lean_dec(v_modifiers_937_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_973_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_array_get_size(v_attrs_946_);
v___x_952_ = ((lean_object*)(l_Lean_Elab_instInhabitedModifiers_default___closed__0));
v___x_953_ = lean_nat_dec_lt(v___x_950_, v___x_951_);
if (v___x_953_ == 0)
{
lean_object* v___x_955_; 
lean_dec_ref(v_attrs_946_);
lean_dec_ref(v_p_938_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 2, v___x_952_);
v___x_955_ = v___x_948_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_stx_939_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_docString_x3f_940_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v___x_952_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, sizeof(void*)*3, v_visibility_941_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, sizeof(void*)*3 + 1, v_isProtected_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, sizeof(void*)*3 + 2, v_computeKind_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, sizeof(void*)*3 + 3, v_recKind_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, sizeof(void*)*3 + 4, v_isUnsafe_945_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
else
{
uint8_t v___x_957_; 
v___x_957_ = lean_nat_dec_le(v___x_951_, v___x_951_);
if (v___x_957_ == 0)
{
if (v___x_953_ == 0)
{
lean_object* v___x_959_; 
lean_dec_ref(v_attrs_946_);
lean_dec_ref(v_p_938_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 2, v___x_952_);
v___x_959_ = v___x_948_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_stx_939_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_docString_x3f_940_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v___x_952_);
lean_ctor_set_uint8(v_reuseFailAlloc_960_, sizeof(void*)*3, v_visibility_941_);
lean_ctor_set_uint8(v_reuseFailAlloc_960_, sizeof(void*)*3 + 1, v_isProtected_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_960_, sizeof(void*)*3 + 2, v_computeKind_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_960_, sizeof(void*)*3 + 3, v_recKind_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_960_, sizeof(void*)*3 + 4, v_isUnsafe_945_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
else
{
size_t v___x_961_; size_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_961_ = ((size_t)0ULL);
v___x_962_ = lean_usize_of_nat(v___x_951_);
v___x_963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_938_, v_attrs_946_, v___x_961_, v___x_962_, v___x_952_);
lean_dec_ref(v_attrs_946_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 2, v___x_963_);
v___x_965_ = v___x_948_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_stx_939_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_docString_x3f_940_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v___x_963_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3, v_visibility_941_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3 + 1, v_isProtected_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3 + 2, v_computeKind_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3 + 3, v_recKind_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3 + 4, v_isUnsafe_945_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
else
{
size_t v___x_967_; size_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_967_ = ((size_t)0ULL);
v___x_968_ = lean_usize_of_nat(v___x_951_);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_938_, v_attrs_946_, v___x_967_, v___x_968_, v___x_952_);
lean_dec_ref(v_attrs_946_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 2, v___x_969_);
v___x_971_ = v___x_948_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_stx_939_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_docString_x3f_940_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v___x_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3, v_visibility_941_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 1, v_isProtected_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 2, v_computeKind_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 3, v_recKind_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 4, v_isUnsafe_945_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(lean_object* v_p_974_, lean_object* v_as_975_, size_t v_i_976_, size_t v_stop_977_){
_start:
{
uint8_t v___x_978_; 
v___x_978_ = lean_usize_dec_eq(v_i_976_, v_stop_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_979_ = lean_array_uget_borrowed(v_as_975_, v_i_976_);
lean_inc_ref(v_p_974_);
lean_inc(v___x_979_);
v___x_980_ = lean_apply_1(v_p_974_, v___x_979_);
v___x_981_ = lean_unbox(v___x_980_);
if (v___x_981_ == 0)
{
size_t v___x_982_; size_t v___x_983_; 
v___x_982_ = ((size_t)1ULL);
v___x_983_ = lean_usize_add(v_i_976_, v___x_982_);
v_i_976_ = v___x_983_;
goto _start;
}
else
{
uint8_t v___x_985_; 
lean_dec_ref(v_p_974_);
v___x_985_ = lean_unbox(v___x_980_);
return v___x_985_;
}
}
else
{
uint8_t v___x_986_; 
lean_dec_ref(v_p_974_);
v___x_986_ = 0;
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0___boxed(lean_object* v_p_987_, lean_object* v_as_988_, lean_object* v_i_989_, lean_object* v_stop_990_){
_start:
{
size_t v_i_boxed_991_; size_t v_stop_boxed_992_; uint8_t v_res_993_; lean_object* v_r_994_; 
v_i_boxed_991_ = lean_unbox_usize(v_i_989_);
lean_dec(v_i_989_);
v_stop_boxed_992_ = lean_unbox_usize(v_stop_990_);
lean_dec(v_stop_990_);
v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_987_, v_as_988_, v_i_boxed_991_, v_stop_boxed_992_);
lean_dec_ref(v_as_988_);
v_r_994_ = lean_box(v_res_993_);
return v_r_994_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_anyAttr(lean_object* v_modifiers_995_, lean_object* v_p_996_){
_start:
{
lean_object* v_attrs_997_; lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v_attrs_997_ = lean_ctor_get(v_modifiers_995_, 2);
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = lean_array_get_size(v_attrs_997_);
v___x_1000_ = lean_nat_dec_lt(v___x_998_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_dec_ref(v_p_996_);
return v___x_1000_;
}
else
{
if (v___x_1000_ == 0)
{
lean_dec_ref(v_p_996_);
return v___x_1000_;
}
else
{
size_t v___x_1001_; size_t v___x_1002_; uint8_t v___x_1003_; 
v___x_1001_ = ((size_t)0ULL);
v___x_1002_ = lean_usize_of_nat(v___x_999_);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_996_, v_attrs_997_, v___x_1001_, v___x_1002_);
return v___x_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_anyAttr___boxed(lean_object* v_modifiers_1004_, lean_object* v_p_1005_){
_start:
{
uint8_t v_res_1006_; lean_object* v_r_1007_; 
v_res_1006_ = l_Lean_Elab_Modifiers_anyAttr(v_modifiers_1004_, v_p_1005_);
lean_dec_ref(v_modifiers_1004_);
v_r_1007_ = lean_box(v_res_1006_);
return v_r_1007_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__0));
v___x_1011_ = lean_string_length(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__2, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__2_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2);
v___x_1013_ = lean_nat_to_int(v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__0(lean_object* v_attr_1020_){
_start:
{
uint8_t v_kind_1021_; lean_object* v_name_1022_; lean_object* v_stx_1023_; lean_object* v___y_1025_; 
v_kind_1021_ = lean_ctor_get_uint8(v_attr_1020_, sizeof(void*)*2);
v_name_1022_ = lean_ctor_get(v_attr_1020_, 0);
lean_inc(v_name_1022_);
v_stx_1023_ = lean_ctor_get(v_attr_1020_, 1);
lean_inc(v_stx_1023_);
lean_dec_ref(v_attr_1020_);
switch(v_kind_1021_)
{
case 0:
{
lean_object* v___x_1047_; 
v___x_1047_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4));
v___y_1025_ = v___x_1047_;
goto v___jp_1024_;
}
case 1:
{
lean_object* v___x_1048_; 
v___x_1048_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__6));
v___y_1025_ = v___x_1048_;
goto v___jp_1024_;
}
default: 
{
lean_object* v___x_1049_; 
v___x_1049_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__7));
v___y_1025_ = v___x_1049_;
goto v___jp_1024_;
}
}
v___jp_1024_:
{
lean_object* v___x_1026_; uint8_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; 
lean_inc_ref(v___y_1025_);
v___x_1026_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___y_1025_);
v___x_1027_ = 1;
v___x_1028_ = l_Lean_Name_toString(v_name_1022_, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1026_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_box(0);
v___x_1032_ = 0;
v___x_1033_ = l_Lean_Syntax_formatStx(v_stx_1023_, v___x_1031_, v___x_1032_);
v___x_1034_ = l_Std_Format_defWidth;
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = l_Std_Format_pretty(v___x_1033_, v___x_1034_, v___x_1035_, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1030_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__3, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__3_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3);
v___x_1040_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__4));
v___x_1041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v___x_1038_);
v___x_1042_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__5));
v___x_1043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1039_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = 0;
v___x_1046_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*1, v___x_1045_);
return v___x_1046_;
}
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__0));
v___x_1059_ = lean_string_length(v___x_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__5, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__5_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5);
v___x_1061_ = lean_nat_to_int(v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__35(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__33));
v___x_1118_ = lean_string_length(v___x_1117_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__36(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__35, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__35_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__35);
v___x_1120_ = lean_nat_to_int(v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__1(lean_object* v___f_1130_, lean_object* v___f_1131_, lean_object* v_m_1132_){
_start:
{
lean_object* v_docString_x3f_1133_; uint8_t v_visibility_1134_; uint8_t v_isProtected_1135_; uint8_t v_computeKind_1136_; uint8_t v_recKind_1137_; uint8_t v_isUnsafe_1138_; lean_object* v_attrs_1139_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1185_; 
v_docString_x3f_1133_ = lean_ctor_get(v_m_1132_, 1);
lean_inc(v_docString_x3f_1133_);
v_visibility_1134_ = lean_ctor_get_uint8(v_m_1132_, sizeof(void*)*3);
v_isProtected_1135_ = lean_ctor_get_uint8(v_m_1132_, sizeof(void*)*3 + 1);
v_computeKind_1136_ = lean_ctor_get_uint8(v_m_1132_, sizeof(void*)*3 + 2);
v_recKind_1137_ = lean_ctor_get_uint8(v_m_1132_, sizeof(void*)*3 + 3);
v_isUnsafe_1138_ = lean_ctor_get_uint8(v_m_1132_, sizeof(void*)*3 + 4);
v_attrs_1139_ = lean_ctor_get(v_m_1132_, 2);
lean_inc_ref(v_attrs_1139_);
lean_dec_ref(v_m_1132_);
if (lean_obj_tag(v_docString_x3f_1133_) == 0)
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_box(0);
v___y_1185_ = v___x_1189_;
goto v___jp_1184_;
}
else
{
lean_object* v_val_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1232_; 
v_val_1190_ = lean_ctor_get(v_docString_x3f_1133_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_docString_x3f_1133_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1192_ = v_docString_x3f_1133_;
v_isShared_1193_ = v_isSharedCheck_1232_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_val_1190_);
lean_dec(v_docString_x3f_1133_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1232_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_fst_1194_; lean_object* v_snd_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1231_; 
v_fst_1194_ = lean_ctor_get(v_val_1190_, 0);
v_snd_1195_ = lean_ctor_get(v_val_1190_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_val_1190_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1197_ = v_val_1190_;
v_isShared_1198_ = v_isSharedCheck_1231_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_snd_1195_);
lean_inc(v_fst_1194_);
lean_dec(v_val_1190_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1231_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1199_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__32));
v___x_1200_ = lean_box(0);
v___x_1201_ = 0;
v___x_1202_ = l_Lean_Syntax_formatStx(v_fst_1194_, v___x_1200_, v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__2));
if (v_isShared_1198_ == 0)
{
lean_ctor_set_tag(v___x_1197_, 5);
lean_ctor_set(v___x_1197_, 1, v___x_1203_);
lean_ctor_set(v___x_1197_, 0, v___x_1202_);
v___x_1205_ = v___x_1197_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___y_1209_; uint8_t v___x_1227_; 
v___x_1206_ = lean_box(1);
v___x_1207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1227_ = lean_unbox(v_snd_1195_);
lean_dec(v_snd_1195_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; 
v___x_1228_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__41));
v___y_1209_ = v___x_1228_;
goto v___jp_1208_;
}
else
{
lean_object* v___x_1229_; 
v___x_1229_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__42));
v___y_1209_ = v___x_1229_;
goto v___jp_1208_;
}
v___jp_1208_:
{
lean_object* v___x_1211_; 
lean_inc_ref(v___y_1209_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set_tag(v___x_1192_, 3);
lean_ctor_set(v___x_1192_, 0, v___y_1209_);
v___x_1211_ = v___x_1192_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___y_1209_);
v___x_1211_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1207_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__36, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__36_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__36);
v___x_1214_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__37));
v___x_1215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___x_1212_);
v___x_1216_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__38));
v___x_1217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1213_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = 0;
v___x_1220_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1220_, 0, v___x_1218_);
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*1, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1199_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__40));
v___x_1223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1221_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = lean_box(0);
v___x_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1223_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___y_1185_ = v___x_1225_;
goto v___jp_1184_;
}
}
}
}
}
}
v___jp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v_components_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; 
lean_inc(v___y_1142_);
v___x_1143_ = l_List_appendTR___redArg(v___y_1141_, v___y_1142_);
v___x_1144_ = lean_array_to_list(v_attrs_1139_);
v___x_1145_ = lean_box(0);
v___x_1146_ = l_List_mapTR_loop___redArg(v___f_1130_, v___x_1144_, v___x_1145_);
v_components_1147_ = l_List_appendTR___redArg(v___x_1143_, v___x_1146_);
v___x_1148_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__3));
v___x_1149_ = l_Std_Format_joinSep___redArg(v___f_1131_, v_components_1147_, v___x_1148_);
v___x_1150_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__6, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__6_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6);
v___x_1151_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__7));
v___x_1152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
lean_ctor_set(v___x_1152_, 1, v___x_1149_);
v___x_1153_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__8));
v___x_1154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1150_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = 0;
v___x_1157_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*1, v___x_1156_);
return v___x_1157_;
}
v___jp_1158_:
{
lean_object* v___x_1161_; 
lean_inc(v___y_1160_);
v___x_1161_ = l_List_appendTR___redArg(v___y_1159_, v___y_1160_);
if (v_isUnsafe_1138_ == 0)
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_box(0);
v___y_1141_ = v___x_1161_;
v___y_1142_ = v___x_1162_;
goto v___jp_1140_;
}
else
{
lean_object* v___x_1163_; 
v___x_1163_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__11));
v___y_1141_ = v___x_1161_;
v___y_1142_ = v___x_1163_;
goto v___jp_1140_;
}
}
v___jp_1164_:
{
lean_object* v___x_1167_; 
lean_inc(v___y_1166_);
v___x_1167_ = l_List_appendTR___redArg(v___y_1165_, v___y_1166_);
switch(v_recKind_1137_)
{
case 0:
{
lean_object* v___x_1168_; 
v___x_1168_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__14));
v___y_1159_ = v___x_1167_;
v___y_1160_ = v___x_1168_;
goto v___jp_1158_;
}
case 1:
{
lean_object* v___x_1169_; 
v___x_1169_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__17));
v___y_1159_ = v___x_1167_;
v___y_1160_ = v___x_1169_;
goto v___jp_1158_;
}
default: 
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_box(0);
v___y_1159_ = v___x_1167_;
v___y_1160_ = v___x_1170_;
goto v___jp_1158_;
}
}
}
v___jp_1171_:
{
lean_object* v___x_1174_; 
lean_inc(v___y_1173_);
v___x_1174_ = l_List_appendTR___redArg(v___y_1172_, v___y_1173_);
switch(v_computeKind_1136_)
{
case 0:
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_box(0);
v___y_1165_ = v___x_1174_;
v___y_1166_ = v___x_1175_;
goto v___jp_1164_;
}
case 1:
{
lean_object* v___x_1176_; 
v___x_1176_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__20));
v___y_1165_ = v___x_1174_;
v___y_1166_ = v___x_1176_;
goto v___jp_1164_;
}
default: 
{
lean_object* v___x_1177_; 
v___x_1177_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__23));
v___y_1165_ = v___x_1174_;
v___y_1166_ = v___x_1177_;
goto v___jp_1164_;
}
}
}
v___jp_1178_:
{
lean_object* v___x_1181_; 
lean_inc(v___y_1180_);
v___x_1181_ = l_List_appendTR___redArg(v___y_1179_, v___y_1180_);
if (v_isProtected_1135_ == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_box(0);
v___y_1172_ = v___x_1181_;
v___y_1173_ = v___x_1182_;
goto v___jp_1171_;
}
else
{
lean_object* v___x_1183_; 
v___x_1183_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__26));
v___y_1172_ = v___x_1181_;
v___y_1173_ = v___x_1183_;
goto v___jp_1171_;
}
}
v___jp_1184_:
{
switch(v_visibility_1134_)
{
case 0:
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_box(0);
v___y_1179_ = v___y_1185_;
v___y_1180_ = v___x_1186_;
goto v___jp_1178_;
}
case 1:
{
lean_object* v___x_1187_; 
v___x_1187_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__28));
v___y_1179_ = v___y_1185_;
v___y_1180_ = v___x_1187_;
goto v___jp_1178_;
}
default: 
{
lean_object* v___x_1188_; 
v___x_1188_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__30));
v___y_1179_ = v___y_1185_;
v___y_1180_ = v___x_1188_;
goto v___jp_1178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lam__0(lean_object* v_f_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = l_Std_Format_defWidth;
v___x_1241_ = lean_unsigned_to_nat(0u);
v___x_1242_ = l_Std_Format_pretty(v_f_1239_, v___x_1240_, v___x_1241_, v___x_1241_);
return v___x_1242_;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = ((lean_object*)(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0));
v___x_1250_ = l_Lean_stringToMessageData(v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg(lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_optDocComment_1253_){
_start:
{
lean_object* v_toApplicative_1254_; lean_object* v_toPure_1255_; lean_object* v___x_1256_; 
v_toApplicative_1254_ = lean_ctor_get(v_inst_1251_, 0);
v_toPure_1255_ = lean_ctor_get(v_toApplicative_1254_, 1);
v___x_1256_ = l_Lean_Syntax_getOptional_x3f(v_optDocComment_1253_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_inc(v_toPure_1255_);
lean_dec_ref(v_inst_1252_);
lean_dec_ref(v_inst_1251_);
v___x_1257_ = lean_box(0);
v___x_1258_ = lean_apply_2(v_toPure_1255_, lean_box(0), v___x_1257_);
return v___x_1258_;
}
else
{
lean_object* v_val_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1280_; 
v_val_1259_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1261_ = v___x_1256_;
v_isShared_1262_ = v_isSharedCheck_1280_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_val_1259_);
lean_dec(v___x_1256_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1280_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = l_Lean_Syntax_getArg(v_val_1259_, v___x_1263_);
if (lean_obj_tag(v___x_1264_) == 2)
{
lean_object* v_val_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1272_; 
lean_inc(v_toPure_1255_);
lean_dec(v_val_1259_);
lean_dec_ref(v_inst_1252_);
lean_dec_ref(v_inst_1251_);
v_val_1265_ = lean_ctor_get(v___x_1264_, 1);
lean_inc_ref(v_val_1265_);
lean_dec_ref(v___x_1264_);
v___x_1266_ = lean_unsigned_to_nat(0u);
v___x_1267_ = lean_string_utf8_byte_size(v_val_1265_);
v___x_1268_ = lean_unsigned_to_nat(2u);
v___x_1269_ = lean_nat_sub(v___x_1267_, v___x_1268_);
v___x_1270_ = lean_string_utf8_extract(v_val_1265_, v___x_1266_, v___x_1269_);
lean_dec(v___x_1269_);
lean_dec_ref(v_val_1265_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v___x_1270_);
v___x_1272_ = v___x_1261_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_apply_2(v_toPure_1255_, lean_box(0), v___x_1272_);
return v___x_1273_;
}
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_del_object(v___x_1261_);
v___x_1275_ = lean_obj_once(&l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1, &l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1_once, _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1);
v___x_1276_ = l_Lean_MessageData_ofSyntax(v___x_1264_);
v___x_1277_ = l_Lean_indentD(v___x_1276_);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1275_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = l_Lean_throwErrorAt___redArg(v_inst_1251_, v_inst_1252_, v_val_1259_, v___x_1278_);
return v___x_1279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___boxed(lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_optDocComment_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1281_, v_inst_1282_, v_optDocComment_1283_);
lean_dec(v_optDocComment_1283_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f(lean_object* v_m_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_optDocComment_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1286_, v_inst_1287_, v_optDocComment_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___boxed(lean_object* v_m_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_optDocComment_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_Elab_expandOptDocComment_x3f(v_m_1290_, v_inst_1291_, v_inst_1292_, v_optDocComment_1293_);
lean_dec(v_optDocComment_1293_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0(lean_object* v_stx_1295_, lean_object* v___y_1296_, uint8_t v_visibility_1297_, uint8_t v___y_1298_, uint8_t v___y_1299_, uint8_t v___y_1300_, lean_object* v_toPure_1301_, lean_object* v_unsafeStx_1302_, lean_object* v_attrs_1303_){
_start:
{
uint8_t v___y_1305_; uint8_t v___x_1308_; 
v___x_1308_ = l_Lean_Syntax_isNone(v_unsafeStx_1302_);
if (v___x_1308_ == 0)
{
uint8_t v___x_1309_; 
v___x_1309_ = 1;
v___y_1305_ = v___x_1309_;
goto v___jp_1304_;
}
else
{
uint8_t v___x_1310_; 
v___x_1310_ = 0;
v___y_1305_ = v___x_1310_;
goto v___jp_1304_;
}
v___jp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1306_, 0, v_stx_1295_);
lean_ctor_set(v___x_1306_, 1, v___y_1296_);
lean_ctor_set(v___x_1306_, 2, v_attrs_1303_);
lean_ctor_set_uint8(v___x_1306_, sizeof(void*)*3, v_visibility_1297_);
lean_ctor_set_uint8(v___x_1306_, sizeof(void*)*3 + 1, v___y_1298_);
lean_ctor_set_uint8(v___x_1306_, sizeof(void*)*3 + 2, v___y_1299_);
lean_ctor_set_uint8(v___x_1306_, sizeof(void*)*3 + 3, v___y_1300_);
lean_ctor_set_uint8(v___x_1306_, sizeof(void*)*3 + 4, v___y_1305_);
v___x_1307_ = lean_apply_2(v_toPure_1301_, lean_box(0), v___x_1306_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0___boxed(lean_object* v_stx_1311_, lean_object* v___y_1312_, lean_object* v_visibility_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v_toPure_1317_, lean_object* v_unsafeStx_1318_, lean_object* v_attrs_1319_){
_start:
{
uint8_t v_visibility_boxed_1320_; uint8_t v___y_482__boxed_1321_; uint8_t v___y_483__boxed_1322_; uint8_t v___y_484__boxed_1323_; lean_object* v_res_1324_; 
v_visibility_boxed_1320_ = lean_unbox(v_visibility_1313_);
v___y_482__boxed_1321_ = lean_unbox(v___y_1314_);
v___y_483__boxed_1322_ = lean_unbox(v___y_1315_);
v___y_484__boxed_1323_ = lean_unbox(v___y_1316_);
v_res_1324_ = l_Lean_Elab_elabModifiers___redArg___lam__0(v_stx_1311_, v___y_1312_, v_visibility_boxed_1320_, v___y_482__boxed_1321_, v___y_483__boxed_1322_, v___y_484__boxed_1323_, v_toPure_1317_, v_unsafeStx_1318_, v_attrs_1319_);
lean_dec(v_unsafeStx_1318_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__1(lean_object* v___f_1325_, lean_object* v_attrs_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_apply_1(v___f_1325_, v_attrs_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3(lean_object* v_stx_1328_, lean_object* v___y_1329_, uint8_t v___y_1330_, uint8_t v___y_1331_, lean_object* v_toPure_1332_, lean_object* v_unsafeStx_1333_, lean_object* v_attrsStx_1334_, lean_object* v___x_1335_, lean_object* v_toBind_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_inst_1341_, lean_object* v_inst_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_protectedStx_1349_, uint8_t v_visibility_1350_){
_start:
{
uint8_t v___y_1352_; uint8_t v___x_1367_; 
v___x_1367_ = l_Lean_Syntax_isNone(v_protectedStx_1349_);
if (v___x_1367_ == 0)
{
uint8_t v___x_1368_; 
v___x_1368_ = 1;
v___y_1352_ = v___x_1368_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1369_; 
v___x_1369_ = 0;
v___y_1352_ = v___x_1369_;
goto v___jp_1351_;
}
v___jp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___f_1357_; lean_object* v___x_1358_; 
v___x_1353_ = lean_box(v_visibility_1350_);
v___x_1354_ = lean_box(v___y_1352_);
v___x_1355_ = lean_box(v___y_1330_);
v___x_1356_ = lean_box(v___y_1331_);
lean_inc(v_toPure_1332_);
v___f_1357_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_1357_, 0, v_stx_1328_);
lean_closure_set(v___f_1357_, 1, v___y_1329_);
lean_closure_set(v___f_1357_, 2, v___x_1353_);
lean_closure_set(v___f_1357_, 3, v___x_1354_);
lean_closure_set(v___f_1357_, 4, v___x_1355_);
lean_closure_set(v___f_1357_, 5, v___x_1356_);
lean_closure_set(v___f_1357_, 6, v_toPure_1332_);
lean_closure_set(v___f_1357_, 7, v_unsafeStx_1333_);
v___x_1358_ = l_Lean_Syntax_getOptional_x3f(v_attrsStx_1334_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v___f_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec(v_inst_1348_);
lean_dec(v_inst_1347_);
lean_dec_ref(v_inst_1346_);
lean_dec(v_inst_1345_);
lean_dec(v_inst_1344_);
lean_dec_ref(v_inst_1343_);
lean_dec_ref(v_inst_1342_);
lean_dec_ref(v_inst_1341_);
lean_dec_ref(v_inst_1340_);
lean_dec_ref(v_inst_1339_);
lean_dec_ref(v_inst_1338_);
lean_dec_ref(v_inst_1337_);
v___f_1359_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1359_, 0, v___f_1357_);
v___x_1360_ = lean_mk_empty_array_with_capacity(v___x_1335_);
v___x_1361_ = lean_apply_2(v_toPure_1332_, lean_box(0), v___x_1360_);
v___x_1362_ = lean_apply_4(v_toBind_1336_, lean_box(0), lean_box(0), v___x_1361_, v___f_1359_);
return v___x_1362_;
}
else
{
lean_object* v_val_1363_; lean_object* v___f_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec(v_toPure_1332_);
v_val_1363_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_val_1363_);
lean_dec_ref(v___x_1358_);
v___f_1364_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1364_, 0, v___f_1357_);
v___x_1365_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_1337_, v_inst_1338_, v_inst_1339_, v_inst_1340_, v_inst_1341_, v_inst_1342_, v_inst_1343_, v_inst_1344_, v_inst_1345_, v_inst_1346_, v_inst_1347_, v_inst_1348_, v_val_1363_);
lean_dec(v_val_1363_);
v___x_1366_ = lean_apply_4(v_toBind_1336_, lean_box(0), lean_box(0), v___x_1365_, v___f_1364_);
return v___x_1366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_stx_1370_ = _args[0];
lean_object* v___y_1371_ = _args[1];
lean_object* v___y_1372_ = _args[2];
lean_object* v___y_1373_ = _args[3];
lean_object* v_toPure_1374_ = _args[4];
lean_object* v_unsafeStx_1375_ = _args[5];
lean_object* v_attrsStx_1376_ = _args[6];
lean_object* v___x_1377_ = _args[7];
lean_object* v_toBind_1378_ = _args[8];
lean_object* v_inst_1379_ = _args[9];
lean_object* v_inst_1380_ = _args[10];
lean_object* v_inst_1381_ = _args[11];
lean_object* v_inst_1382_ = _args[12];
lean_object* v_inst_1383_ = _args[13];
lean_object* v_inst_1384_ = _args[14];
lean_object* v_inst_1385_ = _args[15];
lean_object* v_inst_1386_ = _args[16];
lean_object* v_inst_1387_ = _args[17];
lean_object* v_inst_1388_ = _args[18];
lean_object* v_inst_1389_ = _args[19];
lean_object* v_inst_1390_ = _args[20];
lean_object* v_protectedStx_1391_ = _args[21];
lean_object* v_visibility_1392_ = _args[22];
_start:
{
uint8_t v___y_512__boxed_1393_; uint8_t v___y_513__boxed_1394_; uint8_t v_visibility_boxed_1395_; lean_object* v_res_1396_; 
v___y_512__boxed_1393_ = lean_unbox(v___y_1372_);
v___y_513__boxed_1394_ = lean_unbox(v___y_1373_);
v_visibility_boxed_1395_ = lean_unbox(v_visibility_1392_);
v_res_1396_ = l_Lean_Elab_elabModifiers___redArg___lam__3(v_stx_1370_, v___y_1371_, v___y_512__boxed_1393_, v___y_513__boxed_1394_, v_toPure_1374_, v_unsafeStx_1375_, v_attrsStx_1376_, v___x_1377_, v_toBind_1378_, v_inst_1379_, v_inst_1380_, v_inst_1381_, v_inst_1382_, v_inst_1383_, v_inst_1384_, v_inst_1385_, v_inst_1386_, v_inst_1387_, v_inst_1388_, v_inst_1389_, v_inst_1390_, v_protectedStx_1391_, v_visibility_boxed_1395_);
lean_dec(v_protectedStx_1391_);
lean_dec(v___x_1377_);
lean_dec(v_attrsStx_1376_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2(lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v_inst_1399_, lean_object* v_inst_1400_, lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_toBind_1403_, lean_object* v_stx_1404_, uint8_t v___y_1405_, uint8_t v___y_1406_, lean_object* v_toPure_1407_, lean_object* v_unsafeStx_1408_, lean_object* v_attrsStx_1409_, lean_object* v___x_1410_, lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_inst_1415_, lean_object* v_inst_1416_, lean_object* v_protectedStx_1417_, lean_object* v_visibilityStx_1418_, lean_object* v_docCommentStx_1419_, lean_object* v___x_1420_, lean_object* v_____do__lift_1421_){
_start:
{
lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1428_; lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_Syntax_getOptional_x3f(v_docCommentStx_1419_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v___x_1443_; 
lean_dec_ref(v___x_1420_);
v___x_1443_ = lean_box(0);
v___y_1428_ = v___x_1443_;
goto v___jp_1427_;
}
else
{
lean_object* v_val_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1454_; 
v_val_1444_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1446_ = v___x_1442_;
v_isShared_1447_ = v_isSharedCheck_1454_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_val_1444_);
lean_dec(v___x_1442_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1454_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1448_ = l_Lean_doc_verso;
v___x_1449_ = l_Lean_Option_get___redArg(v___x_1420_, v_____do__lift_1421_, v___x_1448_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v_val_1444_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1450_);
v___x_1452_ = v___x_1446_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
v___y_1428_ = v___x_1452_;
goto v___jp_1427_;
}
}
}
v___jp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = l_Lean_Elab_elabVisibility___redArg(v_inst_1397_, v_inst_1398_, v_inst_1399_, v_inst_1400_, v_inst_1401_, v_inst_1402_, v___y_1424_);
v___x_1426_ = lean_apply_4(v_toBind_1403_, lean_box(0), lean_box(0), v___x_1425_, v___y_1423_);
return v___x_1426_;
}
v___jp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___f_1431_; lean_object* v___x_1432_; 
v___x_1429_ = lean_box(v___y_1405_);
v___x_1430_ = lean_box(v___y_1406_);
lean_inc_ref(v_inst_1401_);
lean_inc(v_inst_1402_);
lean_inc(v_inst_1400_);
lean_inc_ref(v_inst_1398_);
lean_inc_ref(v_inst_1399_);
lean_inc_ref(v_inst_1397_);
lean_inc(v_toBind_1403_);
v___f_1431_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__3___boxed), 23, 22);
lean_closure_set(v___f_1431_, 0, v_stx_1404_);
lean_closure_set(v___f_1431_, 1, v___y_1428_);
lean_closure_set(v___f_1431_, 2, v___x_1429_);
lean_closure_set(v___f_1431_, 3, v___x_1430_);
lean_closure_set(v___f_1431_, 4, v_toPure_1407_);
lean_closure_set(v___f_1431_, 5, v_unsafeStx_1408_);
lean_closure_set(v___f_1431_, 6, v_attrsStx_1409_);
lean_closure_set(v___f_1431_, 7, v___x_1410_);
lean_closure_set(v___f_1431_, 8, v_toBind_1403_);
lean_closure_set(v___f_1431_, 9, v_inst_1397_);
lean_closure_set(v___f_1431_, 10, v_inst_1399_);
lean_closure_set(v___f_1431_, 11, v_inst_1411_);
lean_closure_set(v___f_1431_, 12, v_inst_1398_);
lean_closure_set(v___f_1431_, 13, v_inst_1412_);
lean_closure_set(v___f_1431_, 14, v_inst_1413_);
lean_closure_set(v___f_1431_, 15, v_inst_1414_);
lean_closure_set(v___f_1431_, 16, v_inst_1400_);
lean_closure_set(v___f_1431_, 17, v_inst_1402_);
lean_closure_set(v___f_1431_, 18, v_inst_1401_);
lean_closure_set(v___f_1431_, 19, v_inst_1415_);
lean_closure_set(v___f_1431_, 20, v_inst_1416_);
lean_closure_set(v___f_1431_, 21, v_protectedStx_1417_);
v___x_1432_ = l_Lean_Syntax_getOptional_x3f(v_visibilityStx_1418_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_box(0);
v___y_1423_ = v___f_1431_;
v___y_1424_ = v___x_1433_;
goto v___jp_1422_;
}
else
{
lean_object* v_val_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
v_val_1434_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1432_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_val_1434_);
lean_dec(v___x_1432_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_val_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
v___y_1423_ = v___f_1431_;
v___y_1424_ = v___x_1439_;
goto v___jp_1422_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_inst_1455_ = _args[0];
lean_object* v_inst_1456_ = _args[1];
lean_object* v_inst_1457_ = _args[2];
lean_object* v_inst_1458_ = _args[3];
lean_object* v_inst_1459_ = _args[4];
lean_object* v_inst_1460_ = _args[5];
lean_object* v_toBind_1461_ = _args[6];
lean_object* v_stx_1462_ = _args[7];
lean_object* v___y_1463_ = _args[8];
lean_object* v___y_1464_ = _args[9];
lean_object* v_toPure_1465_ = _args[10];
lean_object* v_unsafeStx_1466_ = _args[11];
lean_object* v_attrsStx_1467_ = _args[12];
lean_object* v___x_1468_ = _args[13];
lean_object* v_inst_1469_ = _args[14];
lean_object* v_inst_1470_ = _args[15];
lean_object* v_inst_1471_ = _args[16];
lean_object* v_inst_1472_ = _args[17];
lean_object* v_inst_1473_ = _args[18];
lean_object* v_inst_1474_ = _args[19];
lean_object* v_protectedStx_1475_ = _args[20];
lean_object* v_visibilityStx_1476_ = _args[21];
lean_object* v_docCommentStx_1477_ = _args[22];
lean_object* v___x_1478_ = _args[23];
lean_object* v_____do__lift_1479_ = _args[24];
_start:
{
uint8_t v___y_603__boxed_1480_; uint8_t v___y_604__boxed_1481_; lean_object* v_res_1482_; 
v___y_603__boxed_1480_ = lean_unbox(v___y_1463_);
v___y_604__boxed_1481_ = lean_unbox(v___y_1464_);
v_res_1482_ = l_Lean_Elab_elabModifiers___redArg___lam__2(v_inst_1455_, v_inst_1456_, v_inst_1457_, v_inst_1458_, v_inst_1459_, v_inst_1460_, v_toBind_1461_, v_stx_1462_, v___y_603__boxed_1480_, v___y_604__boxed_1481_, v_toPure_1465_, v_unsafeStx_1466_, v_attrsStx_1467_, v___x_1468_, v_inst_1469_, v_inst_1470_, v_inst_1471_, v_inst_1472_, v_inst_1473_, v_inst_1474_, v_protectedStx_1475_, v_visibilityStx_1476_, v_docCommentStx_1477_, v___x_1478_, v_____do__lift_1479_);
lean_dec_ref(v_____do__lift_1479_);
lean_dec(v_docCommentStx_1477_);
lean_dec(v_visibilityStx_1476_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg(lean_object* v_inst_1493_, lean_object* v_inst_1494_, lean_object* v_inst_1495_, lean_object* v_inst_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_inst_1499_, lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_inst_1504_, lean_object* v_stx_1505_){
_start:
{
lean_object* v___x_1506_; lean_object* v_toApplicative_1507_; lean_object* v_toBind_1508_; lean_object* v_toPure_1509_; lean_object* v___x_1510_; lean_object* v_docCommentStx_1511_; lean_object* v___x_1512_; lean_object* v_attrsStx_1513_; lean_object* v___x_1514_; lean_object* v_visibilityStx_1515_; lean_object* v___x_1516_; lean_object* v_protectedStx_1517_; uint8_t v___y_1519_; lean_object* v___y_1520_; uint8_t v___y_1521_; uint8_t v___y_1527_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1506_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1507_ = lean_ctor_get(v_inst_1493_, 0);
v_toBind_1508_ = lean_ctor_get(v_inst_1493_, 1);
lean_inc(v_toBind_1508_);
v_toPure_1509_ = lean_ctor_get(v_toApplicative_1507_, 1);
lean_inc(v_toPure_1509_);
v___x_1510_ = lean_unsigned_to_nat(0u);
v_docCommentStx_1511_ = l_Lean_Syntax_getArg(v_stx_1505_, v___x_1510_);
v___x_1512_ = lean_unsigned_to_nat(1u);
v_attrsStx_1513_ = l_Lean_Syntax_getArg(v_stx_1505_, v___x_1512_);
v___x_1514_ = lean_unsigned_to_nat(2u);
v_visibilityStx_1515_ = l_Lean_Syntax_getArg(v_stx_1505_, v___x_1514_);
v___x_1516_ = lean_unsigned_to_nat(3u);
v_protectedStx_1517_ = l_Lean_Syntax_getArg(v_stx_1505_, v___x_1516_);
v___x_1540_ = lean_unsigned_to_nat(4u);
v___x_1541_ = l_Lean_Syntax_getArg(v_stx_1505_, v___x_1540_);
v___x_1542_ = l_Lean_Syntax_isNone(v___x_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1543_ = l_Lean_Syntax_getArg(v___x_1541_, v___x_1510_);
lean_dec(v___x_1541_);
v___x_1544_ = l_Lean_Syntax_getKind(v___x_1543_);
v___x_1545_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__1));
v___x_1546_ = lean_name_eq(v___x_1544_, v___x_1545_);
lean_dec(v___x_1544_);
if (v___x_1546_ == 0)
{
uint8_t v___x_1547_; 
v___x_1547_ = 2;
v___y_1527_ = v___x_1547_;
goto v___jp_1526_;
}
else
{
uint8_t v___x_1548_; 
v___x_1548_ = 1;
v___y_1527_ = v___x_1548_;
goto v___jp_1526_;
}
}
else
{
uint8_t v___x_1549_; 
lean_dec(v___x_1541_);
v___x_1549_ = 0;
v___y_1527_ = v___x_1549_;
goto v___jp_1526_;
}
v___jp_1518_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___f_1524_; lean_object* v___x_1525_; 
v___x_1522_ = lean_box(v___y_1519_);
v___x_1523_ = lean_box(v___y_1521_);
lean_inc(v_toBind_1508_);
lean_inc(v_inst_1501_);
v___f_1524_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__2___boxed), 25, 24);
lean_closure_set(v___f_1524_, 0, v_inst_1493_);
lean_closure_set(v___f_1524_, 1, v_inst_1496_);
lean_closure_set(v___f_1524_, 2, v_inst_1494_);
lean_closure_set(v___f_1524_, 3, v_inst_1501_);
lean_closure_set(v___f_1524_, 4, v_inst_1503_);
lean_closure_set(v___f_1524_, 5, v_inst_1502_);
lean_closure_set(v___f_1524_, 6, v_toBind_1508_);
lean_closure_set(v___f_1524_, 7, v_stx_1505_);
lean_closure_set(v___f_1524_, 8, v___x_1522_);
lean_closure_set(v___f_1524_, 9, v___x_1523_);
lean_closure_set(v___f_1524_, 10, v_toPure_1509_);
lean_closure_set(v___f_1524_, 11, v___y_1520_);
lean_closure_set(v___f_1524_, 12, v_attrsStx_1513_);
lean_closure_set(v___f_1524_, 13, v___x_1510_);
lean_closure_set(v___f_1524_, 14, v_inst_1495_);
lean_closure_set(v___f_1524_, 15, v_inst_1498_);
lean_closure_set(v___f_1524_, 16, v_inst_1499_);
lean_closure_set(v___f_1524_, 17, v_inst_1500_);
lean_closure_set(v___f_1524_, 18, v_inst_1504_);
lean_closure_set(v___f_1524_, 19, v_inst_1497_);
lean_closure_set(v___f_1524_, 20, v_protectedStx_1517_);
lean_closure_set(v___f_1524_, 21, v_visibilityStx_1515_);
lean_closure_set(v___f_1524_, 22, v_docCommentStx_1511_);
lean_closure_set(v___f_1524_, 23, v___x_1506_);
v___x_1525_ = lean_apply_4(v_toBind_1508_, lean_box(0), lean_box(0), v_inst_1501_, v___f_1524_);
return v___x_1525_;
}
v___jp_1526_:
{
lean_object* v___x_1528_; lean_object* v_unsafeStx_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1528_ = lean_unsigned_to_nat(5u);
v_unsafeStx_1529_ = l_Lean_Syntax_getArg(v_stx_1505_, v___x_1528_);
v___x_1530_ = lean_unsigned_to_nat(6u);
v___x_1531_ = l_Lean_Syntax_getArg(v_stx_1505_, v___x_1530_);
v___x_1532_ = l_Lean_Syntax_isNone(v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1533_ = l_Lean_Syntax_getArg(v___x_1531_, v___x_1510_);
lean_dec(v___x_1531_);
v___x_1534_ = l_Lean_Syntax_getKind(v___x_1533_);
v___x_1535_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__0));
v___x_1536_ = lean_name_eq(v___x_1534_, v___x_1535_);
lean_dec(v___x_1534_);
if (v___x_1536_ == 0)
{
uint8_t v___x_1537_; 
v___x_1537_ = 1;
v___y_1519_ = v___y_1527_;
v___y_1520_ = v_unsafeStx_1529_;
v___y_1521_ = v___x_1537_;
goto v___jp_1518_;
}
else
{
uint8_t v___x_1538_; 
v___x_1538_ = 0;
v___y_1519_ = v___y_1527_;
v___y_1520_ = v_unsafeStx_1529_;
v___y_1521_ = v___x_1538_;
goto v___jp_1518_;
}
}
else
{
uint8_t v___x_1539_; 
lean_dec(v___x_1531_);
v___x_1539_ = 2;
v___y_1519_ = v___y_1527_;
v___y_1520_ = v_unsafeStx_1529_;
v___y_1521_ = v___x_1539_;
goto v___jp_1518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object* v_m_1550_, lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v_inst_1556_, lean_object* v_inst_1557_, lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_inst_1560_, lean_object* v_inst_1561_, lean_object* v_inst_1562_, lean_object* v_stx_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Elab_elabModifiers___redArg(v_inst_1551_, v_inst_1552_, v_inst_1553_, v_inst_1554_, v_inst_1555_, v_inst_1556_, v_inst_1557_, v_inst_1558_, v_inst_1559_, v_inst_1560_, v_inst_1561_, v_inst_1562_, v_stx_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__0(lean_object* v_toPure_1565_, lean_object* v_declName_1566_, lean_object* v_____r_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_apply_2(v_toPure_1565_, lean_box(0), v_declName_1566_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__1(lean_object* v_declName_1569_, lean_object* v_env_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_addProtected(v_env_1570_, v_declName_1569_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2(lean_object* v_modifiers_1572_, lean_object* v_toPure_1573_, lean_object* v_declName_1574_, lean_object* v_modifyEnv_1575_, lean_object* v___f_1576_, lean_object* v_toBind_1577_, lean_object* v___f_1578_, lean_object* v_____r_1579_){
_start:
{
uint8_t v_isProtected_1580_; 
v_isProtected_1580_ = lean_ctor_get_uint8(v_modifiers_1572_, sizeof(void*)*3 + 1);
if (v_isProtected_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_dec(v___f_1578_);
lean_dec(v_toBind_1577_);
lean_dec_ref(v___f_1576_);
lean_dec(v_modifyEnv_1575_);
v___x_1581_ = lean_apply_2(v_toPure_1573_, lean_box(0), v_declName_1574_);
return v___x_1581_;
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec(v_declName_1574_);
lean_dec(v_toPure_1573_);
v___x_1582_ = lean_apply_1(v_modifyEnv_1575_, v___f_1576_);
v___x_1583_ = lean_apply_4(v_toBind_1577_, lean_box(0), lean_box(0), v___x_1582_, v___f_1578_);
return v___x_1583_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2___boxed(lean_object* v_modifiers_1584_, lean_object* v_toPure_1585_, lean_object* v_declName_1586_, lean_object* v_modifyEnv_1587_, lean_object* v___f_1588_, lean_object* v_toBind_1589_, lean_object* v___f_1590_, lean_object* v_____r_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_Elab_applyVisibility___redArg___lam__2(v_modifiers_1584_, v_toPure_1585_, v_declName_1586_, v_modifyEnv_1587_, v___f_1588_, v_toBind_1589_, v___f_1590_, v_____r_1591_);
lean_dec_ref(v_modifiers_1584_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__3(lean_object* v_toPure_1593_, lean_object* v_modifiers_1594_, lean_object* v_modifyEnv_1595_, lean_object* v_toBind_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_____r_1602_, lean_object* v_declName_1603_){
_start:
{
lean_object* v___f_1604_; lean_object* v___f_1605_; lean_object* v___f_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_inc_n(v_declName_1603_, 3);
lean_inc(v_toPure_1593_);
v___f_1604_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1604_, 0, v_toPure_1593_);
lean_closure_set(v___f_1604_, 1, v_declName_1603_);
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1605_, 0, v_declName_1603_);
lean_inc(v_toBind_1596_);
v___f_1606_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1606_, 0, v_modifiers_1594_);
lean_closure_set(v___f_1606_, 1, v_toPure_1593_);
lean_closure_set(v___f_1606_, 2, v_declName_1603_);
lean_closure_set(v___f_1606_, 3, v_modifyEnv_1595_);
lean_closure_set(v___f_1606_, 4, v___f_1605_);
lean_closure_set(v___f_1606_, 5, v_toBind_1596_);
lean_closure_set(v___f_1606_, 6, v___f_1604_);
v___x_1607_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(v_inst_1597_, v_inst_1598_, v_inst_1599_, v_inst_1600_, v_inst_1601_, v_declName_1603_);
v___x_1608_ = lean_apply_4(v_toBind_1596_, lean_box(0), lean_box(0), v___x_1607_, v___f_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4(lean_object* v_declName_1609_, lean_object* v___f_1610_, lean_object* v_____do__lift_1611_){
_start:
{
lean_object* v_declName_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_declName_1612_ = l_Lean_mkPrivateName(v_____do__lift_1611_, v_declName_1609_);
v___x_1613_ = lean_box(0);
v___x_1614_ = lean_apply_2(v___f_1610_, v___x_1613_, v_declName_1612_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4___boxed(lean_object* v_declName_1615_, lean_object* v___f_1616_, lean_object* v_____do__lift_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Elab_applyVisibility___redArg___lam__4(v_declName_1615_, v___f_1616_, v_____do__lift_1617_);
lean_dec_ref(v_____do__lift_1617_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5(lean_object* v_modifiers_1619_, lean_object* v_toBind_1620_, lean_object* v_getEnv_1621_, lean_object* v___f_1622_, lean_object* v___f_1623_, lean_object* v_declName_1624_, lean_object* v_____do__lift_1625_){
_start:
{
uint8_t v_visibility_1626_; uint8_t v___x_1627_; 
v_visibility_1626_ = lean_ctor_get_uint8(v_modifiers_1619_, sizeof(void*)*3);
v___x_1627_ = l_Lean_Elab_Visibility_isInferredPublic(v_____do__lift_1625_, v_visibility_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; 
lean_dec(v_declName_1624_);
lean_dec(v___f_1623_);
v___x_1628_ = lean_apply_4(v_toBind_1620_, lean_box(0), lean_box(0), v_getEnv_1621_, v___f_1622_);
return v___x_1628_;
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_dec(v___f_1622_);
lean_dec(v_getEnv_1621_);
lean_dec(v_toBind_1620_);
v___x_1629_ = lean_box(0);
v___x_1630_ = lean_apply_2(v___f_1623_, v___x_1629_, v_declName_1624_);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5___boxed(lean_object* v_modifiers_1631_, lean_object* v_toBind_1632_, lean_object* v_getEnv_1633_, lean_object* v___f_1634_, lean_object* v___f_1635_, lean_object* v_declName_1636_, lean_object* v_____do__lift_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_Elab_applyVisibility___redArg___lam__5(v_modifiers_1631_, v_toBind_1632_, v_getEnv_1633_, v___f_1634_, v___f_1635_, v_declName_1636_, v_____do__lift_1637_);
lean_dec_ref(v_____do__lift_1637_);
lean_dec_ref(v_modifiers_1631_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg(lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_modifiers_1644_, lean_object* v_declName_1645_){
_start:
{
lean_object* v_toApplicative_1646_; lean_object* v_toBind_1647_; lean_object* v_getEnv_1648_; lean_object* v_modifyEnv_1649_; lean_object* v_toPure_1650_; lean_object* v___f_1651_; lean_object* v___f_1652_; lean_object* v___f_1653_; lean_object* v___x_1654_; 
v_toApplicative_1646_ = lean_ctor_get(v_inst_1639_, 0);
v_toBind_1647_ = lean_ctor_get(v_inst_1639_, 1);
lean_inc_n(v_toBind_1647_, 3);
v_getEnv_1648_ = lean_ctor_get(v_inst_1640_, 0);
lean_inc_n(v_getEnv_1648_, 2);
v_modifyEnv_1649_ = lean_ctor_get(v_inst_1640_, 1);
lean_inc(v_modifyEnv_1649_);
v_toPure_1650_ = lean_ctor_get(v_toApplicative_1646_, 1);
lean_inc(v_toPure_1650_);
lean_inc_ref(v_modifiers_1644_);
v___f_1651_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__3), 11, 9);
lean_closure_set(v___f_1651_, 0, v_toPure_1650_);
lean_closure_set(v___f_1651_, 1, v_modifiers_1644_);
lean_closure_set(v___f_1651_, 2, v_modifyEnv_1649_);
lean_closure_set(v___f_1651_, 3, v_toBind_1647_);
lean_closure_set(v___f_1651_, 4, v_inst_1639_);
lean_closure_set(v___f_1651_, 5, v_inst_1640_);
lean_closure_set(v___f_1651_, 6, v_inst_1641_);
lean_closure_set(v___f_1651_, 7, v_inst_1642_);
lean_closure_set(v___f_1651_, 8, v_inst_1643_);
lean_inc_ref(v___f_1651_);
lean_inc(v_declName_1645_);
v___f_1652_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_1652_, 0, v_declName_1645_);
lean_closure_set(v___f_1652_, 1, v___f_1651_);
v___f_1653_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1653_, 0, v_modifiers_1644_);
lean_closure_set(v___f_1653_, 1, v_toBind_1647_);
lean_closure_set(v___f_1653_, 2, v_getEnv_1648_);
lean_closure_set(v___f_1653_, 3, v___f_1652_);
lean_closure_set(v___f_1653_, 4, v___f_1651_);
lean_closure_set(v___f_1653_, 5, v_declName_1645_);
v___x_1654_ = lean_apply_4(v_toBind_1647_, lean_box(0), lean_box(0), v_getEnv_1648_, v___f_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility(lean_object* v_m_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_modifiers_1661_, lean_object* v_declName_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1656_, v_inst_1657_, v_inst_1658_, v_inst_1659_, v_inst_1660_, v_modifiers_1661_, v_declName_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0(lean_object* v_toPure_1664_, lean_object* v_____s_1665_){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_box(0);
v___x_1667_ = lean_apply_2(v_toPure_1664_, lean_box(0), v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1(lean_object* v___x_1668_, lean_object* v_toPure_1669_, lean_object* v_r_1670_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1668_);
v___x_1672_ = lean_apply_2(v_toPure_1669_, lean_box(0), v___x_1671_);
return v___x_1672_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0));
v___x_1675_ = l_Lean_stringToMessageData(v___x_1674_);
return v___x_1675_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2));
v___x_1678_ = l_Lean_stringToMessageData(v___x_1677_);
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4));
v___x_1681_ = l_Lean_stringToMessageData(v___x_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2(lean_object* v_pre_1682_, lean_object* v_declName_1683_, lean_object* v___x_1684_, lean_object* v_toPure_1685_, lean_object* v_inst_1686_, lean_object* v_inst_1687_, lean_object* v_toBind_1688_, lean_object* v___f_1689_, lean_object* v_a_1690_, lean_object* v_x_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1693_; uint8_t v___x_1694_; 
lean_inc(v_a_1690_);
lean_inc(v_pre_1682_);
v___x_1693_ = l_Lean_Name_append(v_pre_1682_, v_a_1690_);
v___x_1694_ = lean_name_eq(v___x_1693_, v_declName_1683_);
lean_dec(v___x_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec(v_a_1690_);
lean_dec(v___f_1689_);
lean_dec(v_toBind_1688_);
lean_dec_ref(v_inst_1687_);
lean_dec_ref(v_inst_1686_);
lean_dec(v_declName_1683_);
lean_dec(v_pre_1682_);
v___x_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1684_);
v___x_1696_ = lean_apply_2(v_toPure_1685_, lean_box(0), v___x_1695_);
return v___x_1696_;
}
else
{
lean_object* v___x_1697_; uint8_t v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_dec(v_toPure_1685_);
v___x_1697_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1698_ = 0;
v___x_1699_ = l_Lean_MessageData_ofConstName(v_declName_1683_, v___x_1698_);
v___x_1700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1697_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_1702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1700_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___x_1703_ = l_Lean_MessageData_ofName(v_pre_1682_);
v___x_1704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1702_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
v___x_1705_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_1706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1704_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = l_Lean_MessageData_ofName(v_a_1690_);
v___x_1708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1706_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = l_Lean_throwError___redArg(v_inst_1686_, v_inst_1687_, v___x_1710_);
v___x_1712_ = lean_apply_4(v_toBind_1688_, lean_box(0), lean_box(0), v___x_1711_, v___f_1689_);
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(lean_object* v_pre_1713_, uint8_t v___x_1714_, lean_object* v_toPure_1715_, lean_object* v_declName_1716_, lean_object* v_inst_1717_, lean_object* v_inst_1718_, lean_object* v_toBind_1719_, lean_object* v___f_1720_, lean_object* v_____do__lift_1721_){
_start:
{
lean_object* v_fieldNames_1722_; lean_object* v___x_1723_; lean_object* v___f_1724_; lean_object* v___f_1725_; size_t v_sz_1726_; size_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_inc(v_pre_1713_);
v_fieldNames_1722_ = l_Lean_getStructureFieldsFlattened(v_____do__lift_1721_, v_pre_1713_, v___x_1714_);
v___x_1723_ = lean_box(0);
lean_inc(v_toPure_1715_);
v___f_1724_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1724_, 0, v___x_1723_);
lean_closure_set(v___f_1724_, 1, v_toPure_1715_);
lean_inc(v_toBind_1719_);
lean_inc_ref(v_inst_1717_);
v___f_1725_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2), 11, 8);
lean_closure_set(v___f_1725_, 0, v_pre_1713_);
lean_closure_set(v___f_1725_, 1, v_declName_1716_);
lean_closure_set(v___f_1725_, 2, v___x_1723_);
lean_closure_set(v___f_1725_, 3, v_toPure_1715_);
lean_closure_set(v___f_1725_, 4, v_inst_1717_);
lean_closure_set(v___f_1725_, 5, v_inst_1718_);
lean_closure_set(v___f_1725_, 6, v_toBind_1719_);
lean_closure_set(v___f_1725_, 7, v___f_1724_);
v_sz_1726_ = lean_array_size(v_fieldNames_1722_);
v___x_1727_ = ((size_t)0ULL);
v___x_1728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1717_, v_fieldNames_1722_, v___f_1725_, v_sz_1726_, v___x_1727_, v___x_1723_);
v___x_1729_ = lean_apply_4(v_toBind_1719_, lean_box(0), lean_box(0), v___x_1728_, v___f_1720_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed(lean_object* v_pre_1730_, lean_object* v___x_1731_, lean_object* v_toPure_1732_, lean_object* v_declName_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_toBind_1736_, lean_object* v___f_1737_, lean_object* v_____do__lift_1738_){
_start:
{
uint8_t v___x_672__boxed_1739_; lean_object* v_res_1740_; 
v___x_672__boxed_1739_ = lean_unbox(v___x_1731_);
v_res_1740_ = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(v_pre_1730_, v___x_672__boxed_1739_, v_toPure_1732_, v_declName_1733_, v_inst_1734_, v_inst_1735_, v_toBind_1736_, v___f_1737_, v_____do__lift_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4(lean_object* v_pre_1741_, lean_object* v_toPure_1742_, lean_object* v_declName_1743_, lean_object* v_inst_1744_, lean_object* v_inst_1745_, lean_object* v_toBind_1746_, lean_object* v___f_1747_, lean_object* v_getEnv_1748_, lean_object* v_____do__lift_1749_){
_start:
{
uint8_t v___x_1750_; 
lean_inc(v_pre_1741_);
v___x_1750_ = l_Lean_isStructure(v_____do__lift_1749_, v_pre_1741_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec(v_getEnv_1748_);
lean_dec(v___f_1747_);
lean_dec(v_toBind_1746_);
lean_dec_ref(v_inst_1745_);
lean_dec_ref(v_inst_1744_);
lean_dec(v_declName_1743_);
lean_dec(v_pre_1741_);
v___x_1751_ = lean_box(0);
v___x_1752_ = lean_apply_2(v_toPure_1742_, lean_box(0), v___x_1751_);
return v___x_1752_;
}
else
{
lean_object* v___x_1753_; lean_object* v___f_1754_; lean_object* v___x_1755_; 
v___x_1753_ = lean_box(v___x_1750_);
lean_inc(v_toBind_1746_);
v___f_1754_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1754_, 0, v_pre_1741_);
lean_closure_set(v___f_1754_, 1, v___x_1753_);
lean_closure_set(v___f_1754_, 2, v_toPure_1742_);
lean_closure_set(v___f_1754_, 3, v_declName_1743_);
lean_closure_set(v___f_1754_, 4, v_inst_1744_);
lean_closure_set(v___f_1754_, 5, v_inst_1745_);
lean_closure_set(v___f_1754_, 6, v_toBind_1746_);
lean_closure_set(v___f_1754_, 7, v___f_1747_);
v___x_1755_ = lean_apply_4(v_toBind_1746_, lean_box(0), lean_box(0), v_getEnv_1748_, v___f_1754_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg(lean_object* v_inst_1756_, lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_declName_1759_){
_start:
{
if (lean_obj_tag(v_declName_1759_) == 1)
{
lean_object* v_toApplicative_1760_; lean_object* v_toBind_1761_; lean_object* v_toPure_1762_; lean_object* v_pre_1763_; lean_object* v_getEnv_1764_; lean_object* v___f_1765_; lean_object* v___f_1766_; lean_object* v___x_1767_; 
v_toApplicative_1760_ = lean_ctor_get(v_inst_1756_, 0);
v_toBind_1761_ = lean_ctor_get(v_inst_1756_, 1);
lean_inc_n(v_toBind_1761_, 2);
v_toPure_1762_ = lean_ctor_get(v_toApplicative_1760_, 1);
lean_inc_n(v_toPure_1762_, 2);
v_pre_1763_ = lean_ctor_get(v_declName_1759_, 0);
lean_inc(v_pre_1763_);
v_getEnv_1764_ = lean_ctor_get(v_inst_1757_, 0);
lean_inc_n(v_getEnv_1764_, 2);
lean_dec_ref(v_inst_1757_);
v___f_1765_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1765_, 0, v_toPure_1762_);
v___f_1766_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1766_, 0, v_pre_1763_);
lean_closure_set(v___f_1766_, 1, v_toPure_1762_);
lean_closure_set(v___f_1766_, 2, v_declName_1759_);
lean_closure_set(v___f_1766_, 3, v_inst_1756_);
lean_closure_set(v___f_1766_, 4, v_inst_1758_);
lean_closure_set(v___f_1766_, 5, v_toBind_1761_);
lean_closure_set(v___f_1766_, 6, v___f_1765_);
lean_closure_set(v___f_1766_, 7, v_getEnv_1764_);
v___x_1767_ = lean_apply_4(v_toBind_1761_, lean_box(0), lean_box(0), v_getEnv_1764_, v___f_1766_);
return v___x_1767_;
}
else
{
lean_object* v_toApplicative_1768_; lean_object* v_toPure_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_toApplicative_1768_ = lean_ctor_get(v_inst_1756_, 0);
lean_inc_ref(v_toApplicative_1768_);
lean_dec(v_declName_1759_);
lean_dec_ref(v_inst_1758_);
lean_dec_ref(v_inst_1757_);
lean_dec_ref(v_inst_1756_);
v_toPure_1769_ = lean_ctor_get(v_toApplicative_1768_, 1);
lean_inc(v_toPure_1769_);
lean_dec_ref(v_toApplicative_1768_);
v___x_1770_ = lean_box(0);
v___x_1771_ = lean_apply_2(v_toPure_1769_, lean_box(0), v___x_1770_);
return v___x_1771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField(lean_object* v_m_1772_, lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_inst_1775_, lean_object* v_declName_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1773_, v_inst_1774_, v_inst_1775_, v_declName_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__0(lean_object* v_toApplicative_1778_, lean_object* v_declName_1779_, lean_object* v_shortName_1780_, lean_object* v_____r_1781_){
_start:
{
lean_object* v_toPure_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_toPure_1782_ = lean_ctor_get(v_toApplicative_1778_, 1);
lean_inc(v_toPure_1782_);
lean_dec_ref(v_toApplicative_1778_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v_declName_1779_);
lean_ctor_set(v___x_1783_, 1, v_shortName_1780_);
v___x_1784_ = lean_apply_2(v_toPure_1782_, lean_box(0), v___x_1783_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0));
v___x_1787_ = l_Lean_stringToMessageData(v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2(lean_object* v_modifiers_1788_, lean_object* v_toApplicative_1789_, lean_object* v_shortName_1790_, lean_object* v_currNamespace_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_toBind_1794_, lean_object* v_declName_1795_){
_start:
{
uint8_t v_isProtected_1796_; 
v_isProtected_1796_ = lean_ctor_get_uint8(v_modifiers_1788_, sizeof(void*)*3 + 1);
if (v_isProtected_1796_ == 0)
{
lean_object* v_toPure_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec(v_toBind_1794_);
lean_dec_ref(v_inst_1793_);
lean_dec_ref(v_inst_1792_);
lean_dec(v_currNamespace_1791_);
v_toPure_1797_ = lean_ctor_get(v_toApplicative_1789_, 1);
lean_inc(v_toPure_1797_);
lean_dec_ref(v_toApplicative_1789_);
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_declName_1795_);
lean_ctor_set(v___x_1798_, 1, v_shortName_1790_);
v___x_1799_ = lean_apply_2(v_toPure_1797_, lean_box(0), v___x_1798_);
return v___x_1799_;
}
else
{
if (lean_obj_tag(v_currNamespace_1791_) == 1)
{
lean_object* v_str_1800_; lean_object* v_toPure_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_dec(v_toBind_1794_);
lean_dec_ref(v_inst_1793_);
lean_dec_ref(v_inst_1792_);
v_str_1800_ = lean_ctor_get(v_currNamespace_1791_, 1);
lean_inc_ref(v_str_1800_);
lean_dec_ref(v_currNamespace_1791_);
v_toPure_1801_ = lean_ctor_get(v_toApplicative_1789_, 1);
lean_inc(v_toPure_1801_);
lean_dec_ref(v_toApplicative_1789_);
v___x_1802_ = lean_box(0);
v___x_1803_ = l_Lean_Name_str___override(v___x_1802_, v_str_1800_);
v___x_1804_ = l_Lean_Name_append(v___x_1803_, v_shortName_1790_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v_declName_1795_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = lean_apply_2(v_toPure_1801_, lean_box(0), v___x_1805_);
return v___x_1806_;
}
else
{
lean_object* v___f_1807_; uint8_t v___x_1808_; 
lean_dec(v_currNamespace_1791_);
lean_inc(v_shortName_1790_);
lean_inc(v_declName_1795_);
lean_inc_ref(v_toApplicative_1789_);
v___f_1807_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1807_, 0, v_toApplicative_1789_);
lean_closure_set(v___f_1807_, 1, v_declName_1795_);
lean_closure_set(v___f_1807_, 2, v_shortName_1790_);
v___x_1808_ = l_Lean_Name_isAtomic(v_shortName_1790_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec_ref(v___f_1807_);
lean_dec(v_toBind_1794_);
lean_dec_ref(v_inst_1793_);
lean_dec_ref(v_inst_1792_);
v___x_1809_ = lean_box(0);
v___x_1810_ = l_Lean_Elab_mkDeclName___redArg___lam__0(v_toApplicative_1789_, v_declName_1795_, v_shortName_1790_, v___x_1809_);
return v___x_1810_;
}
else
{
lean_object* v___f_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec(v_declName_1795_);
lean_dec(v_shortName_1790_);
lean_dec_ref(v_toApplicative_1789_);
v___f_1811_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1811_, 0, v___f_1807_);
v___x_1812_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_1813_ = l_Lean_throwError___redArg(v_inst_1792_, v_inst_1793_, v___x_1812_);
v___x_1814_ = lean_apply_4(v_toBind_1794_, lean_box(0), lean_box(0), v___x_1813_, v___f_1811_);
return v___x_1814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2___boxed(lean_object* v_modifiers_1815_, lean_object* v_toApplicative_1816_, lean_object* v_shortName_1817_, lean_object* v_currNamespace_1818_, lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_toBind_1821_, lean_object* v_declName_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_Elab_mkDeclName___redArg___lam__2(v_modifiers_1815_, v_toApplicative_1816_, v_shortName_1817_, v_currNamespace_1818_, v_inst_1819_, v_inst_1820_, v_toBind_1821_, v_declName_1822_);
lean_dec_ref(v_modifiers_1815_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__1(lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_, lean_object* v_inst_1827_, lean_object* v_inst_1828_, lean_object* v_modifiers_1829_, lean_object* v___y_1830_, lean_object* v_toBind_1831_, lean_object* v___f_1832_, lean_object* v_____r_1833_){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1824_, v_inst_1825_, v_inst_1826_, v_inst_1827_, v_inst_1828_, v_modifiers_1829_, v___y_1830_);
v___x_1835_ = lean_apply_4(v_toBind_1831_, lean_box(0), lean_box(0), v___x_1834_, v___f_1832_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3(lean_object* v_modifiers_1836_, lean_object* v_toApplicative_1837_, lean_object* v_inst_1838_, lean_object* v_inst_1839_, lean_object* v_toBind_1840_, lean_object* v_inst_1841_, lean_object* v_inst_1842_, lean_object* v_inst_1843_, lean_object* v___y_1844_, lean_object* v_____r_1845_, lean_object* v_shortName_1846_, lean_object* v_currNamespace_1847_){
_start:
{
lean_object* v___f_1848_; lean_object* v___f_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_inc_n(v_toBind_1840_, 2);
lean_inc_ref_n(v_inst_1839_, 2);
lean_inc_ref_n(v_inst_1838_, 2);
lean_inc_ref(v_modifiers_1836_);
v___f_1848_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1848_, 0, v_modifiers_1836_);
lean_closure_set(v___f_1848_, 1, v_toApplicative_1837_);
lean_closure_set(v___f_1848_, 2, v_shortName_1846_);
lean_closure_set(v___f_1848_, 3, v_currNamespace_1847_);
lean_closure_set(v___f_1848_, 4, v_inst_1838_);
lean_closure_set(v___f_1848_, 5, v_inst_1839_);
lean_closure_set(v___f_1848_, 6, v_toBind_1840_);
lean_inc(v___y_1844_);
lean_inc_ref(v_inst_1841_);
v___f_1849_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1849_, 0, v_inst_1838_);
lean_closure_set(v___f_1849_, 1, v_inst_1841_);
lean_closure_set(v___f_1849_, 2, v_inst_1839_);
lean_closure_set(v___f_1849_, 3, v_inst_1842_);
lean_closure_set(v___f_1849_, 4, v_inst_1843_);
lean_closure_set(v___f_1849_, 5, v_modifiers_1836_);
lean_closure_set(v___f_1849_, 6, v___y_1844_);
lean_closure_set(v___f_1849_, 7, v_toBind_1840_);
lean_closure_set(v___f_1849_, 8, v___f_1848_);
v___x_1850_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1838_, v_inst_1841_, v_inst_1839_, v___y_1844_);
v___x_1851_ = lean_apply_4(v_toBind_1840_, lean_box(0), lean_box(0), v___x_1850_, v___f_1849_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__4(lean_object* v___f_1852_, lean_object* v_shortName_1853_, lean_object* v_currNamespace_1854_, lean_object* v_____r_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_apply_3(v___f_1852_, v_____r_1855_, v_shortName_1853_, v_currNamespace_1854_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5(lean_object* v_modifiers_1857_, lean_object* v_toApplicative_1858_, lean_object* v_inst_1859_, lean_object* v_inst_1860_, lean_object* v_toBind_1861_, lean_object* v_inst_1862_, lean_object* v_inst_1863_, lean_object* v_inst_1864_, uint8_t v_isRootName_1865_, lean_object* v_shortName_1866_, lean_object* v_currNamespace_1867_, lean_object* v_name_1868_, lean_object* v___x_1869_, lean_object* v_imported_1870_, lean_object* v_ctx_1871_, lean_object* v_scopes_1872_, lean_object* v_____r_1873_){
_start:
{
lean_object* v___y_1875_; 
if (v_isRootName_1865_ == 0)
{
lean_object* v___x_1894_; 
lean_dec(v_scopes_1872_);
lean_dec(v_ctx_1871_);
lean_dec(v_imported_1870_);
lean_inc(v_shortName_1866_);
lean_inc(v_currNamespace_1867_);
v___x_1894_ = l_Lean_Name_append(v_currNamespace_1867_, v_shortName_1866_);
v___y_1875_ = v___x_1894_;
goto v___jp_1874_;
}
else
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1895_ = lean_box(0);
lean_inc(v_name_1868_);
v___x_1896_ = l_Lean_Name_replacePrefix(v_name_1868_, v___x_1869_, v___x_1895_);
v___x_1897_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set(v___x_1897_, 1, v_imported_1870_);
lean_ctor_set(v___x_1897_, 2, v_ctx_1871_);
lean_ctor_set(v___x_1897_, 3, v_scopes_1872_);
v___x_1898_ = l_Lean_MacroScopesView_review(v___x_1897_);
v___y_1875_ = v___x_1898_;
goto v___jp_1874_;
}
v___jp_1874_:
{
lean_object* v___f_1876_; 
lean_inc(v___y_1875_);
lean_inc_ref(v_inst_1864_);
lean_inc(v_inst_1863_);
lean_inc_ref(v_inst_1862_);
lean_inc(v_toBind_1861_);
lean_inc_ref(v_inst_1860_);
lean_inc_ref(v_inst_1859_);
lean_inc_ref(v_toApplicative_1858_);
lean_inc_ref(v_modifiers_1857_);
v___f_1876_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__3), 12, 9);
lean_closure_set(v___f_1876_, 0, v_modifiers_1857_);
lean_closure_set(v___f_1876_, 1, v_toApplicative_1858_);
lean_closure_set(v___f_1876_, 2, v_inst_1859_);
lean_closure_set(v___f_1876_, 3, v_inst_1860_);
lean_closure_set(v___f_1876_, 4, v_toBind_1861_);
lean_closure_set(v___f_1876_, 5, v_inst_1862_);
lean_closure_set(v___f_1876_, 6, v_inst_1863_);
lean_closure_set(v___f_1876_, 7, v_inst_1864_);
lean_closure_set(v___f_1876_, 8, v___y_1875_);
if (v_isRootName_1865_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec_ref(v___f_1876_);
lean_dec(v_name_1868_);
v___x_1877_ = lean_box(0);
v___x_1878_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1857_, v_toApplicative_1858_, v_inst_1859_, v_inst_1860_, v_toBind_1861_, v_inst_1862_, v_inst_1863_, v_inst_1864_, v___y_1875_, v___x_1877_, v_shortName_1866_, v_currNamespace_1867_);
return v___x_1878_;
}
else
{
if (lean_obj_tag(v_name_1868_) == 1)
{
lean_object* v_pre_1879_; lean_object* v_str_1880_; lean_object* v___x_1881_; lean_object* v_shortName_1882_; lean_object* v_currNamespace_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec_ref(v___f_1876_);
lean_dec(v_currNamespace_1867_);
lean_dec(v_shortName_1866_);
v_pre_1879_ = lean_ctor_get(v_name_1868_, 0);
lean_inc(v_pre_1879_);
v_str_1880_ = lean_ctor_get(v_name_1868_, 1);
lean_inc_ref(v_str_1880_);
lean_dec_ref(v_name_1868_);
v___x_1881_ = lean_box(0);
v_shortName_1882_ = l_Lean_Name_str___override(v___x_1881_, v_str_1880_);
v_currNamespace_1883_ = l_Lean_Name_replacePrefix(v_pre_1879_, v___x_1869_, v___x_1881_);
v___x_1884_ = lean_box(0);
v___x_1885_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1857_, v_toApplicative_1858_, v_inst_1859_, v_inst_1860_, v_toBind_1861_, v_inst_1862_, v_inst_1863_, v_inst_1864_, v___y_1875_, v___x_1884_, v_shortName_1882_, v_currNamespace_1883_);
return v___x_1885_;
}
else
{
lean_object* v___f_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_dec(v___y_1875_);
lean_dec_ref(v_inst_1864_);
lean_dec(v_inst_1863_);
lean_dec_ref(v_inst_1862_);
lean_dec_ref(v_toApplicative_1858_);
lean_dec_ref(v_modifiers_1857_);
v___f_1886_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__4), 4, 3);
lean_closure_set(v___f_1886_, 0, v___f_1876_);
lean_closure_set(v___f_1886_, 1, v_shortName_1866_);
lean_closure_set(v___f_1886_, 2, v_currNamespace_1867_);
v___x_1887_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1888_ = l_Lean_MessageData_ofName(v_name_1868_);
v___x_1889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1887_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = l_Lean_throwError___redArg(v_inst_1859_, v_inst_1860_, v___x_1891_);
v___x_1893_ = lean_apply_4(v_toBind_1861_, lean_box(0), lean_box(0), v___x_1892_, v___f_1886_);
return v___x_1893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_modifiers_1899_ = _args[0];
lean_object* v_toApplicative_1900_ = _args[1];
lean_object* v_inst_1901_ = _args[2];
lean_object* v_inst_1902_ = _args[3];
lean_object* v_toBind_1903_ = _args[4];
lean_object* v_inst_1904_ = _args[5];
lean_object* v_inst_1905_ = _args[6];
lean_object* v_inst_1906_ = _args[7];
lean_object* v_isRootName_1907_ = _args[8];
lean_object* v_shortName_1908_ = _args[9];
lean_object* v_currNamespace_1909_ = _args[10];
lean_object* v_name_1910_ = _args[11];
lean_object* v___x_1911_ = _args[12];
lean_object* v_imported_1912_ = _args[13];
lean_object* v_ctx_1913_ = _args[14];
lean_object* v_scopes_1914_ = _args[15];
lean_object* v_____r_1915_ = _args[16];
_start:
{
uint8_t v_isRootName_boxed_1916_; lean_object* v_res_1917_; 
v_isRootName_boxed_1916_ = lean_unbox(v_isRootName_1907_);
v_res_1917_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1899_, v_toApplicative_1900_, v_inst_1901_, v_inst_1902_, v_toBind_1903_, v_inst_1904_, v_inst_1905_, v_inst_1906_, v_isRootName_boxed_1916_, v_shortName_1908_, v_currNamespace_1909_, v_name_1910_, v___x_1911_, v_imported_1912_, v_ctx_1913_, v_scopes_1914_, v_____r_1915_);
lean_dec(v___x_1911_);
return v_res_1917_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___closed__3(void){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__2));
v___x_1923_ = l_Lean_stringToMessageData(v___x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg(lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_inst_1927_, lean_object* v_inst_1928_, lean_object* v_currNamespace_1929_, lean_object* v_modifiers_1930_, lean_object* v_shortName_1931_){
_start:
{
lean_object* v_view_1932_; lean_object* v_name_1933_; lean_object* v_imported_1934_; lean_object* v_ctx_1935_; lean_object* v_scopes_1936_; lean_object* v_toApplicative_1937_; lean_object* v_toBind_1938_; lean_object* v___x_1939_; uint8_t v_isRootName_1940_; lean_object* v___x_1941_; lean_object* v___f_1942_; uint8_t v___x_1943_; 
lean_inc_n(v_shortName_1931_, 2);
v_view_1932_ = l_Lean_extractMacroScopes(v_shortName_1931_);
v_name_1933_ = lean_ctor_get(v_view_1932_, 0);
lean_inc_n(v_name_1933_, 2);
v_imported_1934_ = lean_ctor_get(v_view_1932_, 1);
lean_inc_n(v_imported_1934_, 2);
v_ctx_1935_ = lean_ctor_get(v_view_1932_, 2);
lean_inc_n(v_ctx_1935_, 2);
v_scopes_1936_ = lean_ctor_get(v_view_1932_, 3);
lean_inc_n(v_scopes_1936_, 2);
lean_dec_ref(v_view_1932_);
v_toApplicative_1937_ = lean_ctor_get(v_inst_1924_, 0);
v_toBind_1938_ = lean_ctor_get(v_inst_1924_, 1);
lean_inc_n(v_toBind_1938_, 2);
v___x_1939_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_1940_ = l_Lean_Name_isPrefixOf(v___x_1939_, v_name_1933_);
v___x_1941_ = lean_box(v_isRootName_1940_);
lean_inc(v_currNamespace_1929_);
lean_inc_ref(v_inst_1928_);
lean_inc(v_inst_1927_);
lean_inc_ref(v_inst_1925_);
lean_inc_ref(v_inst_1926_);
lean_inc_ref(v_inst_1924_);
lean_inc_ref(v_toApplicative_1937_);
lean_inc_ref(v_modifiers_1930_);
v___f_1942_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1942_, 0, v_modifiers_1930_);
lean_closure_set(v___f_1942_, 1, v_toApplicative_1937_);
lean_closure_set(v___f_1942_, 2, v_inst_1924_);
lean_closure_set(v___f_1942_, 3, v_inst_1926_);
lean_closure_set(v___f_1942_, 4, v_toBind_1938_);
lean_closure_set(v___f_1942_, 5, v_inst_1925_);
lean_closure_set(v___f_1942_, 6, v_inst_1927_);
lean_closure_set(v___f_1942_, 7, v_inst_1928_);
lean_closure_set(v___f_1942_, 8, v___x_1941_);
lean_closure_set(v___f_1942_, 9, v_shortName_1931_);
lean_closure_set(v___f_1942_, 10, v_currNamespace_1929_);
lean_closure_set(v___f_1942_, 11, v_name_1933_);
lean_closure_set(v___f_1942_, 12, v___x_1939_);
lean_closure_set(v___f_1942_, 13, v_imported_1934_);
lean_closure_set(v___f_1942_, 14, v_ctx_1935_);
lean_closure_set(v___f_1942_, 15, v_scopes_1936_);
v___x_1943_ = lean_name_eq(v_name_1933_, v___x_1939_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
lean_inc_ref(v_toApplicative_1937_);
lean_dec_ref(v___f_1942_);
v___x_1944_ = lean_box(0);
v___x_1945_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1930_, v_toApplicative_1937_, v_inst_1924_, v_inst_1926_, v_toBind_1938_, v_inst_1925_, v_inst_1927_, v_inst_1928_, v_isRootName_1940_, v_shortName_1931_, v_currNamespace_1929_, v_name_1933_, v___x_1939_, v_imported_1934_, v_ctx_1935_, v_scopes_1936_, v___x_1944_);
return v___x_1945_;
}
else
{
lean_object* v___f_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec(v_scopes_1936_);
lean_dec(v_ctx_1935_);
lean_dec(v_imported_1934_);
lean_dec(v_name_1933_);
lean_dec(v_shortName_1931_);
lean_dec_ref(v_modifiers_1930_);
lean_dec(v_currNamespace_1929_);
lean_dec_ref(v_inst_1928_);
lean_dec(v_inst_1927_);
lean_dec_ref(v_inst_1925_);
v___f_1946_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1946_, 0, v___f_1942_);
v___x_1947_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_1948_ = l_Lean_throwError___redArg(v_inst_1924_, v_inst_1926_, v___x_1947_);
v___x_1949_ = lean_apply_4(v_toBind_1938_, lean_box(0), lean_box(0), v___x_1948_, v___f_1946_);
return v___x_1949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName(lean_object* v_m_1950_, lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_inst_1953_, lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_currNamespace_1956_, lean_object* v_modifiers_1957_, lean_object* v_shortName_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lean_Elab_mkDeclName___redArg(v_inst_1951_, v_inst_1952_, v_inst_1953_, v_inst_1954_, v_inst_1955_, v_currNamespace_1956_, v_modifiers_1957_, v_shortName_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore(lean_object* v_declId_1969_){
_start:
{
uint8_t v___x_1970_; 
v___x_1970_ = l_Lean_Syntax_isIdent(v_declId_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v_id_1973_; lean_object* v___x_1974_; lean_object* v_optUnivDeclStx_1975_; lean_object* v___x_1976_; 
v___x_1971_ = lean_unsigned_to_nat(0u);
v___x_1972_ = l_Lean_Syntax_getArg(v_declId_1969_, v___x_1971_);
v_id_1973_ = l_Lean_Syntax_getId(v___x_1972_);
lean_dec(v___x_1972_);
v___x_1974_ = lean_unsigned_to_nat(1u);
v_optUnivDeclStx_1975_ = l_Lean_Syntax_getArg(v_declId_1969_, v___x_1974_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_id_1973_);
lean_ctor_set(v___x_1976_, 1, v_optUnivDeclStx_1975_);
return v___x_1976_;
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = l_Lean_Syntax_getId(v_declId_1969_);
v___x_1978_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__3));
v___x_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1977_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
return v___x_1979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore___boxed(lean_object* v_declId_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_Elab_expandDeclIdCore(v_declId_1980_);
lean_dec(v_declId_1980_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(lean_object* v_msgData_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; lean_object* v_env_1989_; lean_object* v___x_1990_; lean_object* v_mctx_1991_; lean_object* v_lctx_1992_; lean_object* v_options_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1988_ = lean_st_ref_get(v___y_1986_);
v_env_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc_ref(v_env_1989_);
lean_dec(v___x_1988_);
v___x_1990_ = lean_st_ref_get(v___y_1984_);
v_mctx_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc_ref(v_mctx_1991_);
lean_dec(v___x_1990_);
v_lctx_1992_ = lean_ctor_get(v___y_1983_, 2);
v_options_1993_ = lean_ctor_get(v___y_1985_, 2);
lean_inc_ref(v_options_1993_);
lean_inc_ref(v_lctx_1992_);
v___x_1994_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1994_, 0, v_env_1989_);
lean_ctor_set(v___x_1994_, 1, v_mctx_1991_);
lean_ctor_set(v___x_1994_, 2, v_lctx_1992_);
lean_ctor_set(v___x_1994_, 3, v_options_1993_);
v___x_1995_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
lean_ctor_set(v___x_1995_, 1, v_msgData_1982_);
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msgData_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2003_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(lean_object* v_opts_2004_, lean_object* v_opt_2005_){
_start:
{
lean_object* v_name_2006_; lean_object* v_defValue_2007_; lean_object* v_map_2008_; lean_object* v___x_2009_; 
v_name_2006_ = lean_ctor_get(v_opt_2005_, 0);
v_defValue_2007_ = lean_ctor_get(v_opt_2005_, 1);
v_map_2008_ = lean_ctor_get(v_opts_2004_, 0);
v___x_2009_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2008_, v_name_2006_);
if (lean_obj_tag(v___x_2009_) == 0)
{
uint8_t v___x_2010_; 
v___x_2010_ = lean_unbox(v_defValue_2007_);
return v___x_2010_;
}
else
{
lean_object* v_val_2011_; 
v_val_2011_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_val_2011_);
lean_dec_ref(v___x_2009_);
if (lean_obj_tag(v_val_2011_) == 1)
{
uint8_t v_v_2012_; 
v_v_2012_ = lean_ctor_get_uint8(v_val_2011_, 0);
lean_dec_ref(v_val_2011_);
return v_v_2012_;
}
else
{
uint8_t v___x_2013_; 
lean_dec(v_val_2011_);
v___x_2013_ = lean_unbox(v_defValue_2007_);
return v___x_2013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_opts_2014_, lean_object* v_opt_2015_){
_start:
{
uint8_t v_res_2016_; lean_object* v_r_2017_; 
v_res_2016_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_opts_2014_, v_opt_2015_);
lean_dec_ref(v_opt_2015_);
lean_dec_ref(v_opts_2014_);
v_r_2017_ = lean_box(v_res_2016_);
return v_r_2017_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_box(1);
v___x_2019_ = l_Lean_MessageData_ofFormat(v___x_2018_);
return v___x_2019_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3(void){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2));
v___x_2024_ = l_Lean_MessageData_ofFormat(v___x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(lean_object* v_x_2025_, lean_object* v_x_2026_){
_start:
{
if (lean_obj_tag(v_x_2026_) == 0)
{
return v_x_2025_;
}
else
{
lean_object* v_head_2027_; lean_object* v_tail_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2050_; 
v_head_2027_ = lean_ctor_get(v_x_2026_, 0);
v_tail_2028_ = lean_ctor_get(v_x_2026_, 1);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_x_2026_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2030_ = v_x_2026_;
v_isShared_2031_ = v_isSharedCheck_2050_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_tail_2028_);
lean_inc(v_head_2027_);
lean_dec(v_x_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2050_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v_before_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2048_; 
v_before_2032_ = lean_ctor_get(v_head_2027_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_head_2027_);
if (v_isSharedCheck_2048_ == 0)
{
lean_object* v_unused_2049_; 
v_unused_2049_ = lean_ctor_get(v_head_2027_, 1);
lean_dec(v_unused_2049_);
v___x_2034_ = v_head_2027_;
v_isShared_2035_ = v_isSharedCheck_2048_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_before_2032_);
lean_dec(v_head_2027_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2048_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2036_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_2035_ == 0)
{
lean_ctor_set_tag(v___x_2034_, 7);
lean_ctor_set(v___x_2034_, 1, v___x_2036_);
lean_ctor_set(v___x_2034_, 0, v_x_2025_);
v___x_2038_ = v___x_2034_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_x_2025_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2039_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3);
if (v_isShared_2031_ == 0)
{
lean_ctor_set_tag(v___x_2030_, 7);
lean_ctor_set(v___x_2030_, 1, v___x_2039_);
lean_ctor_set(v___x_2030_, 0, v___x_2038_);
v___x_2041_ = v___x_2030_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2042_ = l_Lean_MessageData_ofSyntax(v_before_2032_);
v___x_2043_ = l_Lean_indentD(v___x_2042_);
v___x_2044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2041_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v_x_2025_ = v___x_2044_;
v_x_2026_ = v_tail_2028_;
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
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1));
v___x_2055_ = l_Lean_MessageData_ofFormat(v___x_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_2056_, lean_object* v_macroStack_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_options_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
v_options_2060_ = lean_ctor_get(v___y_2058_, 2);
v___x_2061_ = l_Lean_Elab_pp_macroStack;
v___x_2062_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_options_2060_, v___x_2061_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; 
lean_dec(v_macroStack_2057_);
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_msgData_2056_);
return v___x_2063_;
}
else
{
if (lean_obj_tag(v_macroStack_2057_) == 0)
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v_msgData_2056_);
return v___x_2064_;
}
else
{
lean_object* v_head_2065_; lean_object* v_after_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2081_; 
v_head_2065_ = lean_ctor_get(v_macroStack_2057_, 0);
lean_inc(v_head_2065_);
v_after_2066_ = lean_ctor_get(v_head_2065_, 1);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_head_2065_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; 
v_unused_2082_ = lean_ctor_get(v_head_2065_, 0);
lean_dec(v_unused_2082_);
v___x_2068_ = v_head_2065_;
v_isShared_2069_ = v_isSharedCheck_2081_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_after_2066_);
lean_dec(v_head_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2081_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_2069_ == 0)
{
lean_ctor_set_tag(v___x_2068_, 7);
lean_ctor_set(v___x_2068_, 1, v___x_2070_);
lean_ctor_set(v___x_2068_, 0, v_msgData_2056_);
v___x_2072_ = v___x_2068_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_msgData_2056_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v_msgData_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2073_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = l_Lean_MessageData_ofSyntax(v_after_2066_);
v___x_2076_ = l_Lean_indentD(v___x_2075_);
v_msgData_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2077_, 0, v___x_2074_);
lean_ctor_set(v_msgData_2077_, 1, v___x_2076_);
v___x_2078_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(v_msgData_2077_, v_macroStack_2057_);
v___x_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
return v___x_2079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_2083_, lean_object* v_macroStack_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_2083_, v_macroStack_2084_, v___y_2085_);
lean_dec_ref(v___y_2085_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(lean_object* v_msg_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_ref_2096_; lean_object* v___x_2097_; lean_object* v_a_2098_; lean_object* v_macroStack_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2110_; 
v_ref_2096_ = lean_ctor_get(v___y_2093_, 5);
v___x_2097_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msg_2088_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref(v___x_2097_);
v_macroStack_2099_ = lean_ctor_get(v___y_2089_, 1);
v___x_2100_ = l_Lean_Elab_getBetterRef(v_ref_2096_, v_macroStack_2099_);
lean_inc(v_macroStack_2099_);
v___x_2101_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_a_2098_, v_macroStack_2099_, v___y_2093_);
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2100_);
lean_ctor_set(v___x_2106_, 1, v_a_2102_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set_tag(v___x_2104_, 1);
lean_ctor_set(v___x_2104_, 0, v___x_2106_);
v___x_2108_ = v___x_2104_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg___boxed(lean_object* v_msg_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(lean_object* v_env_2120_, lean_object* v_declName_2121_, lean_object* v___f_2122_, lean_object* v_addInfo_2123_, lean_object* v_____r_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; uint8_t v___x_2133_; uint8_t v___x_2134_; 
lean_inc(v_declName_2121_);
v___x_2132_ = l_Lean_mkPrivateName(v_env_2120_, v_declName_2121_);
v___x_2133_ = 1;
lean_inc(v___x_2132_);
v___x_2134_ = l_Lean_Environment_contains(v_env_2120_, v___x_2132_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec(v___x_2132_);
lean_dec_ref(v_addInfo_2123_);
lean_dec(v_declName_2121_);
v___x_2135_ = lean_box(0);
lean_inc(v___y_2130_);
lean_inc_ref(v___y_2129_);
lean_inc(v___y_2128_);
lean_inc_ref(v___y_2127_);
lean_inc(v___y_2126_);
lean_inc_ref(v___y_2125_);
v___x_2136_ = lean_apply_8(v___f_2122_, v___x_2135_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, lean_box(0));
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; 
lean_dec_ref(v___f_2122_);
lean_inc(v___y_2130_);
lean_inc_ref(v___y_2129_);
lean_inc(v___y_2128_);
lean_inc_ref(v___y_2127_);
lean_inc(v___y_2126_);
lean_inc_ref(v___y_2125_);
v___x_2137_ = lean_apply_8(v_addInfo_2123_, v___x_2132_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, lean_box(0));
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec_ref(v___x_2137_);
v___x_2138_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1);
v___x_2139_ = l_Lean_MessageData_ofConstName(v_declName_2121_, v___x_2133_);
v___x_2140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2138_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2140_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
v___x_2143_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2142_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
return v___x_2143_;
}
else
{
lean_dec(v_declName_2121_);
return v___x_2137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed(lean_object* v_env_2144_, lean_object* v_declName_2145_, lean_object* v___f_2146_, lean_object* v_addInfo_2147_, lean_object* v_____r_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(v_env_2144_, v_declName_2145_, v___f_2146_, v_addInfo_2147_, v_____r_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(lean_object* v___f_2157_, lean_object* v_declName_2158_, uint8_t v___x_2159_, lean_object* v_env_2160_, lean_object* v_____do__lift_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
uint8_t v___y_2170_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
lean_inc(v_declName_2158_);
v___x_2179_ = l_Lean_privateToUserName(v_declName_2158_);
lean_inc_ref(v_env_2160_);
v___x_2180_ = lean_is_reserved_name(v_env_2160_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
lean_inc(v_declName_2158_);
v___x_2181_ = l_Lean_mkPrivateName(v_____do__lift_2161_, v_declName_2158_);
v___x_2182_ = lean_is_reserved_name(v_env_2160_, v___x_2181_);
v___y_2170_ = v___x_2182_;
goto v___jp_2169_;
}
else
{
lean_dec_ref(v_env_2160_);
v___y_2170_ = v___x_2180_;
goto v___jp_2169_;
}
v___jp_2169_:
{
if (v___y_2170_ == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec(v_declName_2158_);
v___x_2171_ = lean_box(0);
lean_inc(v___y_2167_);
lean_inc_ref(v___y_2166_);
lean_inc(v___y_2165_);
lean_inc_ref(v___y_2164_);
lean_inc(v___y_2163_);
lean_inc_ref(v___y_2162_);
v___x_2172_ = lean_apply_8(v___f_2157_, v___x_2171_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, lean_box(0));
return v___x_2172_;
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_dec_ref(v___f_2157_);
v___x_2173_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2174_ = l_Lean_MessageData_ofConstName(v_declName_2158_, v___x_2159_);
v___x_2175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2173_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
v___x_2176_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3);
v___x_2177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2175_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2177_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
return v___x_2178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed(lean_object* v___f_2183_, lean_object* v_declName_2184_, lean_object* v___x_2185_, lean_object* v_env_2186_, lean_object* v_____do__lift_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
uint8_t v___x_17521__boxed_2195_; lean_object* v_res_2196_; 
v___x_17521__boxed_2195_ = lean_unbox(v___x_2185_);
v_res_2196_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(v___f_2183_, v_declName_2184_, v___x_17521__boxed_2195_, v_env_2186_, v_____do__lift_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec_ref(v_____do__lift_2187_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(lean_object* v_t_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; lean_object* v_infoState_2201_; uint8_t v_enabled_2202_; 
v___x_2200_ = lean_st_ref_get(v___y_2198_);
v_infoState_2201_ = lean_ctor_get(v___x_2200_, 7);
lean_inc_ref(v_infoState_2201_);
lean_dec(v___x_2200_);
v_enabled_2202_ = lean_ctor_get_uint8(v_infoState_2201_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2201_);
if (v_enabled_2202_ == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec_ref(v_t_2197_);
v___x_2203_ = lean_box(0);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
else
{
lean_object* v___x_2205_; lean_object* v_infoState_2206_; lean_object* v_env_2207_; lean_object* v_nextMacroScope_2208_; lean_object* v_ngen_2209_; lean_object* v_auxDeclNGen_2210_; lean_object* v_traceState_2211_; lean_object* v_cache_2212_; lean_object* v_messages_2213_; lean_object* v_snapshotTasks_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2236_; 
v___x_2205_ = lean_st_ref_take(v___y_2198_);
v_infoState_2206_ = lean_ctor_get(v___x_2205_, 7);
v_env_2207_ = lean_ctor_get(v___x_2205_, 0);
v_nextMacroScope_2208_ = lean_ctor_get(v___x_2205_, 1);
v_ngen_2209_ = lean_ctor_get(v___x_2205_, 2);
v_auxDeclNGen_2210_ = lean_ctor_get(v___x_2205_, 3);
v_traceState_2211_ = lean_ctor_get(v___x_2205_, 4);
v_cache_2212_ = lean_ctor_get(v___x_2205_, 5);
v_messages_2213_ = lean_ctor_get(v___x_2205_, 6);
v_snapshotTasks_2214_ = lean_ctor_get(v___x_2205_, 8);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2216_ = v___x_2205_;
v_isShared_2217_ = v_isSharedCheck_2236_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_snapshotTasks_2214_);
lean_inc(v_infoState_2206_);
lean_inc(v_messages_2213_);
lean_inc(v_cache_2212_);
lean_inc(v_traceState_2211_);
lean_inc(v_auxDeclNGen_2210_);
lean_inc(v_ngen_2209_);
lean_inc(v_nextMacroScope_2208_);
lean_inc(v_env_2207_);
lean_dec(v___x_2205_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2236_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
uint8_t v_enabled_2218_; lean_object* v_assignment_2219_; lean_object* v_lazyAssignment_2220_; lean_object* v_trees_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2235_; 
v_enabled_2218_ = lean_ctor_get_uint8(v_infoState_2206_, sizeof(void*)*3);
v_assignment_2219_ = lean_ctor_get(v_infoState_2206_, 0);
v_lazyAssignment_2220_ = lean_ctor_get(v_infoState_2206_, 1);
v_trees_2221_ = lean_ctor_get(v_infoState_2206_, 2);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_infoState_2206_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2223_ = v_infoState_2206_;
v_isShared_2224_ = v_isSharedCheck_2235_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_trees_2221_);
lean_inc(v_lazyAssignment_2220_);
lean_inc(v_assignment_2219_);
lean_dec(v_infoState_2206_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2235_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2225_ = l_Lean_PersistentArray_push___redArg(v_trees_2221_, v_t_2197_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 2, v___x_2225_);
v___x_2227_ = v___x_2223_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_assignment_2219_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_lazyAssignment_2220_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v___x_2225_);
lean_ctor_set_uint8(v_reuseFailAlloc_2234_, sizeof(void*)*3, v_enabled_2218_);
v___x_2227_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2229_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 7, v___x_2227_);
v___x_2229_ = v___x_2216_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_env_2207_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v_nextMacroScope_2208_);
lean_ctor_set(v_reuseFailAlloc_2233_, 2, v_ngen_2209_);
lean_ctor_set(v_reuseFailAlloc_2233_, 3, v_auxDeclNGen_2210_);
lean_ctor_set(v_reuseFailAlloc_2233_, 4, v_traceState_2211_);
lean_ctor_set(v_reuseFailAlloc_2233_, 5, v_cache_2212_);
lean_ctor_set(v_reuseFailAlloc_2233_, 6, v_messages_2213_);
lean_ctor_set(v_reuseFailAlloc_2233_, 7, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2233_, 8, v_snapshotTasks_2214_);
v___x_2229_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = lean_st_ref_set(v___y_2198_, v___x_2229_);
v___x_2231_ = lean_box(0);
v___x_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
return v___x_2232_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg___boxed(lean_object* v_t_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_2237_, v___y_2238_);
lean_dec(v___y_2238_);
return v_res_2240_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = lean_unsigned_to_nat(32u);
v___x_2242_ = lean_mk_empty_array_with_capacity(v___x_2241_);
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
return v___x_2243_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1(void){
_start:
{
size_t v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2244_ = ((size_t)5ULL);
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = lean_unsigned_to_nat(32u);
v___x_2247_ = lean_mk_empty_array_with_capacity(v___x_2246_);
v___x_2248_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0);
v___x_2249_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v___x_2247_);
lean_ctor_set(v___x_2249_, 2, v___x_2245_);
lean_ctor_set(v___x_2249_, 3, v___x_2245_);
lean_ctor_set_usize(v___x_2249_, 4, v___x_2244_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(lean_object* v_t_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v___x_2258_; lean_object* v_infoState_2259_; uint8_t v_enabled_2260_; 
v___x_2258_ = lean_st_ref_get(v___y_2256_);
v_infoState_2259_ = lean_ctor_get(v___x_2258_, 7);
lean_inc_ref(v_infoState_2259_);
lean_dec(v___x_2258_);
v_enabled_2260_ = lean_ctor_get_uint8(v_infoState_2259_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2259_);
if (v_enabled_2260_ == 0)
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec_ref(v_t_2250_);
v___x_2261_ = lean_box(0);
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1);
v___x_2264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2264_, 0, v_t_2250_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v___x_2264_, v___y_2256_);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___boxed(lean_object* v_t_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v_t_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(lean_object* v_a_2275_, lean_object* v_a_2276_){
_start:
{
if (lean_obj_tag(v_a_2275_) == 0)
{
lean_object* v___x_2277_; 
v___x_2277_ = l_List_reverse___redArg(v_a_2276_);
return v___x_2277_;
}
else
{
lean_object* v_head_2278_; lean_object* v_tail_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2288_; 
v_head_2278_ = lean_ctor_get(v_a_2275_, 0);
v_tail_2279_ = lean_ctor_get(v_a_2275_, 1);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_a_2275_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2281_ = v_a_2275_;
v_isShared_2282_ = v_isSharedCheck_2288_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_tail_2279_);
lean_inc(v_head_2278_);
lean_dec(v_a_2275_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2288_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; lean_object* v___x_2285_; 
v___x_2283_ = l_Lean_mkLevelParam(v_head_2278_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 1, v_a_2276_);
lean_ctor_set(v___x_2281_, 0, v___x_2283_);
v___x_2285_ = v___x_2281_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_a_2276_);
v___x_2285_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
v_a_2275_ = v_tail_2279_;
v_a_2276_ = v___x_2285_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0(void){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2289_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0);
v___x_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
return v___x_2291_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
v___x_2293_ = lean_unsigned_to_nat(0u);
v___x_2294_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
lean_ctor_set(v___x_2294_, 2, v___x_2293_);
lean_ctor_set(v___x_2294_, 3, v___x_2293_);
lean_ctor_set(v___x_2294_, 4, v___x_2292_);
lean_ctor_set(v___x_2294_, 5, v___x_2292_);
lean_ctor_set(v___x_2294_, 6, v___x_2292_);
lean_ctor_set(v___x_2294_, 7, v___x_2292_);
lean_ctor_set(v___x_2294_, 8, v___x_2292_);
lean_ctor_set(v___x_2294_, 9, v___x_2292_);
return v___x_2294_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2295_ = lean_box(1);
v___x_2296_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3);
v___x_2297_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
v___x_2298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v___x_2296_);
lean_ctor_set(v___x_2298_, 2, v___x_2295_);
return v___x_2298_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4));
v___x_2301_ = l_Lean_stringToMessageData(v___x_2300_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6));
v___x_2304_ = l_Lean_stringToMessageData(v___x_2303_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8));
v___x_2307_ = l_Lean_stringToMessageData(v___x_2306_);
return v___x_2307_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10));
v___x_2310_ = l_Lean_stringToMessageData(v___x_2309_);
return v___x_2310_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12));
v___x_2313_ = l_Lean_stringToMessageData(v___x_2312_);
return v___x_2313_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14));
v___x_2316_ = l_Lean_stringToMessageData(v___x_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16));
v___x_2319_ = l_Lean_stringToMessageData(v___x_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(lean_object* v_msg_2320_, lean_object* v_declHint_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___x_2324_; lean_object* v_env_2325_; uint8_t v___x_2326_; 
v___x_2324_ = lean_st_ref_get(v___y_2322_);
v_env_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc_ref(v_env_2325_);
lean_dec(v___x_2324_);
v___x_2326_ = l_Lean_Name_isAnonymous(v_declHint_2321_);
if (v___x_2326_ == 0)
{
uint8_t v_isExporting_2327_; 
v_isExporting_2327_ = lean_ctor_get_uint8(v_env_2325_, sizeof(void*)*8);
if (v_isExporting_2327_ == 0)
{
lean_object* v___x_2328_; 
lean_dec_ref(v_env_2325_);
lean_dec(v_declHint_2321_);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_msg_2320_);
return v___x_2328_;
}
else
{
lean_object* v___x_2329_; uint8_t v___x_2330_; 
lean_inc_ref(v_env_2325_);
v___x_2329_ = l_Lean_Environment_setExporting(v_env_2325_, v___x_2326_);
lean_inc(v_declHint_2321_);
lean_inc_ref(v___x_2329_);
v___x_2330_ = l_Lean_Environment_contains(v___x_2329_, v_declHint_2321_, v_isExporting_2327_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; 
lean_dec_ref(v___x_2329_);
lean_dec_ref(v_env_2325_);
lean_dec(v_declHint_2321_);
v___x_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2331_, 0, v_msg_2320_);
return v___x_2331_;
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v_c_2337_; lean_object* v___x_2338_; 
v___x_2332_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2);
v___x_2333_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3);
v___x_2334_ = l_Lean_Options_empty;
v___x_2335_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2329_);
lean_ctor_set(v___x_2335_, 1, v___x_2332_);
lean_ctor_set(v___x_2335_, 2, v___x_2333_);
lean_ctor_set(v___x_2335_, 3, v___x_2334_);
lean_inc(v_declHint_2321_);
v___x_2336_ = l_Lean_MessageData_ofConstName(v_declHint_2321_, v___x_2326_);
v_c_2337_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2337_, 0, v___x_2335_);
lean_ctor_set(v_c_2337_, 1, v___x_2336_);
v___x_2338_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2325_, v_declHint_2321_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_dec_ref(v_env_2325_);
lean_dec(v_declHint_2321_);
v___x_2339_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5);
v___x_2340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
lean_ctor_set(v___x_2340_, 1, v_c_2337_);
v___x_2341_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7);
v___x_2342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = l_Lean_MessageData_note(v___x_2342_);
v___x_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2344_, 0, v_msg_2320_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
return v___x_2345_;
}
else
{
lean_object* v_val_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2381_; 
v_val_2346_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2348_ = v___x_2338_;
v_isShared_2349_ = v_isSharedCheck_2381_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_val_2346_);
lean_dec(v___x_2338_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2381_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v_mod_2353_; uint8_t v___x_2354_; 
v___x_2350_ = lean_box(0);
v___x_2351_ = l_Lean_Environment_header(v_env_2325_);
lean_dec_ref(v_env_2325_);
v___x_2352_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2351_);
v_mod_2353_ = lean_array_get(v___x_2350_, v___x_2352_, v_val_2346_);
lean_dec(v_val_2346_);
lean_dec_ref(v___x_2352_);
v___x_2354_ = l_Lean_isPrivateName(v_declHint_2321_);
lean_dec(v_declHint_2321_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2355_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9);
v___x_2356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
lean_ctor_set(v___x_2356_, 1, v_c_2337_);
v___x_2357_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11);
v___x_2358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = l_Lean_MessageData_ofName(v_mod_2353_);
v___x_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2358_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13);
v___x_2362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2360_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
v___x_2363_ = l_Lean_MessageData_note(v___x_2362_);
v___x_2364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2364_, 0, v_msg_2320_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set_tag(v___x_2348_, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2364_);
v___x_2366_ = v___x_2348_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
else
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2379_; 
v___x_2368_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
lean_ctor_set(v___x_2369_, 1, v_c_2337_);
v___x_2370_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15);
v___x_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = l_Lean_MessageData_ofName(v_mod_2353_);
v___x_2373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17);
v___x_2375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2373_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = l_Lean_MessageData_note(v___x_2375_);
v___x_2377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2377_, 0, v_msg_2320_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set_tag(v___x_2348_, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2377_);
v___x_2379_ = v___x_2348_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2382_; 
lean_dec_ref(v_env_2325_);
lean_dec(v_declHint_2321_);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v_msg_2320_);
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___boxed(lean_object* v_msg_2383_, lean_object* v_declHint_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2383_, v_declHint_2384_, v___y_2385_);
lean_dec(v___y_2385_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(lean_object* v_msg_2388_, lean_object* v_declHint_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___x_2397_; lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2407_; 
v___x_2397_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2388_, v_declHint_2389_, v___y_2395_);
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2407_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2407_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2402_ = l_Lean_unknownIdentifierMessageTag;
v___x_2403_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
lean_ctor_set(v___x_2403_, 1, v_a_2398_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v___x_2403_);
v___x_2405_ = v___x_2400_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23___boxed(lean_object* v_msg_2408_, lean_object* v_declHint_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2408_, v_declHint_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(lean_object* v_ref_2418_, lean_object* v_msg_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_fileName_2427_; lean_object* v_fileMap_2428_; lean_object* v_options_2429_; lean_object* v_currRecDepth_2430_; lean_object* v_maxRecDepth_2431_; lean_object* v_ref_2432_; lean_object* v_currNamespace_2433_; lean_object* v_openDecls_2434_; lean_object* v_initHeartbeats_2435_; lean_object* v_maxHeartbeats_2436_; lean_object* v_quotContext_2437_; lean_object* v_currMacroScope_2438_; uint8_t v_diag_2439_; lean_object* v_cancelTk_x3f_2440_; uint8_t v_suppressElabErrors_2441_; lean_object* v_inheritedTraceOptions_2442_; lean_object* v_ref_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_fileName_2427_ = lean_ctor_get(v___y_2424_, 0);
v_fileMap_2428_ = lean_ctor_get(v___y_2424_, 1);
v_options_2429_ = lean_ctor_get(v___y_2424_, 2);
v_currRecDepth_2430_ = lean_ctor_get(v___y_2424_, 3);
v_maxRecDepth_2431_ = lean_ctor_get(v___y_2424_, 4);
v_ref_2432_ = lean_ctor_get(v___y_2424_, 5);
v_currNamespace_2433_ = lean_ctor_get(v___y_2424_, 6);
v_openDecls_2434_ = lean_ctor_get(v___y_2424_, 7);
v_initHeartbeats_2435_ = lean_ctor_get(v___y_2424_, 8);
v_maxHeartbeats_2436_ = lean_ctor_get(v___y_2424_, 9);
v_quotContext_2437_ = lean_ctor_get(v___y_2424_, 10);
v_currMacroScope_2438_ = lean_ctor_get(v___y_2424_, 11);
v_diag_2439_ = lean_ctor_get_uint8(v___y_2424_, sizeof(void*)*14);
v_cancelTk_x3f_2440_ = lean_ctor_get(v___y_2424_, 12);
v_suppressElabErrors_2441_ = lean_ctor_get_uint8(v___y_2424_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2442_ = lean_ctor_get(v___y_2424_, 13);
v_ref_2443_ = l_Lean_replaceRef(v_ref_2418_, v_ref_2432_);
lean_inc_ref(v_inheritedTraceOptions_2442_);
lean_inc(v_cancelTk_x3f_2440_);
lean_inc(v_currMacroScope_2438_);
lean_inc(v_quotContext_2437_);
lean_inc(v_maxHeartbeats_2436_);
lean_inc(v_initHeartbeats_2435_);
lean_inc(v_openDecls_2434_);
lean_inc(v_currNamespace_2433_);
lean_inc(v_maxRecDepth_2431_);
lean_inc(v_currRecDepth_2430_);
lean_inc_ref(v_options_2429_);
lean_inc_ref(v_fileMap_2428_);
lean_inc_ref(v_fileName_2427_);
v___x_2444_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2444_, 0, v_fileName_2427_);
lean_ctor_set(v___x_2444_, 1, v_fileMap_2428_);
lean_ctor_set(v___x_2444_, 2, v_options_2429_);
lean_ctor_set(v___x_2444_, 3, v_currRecDepth_2430_);
lean_ctor_set(v___x_2444_, 4, v_maxRecDepth_2431_);
lean_ctor_set(v___x_2444_, 5, v_ref_2443_);
lean_ctor_set(v___x_2444_, 6, v_currNamespace_2433_);
lean_ctor_set(v___x_2444_, 7, v_openDecls_2434_);
lean_ctor_set(v___x_2444_, 8, v_initHeartbeats_2435_);
lean_ctor_set(v___x_2444_, 9, v_maxHeartbeats_2436_);
lean_ctor_set(v___x_2444_, 10, v_quotContext_2437_);
lean_ctor_set(v___x_2444_, 11, v_currMacroScope_2438_);
lean_ctor_set(v___x_2444_, 12, v_cancelTk_x3f_2440_);
lean_ctor_set(v___x_2444_, 13, v_inheritedTraceOptions_2442_);
lean_ctor_set_uint8(v___x_2444_, sizeof(void*)*14, v_diag_2439_);
lean_ctor_set_uint8(v___x_2444_, sizeof(void*)*14 + 1, v_suppressElabErrors_2441_);
v___x_2445_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___x_2444_, v___y_2425_);
lean_dec_ref(v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg___boxed(lean_object* v_ref_2446_, lean_object* v_msg_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2446_, v_msg_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v_ref_2446_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(lean_object* v_ref_2456_, lean_object* v_msg_2457_, lean_object* v_declHint_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2466_; lean_object* v_a_2467_; lean_object* v___x_2468_; 
v___x_2466_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2457_, v_declHint_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref(v___x_2466_);
v___x_2468_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2456_, v_a_2467_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg___boxed(lean_object* v_ref_2469_, lean_object* v_msg_2470_, lean_object* v_declHint_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2469_, v_msg_2470_, v_declHint_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v_ref_2469_);
return v_res_2479_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0));
v___x_2482_ = l_Lean_stringToMessageData(v___x_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(lean_object* v_ref_2483_, lean_object* v_constName_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v___x_2492_; uint8_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2492_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1);
v___x_2493_ = 0;
lean_inc(v_constName_2484_);
v___x_2494_ = l_Lean_MessageData_ofConstName(v_constName_2484_, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2492_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2495_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2483_, v___x_2497_, v_constName_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___boxed(lean_object* v_ref_2499_, lean_object* v_constName_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2499_, v_constName_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v_ref_2499_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(lean_object* v_constName_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_ref_2517_; lean_object* v___x_2518_; 
v_ref_2517_ = lean_ctor_get(v___y_2514_, 5);
v___x_2518_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2517_, v_constName_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_constName_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(lean_object* v_constName_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; lean_object* v_env_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; 
v___x_2536_ = lean_st_ref_get(v___y_2534_);
v_env_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc_ref(v_env_2537_);
lean_dec(v___x_2536_);
v___x_2538_ = 0;
lean_inc(v_constName_2528_);
v___x_2539_ = l_Lean_Environment_findConstVal_x3f(v_env_2537_, v_constName_2528_, v___x_2538_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v___x_2540_; 
v___x_2540_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
return v___x_2540_;
}
else
{
lean_object* v_val_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_constName_2528_);
v_val_2541_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2539_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_val_2541_);
lean_dec(v___x_2539_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
lean_ctor_set_tag(v___x_2543_, 0);
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_val_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14___boxed(lean_object* v_constName_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(lean_object* v_constName_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; 
lean_inc(v_constName_2558_);
v___x_2566_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2578_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2578_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2578_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v_levelParams_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
v_levelParams_2571_ = lean_ctor_get(v_a_2567_, 1);
lean_inc(v_levelParams_2571_);
lean_dec(v_a_2567_);
v___x_2572_ = lean_box(0);
v___x_2573_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(v_levelParams_2571_, v___x_2572_);
v___x_2574_ = l_Lean_mkConst(v_constName_2558_, v___x_2573_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2574_);
v___x_2576_ = v___x_2569_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec(v_constName_2558_);
v_a_2579_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2566_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2566_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_constName_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_constName_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(uint8_t v___x_2596_, lean_object* v_declName_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_ref_2605_; lean_object* v___x_2606_; 
v_ref_2605_ = lean_ctor_get(v___y_2602_, 5);
v___x_2606_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_declName_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref(v___x_2606_);
v___x_2608_ = lean_box(0);
lean_inc(v_ref_2605_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
lean_ctor_set(v___x_2609_, 1, v_ref_2605_);
v___x_2610_ = lean_unsigned_to_nat(32u);
v___x_2611_ = lean_mk_empty_array_with_capacity(v___x_2610_);
lean_dec_ref(v___x_2611_);
v___x_2612_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4);
v___x_2613_ = lean_box(0);
v___x_2614_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2614_, 0, v___x_2609_);
lean_ctor_set(v___x_2614_, 1, v___x_2612_);
lean_ctor_set(v___x_2614_, 2, v___x_2613_);
lean_ctor_set(v___x_2614_, 3, v_a_2607_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*4, v___x_2596_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*4 + 1, v___x_2596_);
v___x_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
v___x_2616_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v___x_2615_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
return v___x_2616_;
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
v_a_2617_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2606_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2606_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v___x_2625_, lean_object* v_declName_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
uint8_t v___x_18250__boxed_2634_; lean_object* v_res_2635_; 
v___x_18250__boxed_2634_ = lean_unbox(v___x_2625_);
v_res_2635_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(v___x_18250__boxed_2634_, v_declName_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(lean_object* v___f_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v___x_2644_; lean_object* v_env_2645_; lean_object* v___x_2646_; 
v___x_2644_ = lean_st_ref_get(v___y_2642_);
v_env_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc_ref(v_env_2645_);
lean_dec(v___x_2644_);
v___x_2646_ = lean_apply_8(v___f_2636_, v_env_2645_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, lean_box(0));
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed(lean_object* v___f_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(v___f_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
return v_res_2655_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2656_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
return v___x_2658_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
v___x_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
return v___x_2660_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
v___x_2662_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
lean_ctor_set(v___x_2662_, 2, v___x_2661_);
lean_ctor_set(v___x_2662_, 3, v___x_2661_);
lean_ctor_set(v___x_2662_, 4, v___x_2661_);
lean_ctor_set(v___x_2662_, 5, v___x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(lean_object* v_env_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; lean_object* v_nextMacroScope_2668_; lean_object* v_ngen_2669_; lean_object* v_auxDeclNGen_2670_; lean_object* v_traceState_2671_; lean_object* v_messages_2672_; lean_object* v_infoState_2673_; lean_object* v_snapshotTasks_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2700_; 
v___x_2667_ = lean_st_ref_take(v___y_2665_);
v_nextMacroScope_2668_ = lean_ctor_get(v___x_2667_, 1);
v_ngen_2669_ = lean_ctor_get(v___x_2667_, 2);
v_auxDeclNGen_2670_ = lean_ctor_get(v___x_2667_, 3);
v_traceState_2671_ = lean_ctor_get(v___x_2667_, 4);
v_messages_2672_ = lean_ctor_get(v___x_2667_, 6);
v_infoState_2673_ = lean_ctor_get(v___x_2667_, 7);
v_snapshotTasks_2674_ = lean_ctor_get(v___x_2667_, 8);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2700_ == 0)
{
lean_object* v_unused_2701_; lean_object* v_unused_2702_; 
v_unused_2701_ = lean_ctor_get(v___x_2667_, 5);
lean_dec(v_unused_2701_);
v_unused_2702_ = lean_ctor_get(v___x_2667_, 0);
lean_dec(v_unused_2702_);
v___x_2676_ = v___x_2667_;
v_isShared_2677_ = v_isSharedCheck_2700_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_snapshotTasks_2674_);
lean_inc(v_infoState_2673_);
lean_inc(v_messages_2672_);
lean_inc(v_traceState_2671_);
lean_inc(v_auxDeclNGen_2670_);
lean_inc(v_ngen_2669_);
lean_inc(v_nextMacroScope_2668_);
lean_dec(v___x_2667_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2700_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2678_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 5, v___x_2678_);
lean_ctor_set(v___x_2676_, 0, v_env_2663_);
v___x_2680_ = v___x_2676_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_env_2663_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_nextMacroScope_2668_);
lean_ctor_set(v_reuseFailAlloc_2699_, 2, v_ngen_2669_);
lean_ctor_set(v_reuseFailAlloc_2699_, 3, v_auxDeclNGen_2670_);
lean_ctor_set(v_reuseFailAlloc_2699_, 4, v_traceState_2671_);
lean_ctor_set(v_reuseFailAlloc_2699_, 5, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2699_, 6, v_messages_2672_);
lean_ctor_set(v_reuseFailAlloc_2699_, 7, v_infoState_2673_);
lean_ctor_set(v_reuseFailAlloc_2699_, 8, v_snapshotTasks_2674_);
v___x_2680_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v_mctx_2683_; lean_object* v_zetaDeltaFVarIds_2684_; lean_object* v_postponed_2685_; lean_object* v_diag_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2697_; 
v___x_2681_ = lean_st_ref_set(v___y_2665_, v___x_2680_);
v___x_2682_ = lean_st_ref_take(v___y_2664_);
v_mctx_2683_ = lean_ctor_get(v___x_2682_, 0);
v_zetaDeltaFVarIds_2684_ = lean_ctor_get(v___x_2682_, 2);
v_postponed_2685_ = lean_ctor_get(v___x_2682_, 3);
v_diag_2686_ = lean_ctor_get(v___x_2682_, 4);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2697_ == 0)
{
lean_object* v_unused_2698_; 
v_unused_2698_ = lean_ctor_get(v___x_2682_, 1);
lean_dec(v_unused_2698_);
v___x_2688_ = v___x_2682_;
v_isShared_2689_ = v_isSharedCheck_2697_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_diag_2686_);
lean_inc(v_postponed_2685_);
lean_inc(v_zetaDeltaFVarIds_2684_);
lean_inc(v_mctx_2683_);
lean_dec(v___x_2682_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2697_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2690_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 1, v___x_2690_);
v___x_2692_ = v___x_2688_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_mctx_2683_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2696_, 2, v_zetaDeltaFVarIds_2684_);
lean_ctor_set(v_reuseFailAlloc_2696_, 3, v_postponed_2685_);
lean_ctor_set(v_reuseFailAlloc_2696_, 4, v_diag_2686_);
v___x_2692_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2693_ = lean_st_ref_set(v___y_2664_, v___x_2692_);
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
return v___x_2695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___boxed(lean_object* v_env_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec(v___y_2704_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(lean_object* v_env_2708_, lean_object* v_x_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2717_; lean_object* v_env_2718_; lean_object* v_a_2720_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2717_ = lean_st_ref_get(v___y_2715_);
v_env_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc_ref(v_env_2718_);
lean_dec(v___x_2717_);
v___x_2730_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2708_, v___y_2713_, v___y_2715_);
lean_dec_ref(v___x_2730_);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
v___x_2731_ = lean_apply_7(v_x_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, lean_box(0));
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref(v___x_2731_);
v___x_2733_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2718_, v___y_2713_, v___y_2715_);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2740_ == 0)
{
lean_object* v_unused_2741_; 
v_unused_2741_ = lean_ctor_get(v___x_2733_, 0);
lean_dec(v_unused_2741_);
v___x_2735_ = v___x_2733_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_dec(v___x_2733_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v_a_2732_);
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2732_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
else
{
lean_object* v_a_2742_; 
v_a_2742_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2742_);
lean_dec_ref(v___x_2731_);
v_a_2720_ = v_a_2742_;
goto v___jp_2719_;
}
v___jp_2719_:
{
lean_object* v___x_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
v___x_2721_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2718_, v___y_2713_, v___y_2715_);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2728_ == 0)
{
lean_object* v_unused_2729_; 
v_unused_2729_ = lean_ctor_get(v___x_2721_, 0);
lean_dec(v_unused_2729_);
v___x_2723_ = v___x_2721_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_dec(v___x_2721_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
lean_ctor_set_tag(v___x_2723_, 1);
lean_ctor_set(v___x_2723_, 0, v_a_2720_);
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2720_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_env_2743_, lean_object* v_x_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2743_, v_x_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(lean_object* v_declName_2753_, lean_object* v_env_2754_, lean_object* v_addInfo_2755_, lean_object* v_____r_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_private_to_user_name(v_declName_2753_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_dec_ref(v_addInfo_2755_);
lean_dec_ref(v_env_2754_);
v___x_2765_ = lean_box(0);
v___x_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
return v___x_2766_;
}
else
{
lean_object* v_val_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2784_; 
v_val_2767_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2769_ = v___x_2764_;
v_isShared_2770_ = v_isSharedCheck_2784_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_val_2767_);
lean_dec(v___x_2764_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2784_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
uint8_t v___x_2771_; uint8_t v___x_2772_; 
v___x_2771_ = 1;
lean_inc(v_val_2767_);
v___x_2772_ = l_Lean_Environment_contains(v_env_2754_, v_val_2767_, v___x_2771_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2775_; 
lean_dec(v_val_2767_);
lean_dec_ref(v_addInfo_2755_);
v___x_2773_ = lean_box(0);
if (v_isShared_2770_ == 0)
{
lean_ctor_set_tag(v___x_2769_, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2773_);
v___x_2775_ = v___x_2769_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
else
{
lean_object* v___x_2777_; 
lean_del_object(v___x_2769_);
lean_inc(v___y_2762_);
lean_inc_ref(v___y_2761_);
lean_inc(v___y_2760_);
lean_inc_ref(v___y_2759_);
lean_inc(v___y_2758_);
lean_inc_ref(v___y_2757_);
lean_inc(v_val_2767_);
v___x_2777_ = lean_apply_8(v_addInfo_2755_, v_val_2767_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, lean_box(0));
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
lean_dec_ref(v___x_2777_);
v___x_2778_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
v___x_2779_ = l_Lean_MessageData_ofConstName(v_val_2767_, v___x_2771_);
v___x_2780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2778_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
v___x_2781_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2780_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2782_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
return v___x_2783_;
}
else
{
lean_dec(v_val_2767_);
return v___x_2777_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed(lean_object* v_declName_2785_, lean_object* v_env_2786_, lean_object* v_addInfo_2787_, lean_object* v_____r_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(v_declName_2785_, v_env_2786_, v_addInfo_2787_, v_____r_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(lean_object* v_addInfo_2797_, lean_object* v_declName_2798_, uint8_t v___x_2799_, lean_object* v___f_2800_, uint8_t v___x_2801_, lean_object* v_env_2802_, lean_object* v___f_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v___x_2811_; 
lean_inc(v___y_2809_);
lean_inc_ref(v___y_2808_);
lean_inc(v___y_2807_);
lean_inc_ref(v___y_2806_);
lean_inc(v___y_2805_);
lean_inc_ref(v___y_2804_);
lean_inc(v_declName_2798_);
v___x_2811_ = lean_apply_8(v_addInfo_2797_, v_declName_2798_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, lean_box(0));
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v___x_2812_; 
lean_dec_ref(v___x_2811_);
lean_inc(v_declName_2798_);
v___x_2812_ = lean_private_to_user_name(v_declName_2798_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2813_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2814_ = l_Lean_MessageData_ofConstName(v_declName_2798_, v___x_2799_);
v___x_2815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2815_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
v___x_2818_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2817_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
return v___x_2818_;
}
else
{
lean_object* v_val_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec(v_declName_2798_);
v_val_2819_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_val_2819_);
lean_dec_ref(v___x_2812_);
v___x_2820_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1);
v___x_2821_ = l_Lean_MessageData_ofConstName(v_val_2819_, v___x_2799_);
v___x_2822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2820_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2822_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2824_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
return v___x_2825_;
}
}
else
{
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v_declName_2798_);
return v___x_2811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed(lean_object* v_addInfo_2826_, lean_object* v_declName_2827_, lean_object* v___x_2828_, lean_object* v___f_2829_, lean_object* v___x_2830_, lean_object* v_env_2831_, lean_object* v___f_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
uint8_t v___x_18604__boxed_2840_; uint8_t v___x_18606__boxed_2841_; lean_object* v_res_2842_; 
v___x_18604__boxed_2840_ = lean_unbox(v___x_2828_);
v___x_18606__boxed_2841_ = lean_unbox(v___x_2830_);
v_res_2842_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(v_addInfo_2826_, v_declName_2827_, v___x_18604__boxed_2840_, v___f_2829_, v___x_18606__boxed_2841_, v_env_2831_, v___f_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
lean_dec_ref(v___f_2832_);
lean_dec_ref(v_env_2831_);
lean_dec_ref(v___f_2829_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(lean_object* v_declName_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v___x_2854_; lean_object* v_env_2855_; uint8_t v___x_2856_; lean_object* v_addInfo_2857_; lean_object* v_env_2858_; lean_object* v___f_2859_; lean_object* v___f_2860_; lean_object* v___x_2861_; lean_object* v___f_2862_; uint8_t v___x_2863_; uint8_t v___x_2864_; 
v___x_2854_ = lean_st_ref_get(v___y_2852_);
v_env_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc_ref(v_env_2855_);
lean_dec(v___x_2854_);
v___x_2856_ = 0;
v_addInfo_2857_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0));
v_env_2858_ = l_Lean_Environment_setExporting(v_env_2855_, v___x_2856_);
lean_inc_ref_n(v_env_2858_, 4);
lean_inc_n(v_declName_2846_, 4);
v___f_2859_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed), 11, 3);
lean_closure_set(v___f_2859_, 0, v_declName_2846_);
lean_closure_set(v___f_2859_, 1, v_env_2858_);
lean_closure_set(v___f_2859_, 2, v_addInfo_2857_);
v___f_2860_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2860_, 0, v_env_2858_);
lean_closure_set(v___f_2860_, 1, v_declName_2846_);
lean_closure_set(v___f_2860_, 2, v___f_2859_);
lean_closure_set(v___f_2860_, 3, v_addInfo_2857_);
v___x_2861_ = lean_box(v___x_2856_);
lean_inc_ref(v___f_2860_);
v___f_2862_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed), 12, 4);
lean_closure_set(v___f_2862_, 0, v___f_2860_);
lean_closure_set(v___f_2862_, 1, v_declName_2846_);
lean_closure_set(v___f_2862_, 2, v___x_2861_);
lean_closure_set(v___f_2862_, 3, v_env_2858_);
v___x_2863_ = 1;
v___x_2864_ = l_Lean_Environment_contains(v_env_2858_, v_declName_2846_, v___x_2863_);
if (v___x_2864_ == 0)
{
lean_object* v___f_2865_; lean_object* v___x_2866_; 
lean_dec_ref(v___f_2860_);
lean_dec(v_declName_2846_);
v___f_2865_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed), 8, 1);
lean_closure_set(v___f_2865_, 0, v___f_2862_);
v___x_2866_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2858_, v___f_2865_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
return v___x_2866_;
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___f_2869_; lean_object* v___x_2870_; 
v___x_2867_ = lean_box(v___x_2863_);
v___x_2868_ = lean_box(v___x_2856_);
lean_inc_ref(v_env_2858_);
v___f_2869_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed), 14, 7);
lean_closure_set(v___f_2869_, 0, v_addInfo_2857_);
lean_closure_set(v___f_2869_, 1, v_declName_2846_);
lean_closure_set(v___f_2869_, 2, v___x_2867_);
lean_closure_set(v___f_2869_, 3, v___f_2860_);
lean_closure_set(v___f_2869_, 4, v___x_2868_);
lean_closure_set(v___f_2869_, 5, v_env_2858_);
lean_closure_set(v___f_2869_, 6, v___f_2862_);
v___x_2870_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2858_, v___f_2869_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
return v___x_2870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___boxed(lean_object* v_declName_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(lean_object* v_modifiers_2880_, lean_object* v_declName_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; lean_object* v_env_2890_; uint8_t v_visibility_2891_; uint8_t v_isProtected_2892_; lean_object* v_declName_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; uint8_t v___x_2956_; 
v___x_2889_ = lean_st_ref_get(v___y_2887_);
v_env_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc_ref(v_env_2890_);
lean_dec(v___x_2889_);
v_visibility_2891_ = lean_ctor_get_uint8(v_modifiers_2880_, sizeof(void*)*3);
v_isProtected_2892_ = lean_ctor_get_uint8(v_modifiers_2880_, sizeof(void*)*3 + 1);
v___x_2956_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_2890_, v_visibility_2891_);
lean_dec_ref(v_env_2890_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; lean_object* v_env_2958_; lean_object* v_declName_2959_; 
v___x_2957_ = lean_st_ref_get(v___y_2887_);
v_env_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc_ref(v_env_2958_);
lean_dec(v___x_2957_);
v_declName_2959_ = l_Lean_mkPrivateName(v_env_2958_, v_declName_2881_);
lean_dec_ref(v_env_2958_);
v_declName_2894_ = v_declName_2959_;
v___y_2895_ = v___y_2882_;
v___y_2896_ = v___y_2883_;
v___y_2897_ = v___y_2884_;
v___y_2898_ = v___y_2885_;
v___y_2899_ = v___y_2886_;
v___y_2900_ = v___y_2887_;
goto v___jp_2893_;
}
else
{
v_declName_2894_ = v_declName_2881_;
v___y_2895_ = v___y_2882_;
v___y_2896_ = v___y_2883_;
v___y_2897_ = v___y_2884_;
v___y_2898_ = v___y_2885_;
v___y_2899_ = v___y_2886_;
v___y_2900_ = v___y_2887_;
goto v___jp_2893_;
}
v___jp_2893_:
{
lean_object* v___x_2901_; 
lean_inc(v_declName_2894_);
v___x_2901_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2946_; 
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2946_ == 0)
{
lean_object* v_unused_2947_; 
v_unused_2947_ = lean_ctor_get(v___x_2901_, 0);
lean_dec(v_unused_2947_);
v___x_2903_ = v___x_2901_;
v_isShared_2904_ = v_isSharedCheck_2946_;
goto v_resetjp_2902_;
}
else
{
lean_dec(v___x_2901_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2946_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
if (v_isProtected_2892_ == 0)
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v_declName_2894_);
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_declName_2894_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
else
{
lean_object* v___x_2908_; lean_object* v_env_2909_; lean_object* v_nextMacroScope_2910_; lean_object* v_ngen_2911_; lean_object* v_auxDeclNGen_2912_; lean_object* v_traceState_2913_; lean_object* v_messages_2914_; lean_object* v_infoState_2915_; lean_object* v_snapshotTasks_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2944_; 
v___x_2908_ = lean_st_ref_take(v___y_2900_);
v_env_2909_ = lean_ctor_get(v___x_2908_, 0);
v_nextMacroScope_2910_ = lean_ctor_get(v___x_2908_, 1);
v_ngen_2911_ = lean_ctor_get(v___x_2908_, 2);
v_auxDeclNGen_2912_ = lean_ctor_get(v___x_2908_, 3);
v_traceState_2913_ = lean_ctor_get(v___x_2908_, 4);
v_messages_2914_ = lean_ctor_get(v___x_2908_, 6);
v_infoState_2915_ = lean_ctor_get(v___x_2908_, 7);
v_snapshotTasks_2916_ = lean_ctor_get(v___x_2908_, 8);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2944_ == 0)
{
lean_object* v_unused_2945_; 
v_unused_2945_ = lean_ctor_get(v___x_2908_, 5);
lean_dec(v_unused_2945_);
v___x_2918_ = v___x_2908_;
v_isShared_2919_ = v_isSharedCheck_2944_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_snapshotTasks_2916_);
lean_inc(v_infoState_2915_);
lean_inc(v_messages_2914_);
lean_inc(v_traceState_2913_);
lean_inc(v_auxDeclNGen_2912_);
lean_inc(v_ngen_2911_);
lean_inc(v_nextMacroScope_2910_);
lean_inc(v_env_2909_);
lean_dec(v___x_2908_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2944_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2923_; 
lean_inc(v_declName_2894_);
v___x_2920_ = l_Lean_addProtected(v_env_2909_, v_declName_2894_);
v___x_2921_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 5, v___x_2921_);
lean_ctor_set(v___x_2918_, 0, v___x_2920_);
v___x_2923_ = v___x_2918_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_nextMacroScope_2910_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v_ngen_2911_);
lean_ctor_set(v_reuseFailAlloc_2943_, 3, v_auxDeclNGen_2912_);
lean_ctor_set(v_reuseFailAlloc_2943_, 4, v_traceState_2913_);
lean_ctor_set(v_reuseFailAlloc_2943_, 5, v___x_2921_);
lean_ctor_set(v_reuseFailAlloc_2943_, 6, v_messages_2914_);
lean_ctor_set(v_reuseFailAlloc_2943_, 7, v_infoState_2915_);
lean_ctor_set(v_reuseFailAlloc_2943_, 8, v_snapshotTasks_2916_);
v___x_2923_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v_mctx_2926_; lean_object* v_zetaDeltaFVarIds_2927_; lean_object* v_postponed_2928_; lean_object* v_diag_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2941_; 
v___x_2924_ = lean_st_ref_set(v___y_2900_, v___x_2923_);
v___x_2925_ = lean_st_ref_take(v___y_2898_);
v_mctx_2926_ = lean_ctor_get(v___x_2925_, 0);
v_zetaDeltaFVarIds_2927_ = lean_ctor_get(v___x_2925_, 2);
v_postponed_2928_ = lean_ctor_get(v___x_2925_, 3);
v_diag_2929_ = lean_ctor_get(v___x_2925_, 4);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2941_ == 0)
{
lean_object* v_unused_2942_; 
v_unused_2942_ = lean_ctor_get(v___x_2925_, 1);
lean_dec(v_unused_2942_);
v___x_2931_ = v___x_2925_;
v_isShared_2932_ = v_isSharedCheck_2941_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_diag_2929_);
lean_inc(v_postponed_2928_);
lean_inc(v_zetaDeltaFVarIds_2927_);
lean_inc(v_mctx_2926_);
lean_dec(v___x_2925_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2941_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2933_; lean_object* v___x_2935_; 
v___x_2933_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 1, v___x_2933_);
v___x_2935_ = v___x_2931_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_mctx_2926_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v___x_2933_);
lean_ctor_set(v_reuseFailAlloc_2940_, 2, v_zetaDeltaFVarIds_2927_);
lean_ctor_set(v_reuseFailAlloc_2940_, 3, v_postponed_2928_);
lean_ctor_set(v_reuseFailAlloc_2940_, 4, v_diag_2929_);
v___x_2935_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
lean_object* v___x_2936_; lean_object* v___x_2938_; 
v___x_2936_ = lean_st_ref_set(v___y_2898_, v___x_2935_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v_declName_2894_);
v___x_2938_ = v___x_2903_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_declName_2894_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
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
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec(v_declName_2894_);
v_a_2948_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2901_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2901_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4___boxed(lean_object* v_modifiers_2960_, lean_object* v_declName_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2960_, v_declName_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec_ref(v_modifiers_2960_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(lean_object* v_pre_2970_, lean_object* v_declName_2971_, lean_object* v_as_2972_, size_t v_sz_2973_, size_t v_i_2974_, lean_object* v_b_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_a_2984_; uint8_t v___x_2988_; 
v___x_2988_ = lean_usize_dec_lt(v_i_2974_, v_sz_2973_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; 
lean_dec(v_declName_2971_);
lean_dec(v_pre_2970_);
v___x_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2989_, 0, v_b_2975_);
return v___x_2989_;
}
else
{
lean_object* v___x_2990_; lean_object* v_a_2991_; lean_object* v___x_2992_; uint8_t v___x_2993_; 
v___x_2990_ = lean_box(0);
v_a_2991_ = lean_array_uget_borrowed(v_as_2972_, v_i_2974_);
lean_inc(v_a_2991_);
lean_inc(v_pre_2970_);
v___x_2992_ = l_Lean_Name_append(v_pre_2970_, v_a_2991_);
v___x_2993_ = lean_name_eq(v___x_2992_, v_declName_2971_);
lean_dec(v___x_2992_);
if (v___x_2993_ == 0)
{
v_a_2984_ = v___x_2990_;
goto v___jp_2983_;
}
else
{
lean_object* v___x_2994_; uint8_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_2994_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_2995_ = 0;
lean_inc(v_declName_2971_);
v___x_2996_ = l_Lean_MessageData_ofConstName(v_declName_2971_, v___x_2995_);
v___x_2997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2994_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
v___x_2998_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_2999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2997_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
lean_inc(v_pre_2970_);
v___x_3000_ = l_Lean_MessageData_ofName(v_pre_2970_);
v___x_3001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_2999_);
lean_ctor_set(v___x_3001_, 1, v___x_3000_);
v___x_3002_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_3003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3001_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
lean_inc(v_a_2991_);
v___x_3004_ = l_Lean_MessageData_ofName(v_a_2991_);
v___x_3005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3003_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
v___x_3006_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_3007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3005_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3007_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_dec_ref(v___x_3008_);
v_a_2984_ = v___x_2990_;
goto v___jp_2983_;
}
else
{
lean_dec(v_declName_2971_);
lean_dec(v_pre_2970_);
return v___x_3008_;
}
}
}
v___jp_2983_:
{
size_t v___x_2985_; size_t v___x_2986_; 
v___x_2985_ = ((size_t)1ULL);
v___x_2986_ = lean_usize_add(v_i_2974_, v___x_2985_);
v_i_2974_ = v___x_2986_;
v_b_2975_ = v_a_2984_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6___boxed(lean_object* v_pre_3009_, lean_object* v_declName_3010_, lean_object* v_as_3011_, lean_object* v_sz_3012_, lean_object* v_i_3013_, lean_object* v_b_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
size_t v_sz_boxed_3022_; size_t v_i_boxed_3023_; lean_object* v_res_3024_; 
v_sz_boxed_3022_ = lean_unbox_usize(v_sz_3012_);
lean_dec(v_sz_3012_);
v_i_boxed_3023_ = lean_unbox_usize(v_i_3013_);
lean_dec(v_i_3013_);
v_res_3024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_3009_, v_declName_3010_, v_as_3011_, v_sz_boxed_3022_, v_i_boxed_3023_, v_b_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec_ref(v_as_3011_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(lean_object* v_declName_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
if (lean_obj_tag(v_declName_3025_) == 1)
{
lean_object* v_pre_3033_; lean_object* v___x_3034_; lean_object* v_env_3035_; uint8_t v___x_3036_; 
v_pre_3033_ = lean_ctor_get(v_declName_3025_, 0);
lean_inc_n(v_pre_3033_, 2);
v___x_3034_ = lean_st_ref_get(v___y_3031_);
v_env_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc_ref(v_env_3035_);
lean_dec(v___x_3034_);
v___x_3036_ = l_Lean_isStructure(v_env_3035_, v_pre_3033_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_dec(v_pre_3033_);
lean_dec_ref(v_declName_3025_);
v___x_3037_ = lean_box(0);
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
return v___x_3038_;
}
else
{
lean_object* v___x_3039_; lean_object* v_env_3040_; lean_object* v_fieldNames_3041_; lean_object* v___x_3042_; size_t v_sz_3043_; size_t v___x_3044_; lean_object* v___x_3045_; 
v___x_3039_ = lean_st_ref_get(v___y_3031_);
v_env_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc_ref(v_env_3040_);
lean_dec(v___x_3039_);
lean_inc(v_pre_3033_);
v_fieldNames_3041_ = l_Lean_getStructureFieldsFlattened(v_env_3040_, v_pre_3033_, v___x_3036_);
v___x_3042_ = lean_box(0);
v_sz_3043_ = lean_array_size(v_fieldNames_3041_);
v___x_3044_ = ((size_t)0ULL);
v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_3033_, v_declName_3025_, v_fieldNames_3041_, v_sz_3043_, v___x_3044_, v___x_3042_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec_ref(v_fieldNames_3041_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; 
v_unused_3053_ = lean_ctor_get(v___x_3045_, 0);
lean_dec(v_unused_3053_);
v___x_3047_ = v___x_3045_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_dec(v___x_3045_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3042_);
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3042_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
else
{
return v___x_3045_;
}
}
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
lean_dec(v_declName_3025_);
v___x_3054_ = lean_box(0);
v___x_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
return v___x_3055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3___boxed(lean_object* v_declName_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v_declName_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(lean_object* v_currNamespace_3065_, lean_object* v_modifiers_3066_, lean_object* v_shortName_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3081_; lean_object* v_shortName_3082_; lean_object* v_currNamespace_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v_view_3143_; lean_object* v_name_3144_; lean_object* v_imported_3145_; lean_object* v_ctx_3146_; lean_object* v_scopes_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3205_; 
lean_inc(v_shortName_3067_);
v_view_3143_ = l_Lean_extractMacroScopes(v_shortName_3067_);
v_name_3144_ = lean_ctor_get(v_view_3143_, 0);
v_imported_3145_ = lean_ctor_get(v_view_3143_, 1);
v_ctx_3146_ = lean_ctor_get(v_view_3143_, 2);
v_scopes_3147_ = lean_ctor_get(v_view_3143_, 3);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_view_3143_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3149_ = v_view_3143_;
v_isShared_3150_ = v_isSharedCheck_3205_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_scopes_3147_);
lean_inc(v_ctx_3146_);
lean_inc(v_imported_3145_);
lean_inc(v_name_3144_);
lean_dec(v_view_3143_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3205_;
goto v_resetjp_3148_;
}
v___jp_3075_:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___y_3077_);
lean_ctor_set(v___x_3078_, 1, v___y_3076_);
v___x_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
return v___x_3079_;
}
v___jp_3080_:
{
lean_object* v___x_3090_; 
lean_inc(v___y_3081_);
v___x_3090_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v___y_3081_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v___x_3091_; 
lean_dec_ref(v___x_3090_);
v___x_3091_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_3066_, v___y_3081_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3091_) == 0)
{
uint8_t v_isProtected_3092_; 
v_isProtected_3092_ = lean_ctor_get_uint8(v_modifiers_3066_, sizeof(void*)*3 + 1);
if (v_isProtected_3092_ == 0)
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3101_; 
lean_dec(v_currNamespace_3083_);
v_a_3093_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3095_ = v___x_3091_;
v_isShared_3096_ = v_isSharedCheck_3101_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3091_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3101_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3097_, 0, v_a_3093_);
lean_ctor_set(v___x_3097_, 1, v_shortName_3082_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 0, v___x_3097_);
v___x_3099_ = v___x_3095_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
else
{
if (lean_obj_tag(v_currNamespace_3083_) == 1)
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3114_; 
v_a_3102_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3104_ = v___x_3091_;
v_isShared_3105_ = v_isSharedCheck_3114_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3091_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3114_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v_str_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
v_str_3106_ = lean_ctor_get(v_currNamespace_3083_, 1);
lean_inc_ref(v_str_3106_);
lean_dec_ref(v_currNamespace_3083_);
v___x_3107_ = lean_box(0);
v___x_3108_ = l_Lean_Name_str___override(v___x_3107_, v_str_3106_);
v___x_3109_ = l_Lean_Name_append(v___x_3108_, v_shortName_3082_);
v___x_3110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3110_, 0, v_a_3102_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 0, v___x_3110_);
v___x_3112_ = v___x_3104_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3110_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
else
{
lean_object* v_a_3115_; uint8_t v___x_3116_; 
lean_dec(v_currNamespace_3083_);
v_a_3115_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_a_3115_);
lean_dec_ref(v___x_3091_);
v___x_3116_ = l_Lean_Name_isAtomic(v_shortName_3082_);
if (v___x_3116_ == 0)
{
v___y_3076_ = v_shortName_3082_;
v___y_3077_ = v_a_3115_;
goto v___jp_3075_;
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v_a_3115_);
lean_dec(v_shortName_3082_);
v___x_3117_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_3118_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3117_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec(v_currNamespace_3083_);
lean_dec(v_shortName_3082_);
v_a_3127_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3091_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3091_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec(v_currNamespace_3083_);
lean_dec(v_shortName_3082_);
lean_dec(v___y_3081_);
v_a_3135_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3090_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3090_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
v_resetjp_3148_:
{
lean_object* v___x_3151_; uint8_t v_isRootName_3152_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; uint8_t v___x_3194_; 
v___x_3151_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_3152_ = l_Lean_Name_isPrefixOf(v___x_3151_, v_name_3144_);
v___x_3194_ = lean_name_eq(v_name_3144_, v___x_3151_);
if (v___x_3194_ == 0)
{
v___y_3181_ = v___y_3068_;
v___y_3182_ = v___y_3069_;
v___y_3183_ = v___y_3070_;
v___y_3184_ = v___y_3071_;
v___y_3185_ = v___y_3072_;
v___y_3186_ = v___y_3073_;
goto v___jp_3180_;
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_del_object(v___x_3149_);
lean_dec(v_scopes_3147_);
lean_dec(v_ctx_3146_);
lean_dec(v_imported_3145_);
lean_dec(v_name_3144_);
lean_dec(v_shortName_3067_);
lean_dec(v_currNamespace_3065_);
v___x_3195_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_3196_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3195_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
v___jp_3153_:
{
if (v_isRootName_3152_ == 0)
{
lean_dec(v_name_3144_);
v___y_3081_ = v___y_3160_;
v_shortName_3082_ = v_shortName_3067_;
v_currNamespace_3083_ = v_currNamespace_3065_;
v___y_3084_ = v___y_3159_;
v___y_3085_ = v___y_3158_;
v___y_3086_ = v___y_3156_;
v___y_3087_ = v___y_3155_;
v___y_3088_ = v___y_3157_;
v___y_3089_ = v___y_3154_;
goto v___jp_3080_;
}
else
{
lean_dec(v_shortName_3067_);
lean_dec(v_currNamespace_3065_);
if (lean_obj_tag(v_name_3144_) == 1)
{
lean_object* v_pre_3161_; lean_object* v_str_3162_; lean_object* v___x_3163_; lean_object* v_shortName_3164_; lean_object* v_currNamespace_3165_; 
v_pre_3161_ = lean_ctor_get(v_name_3144_, 0);
lean_inc(v_pre_3161_);
v_str_3162_ = lean_ctor_get(v_name_3144_, 1);
lean_inc_ref(v_str_3162_);
lean_dec_ref(v_name_3144_);
v___x_3163_ = lean_box(0);
v_shortName_3164_ = l_Lean_Name_str___override(v___x_3163_, v_str_3162_);
v_currNamespace_3165_ = l_Lean_Name_replacePrefix(v_pre_3161_, v___x_3151_, v___x_3163_);
v___y_3081_ = v___y_3160_;
v_shortName_3082_ = v_shortName_3164_;
v_currNamespace_3083_ = v_currNamespace_3165_;
v___y_3084_ = v___y_3159_;
v___y_3085_ = v___y_3158_;
v___y_3086_ = v___y_3156_;
v___y_3087_ = v___y_3155_;
v___y_3088_ = v___y_3157_;
v___y_3089_ = v___y_3154_;
goto v___jp_3080_;
}
else
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec(v___y_3160_);
v___x_3166_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_3167_ = l_Lean_MessageData_ofName(v_name_3144_);
v___x_3168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3166_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_3170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3168_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3170_, v___y_3159_, v___y_3158_, v___y_3156_, v___y_3155_, v___y_3157_, v___y_3154_);
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3171_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
}
v___jp_3180_:
{
if (v_isRootName_3152_ == 0)
{
lean_object* v___x_3187_; 
lean_del_object(v___x_3149_);
lean_dec(v_scopes_3147_);
lean_dec(v_ctx_3146_);
lean_dec(v_imported_3145_);
lean_inc(v_shortName_3067_);
lean_inc(v_currNamespace_3065_);
v___x_3187_ = l_Lean_Name_append(v_currNamespace_3065_, v_shortName_3067_);
v___y_3154_ = v___y_3186_;
v___y_3155_ = v___y_3184_;
v___y_3156_ = v___y_3183_;
v___y_3157_ = v___y_3185_;
v___y_3158_ = v___y_3182_;
v___y_3159_ = v___y_3181_;
v___y_3160_ = v___x_3187_;
goto v___jp_3153_;
}
else
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3191_; 
v___x_3188_ = lean_box(0);
lean_inc(v_name_3144_);
v___x_3189_ = l_Lean_Name_replacePrefix(v_name_3144_, v___x_3151_, v___x_3188_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 0, v___x_3189_);
v___x_3191_ = v___x_3149_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_imported_3145_);
lean_ctor_set(v_reuseFailAlloc_3193_, 2, v_ctx_3146_);
lean_ctor_set(v_reuseFailAlloc_3193_, 3, v_scopes_3147_);
v___x_3191_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_Lean_MacroScopesView_review(v___x_3191_);
v___y_3154_ = v___y_3186_;
v___y_3155_ = v___y_3184_;
v___y_3156_ = v___y_3183_;
v___y_3157_ = v___y_3185_;
v___y_3158_ = v___y_3182_;
v___y_3159_ = v___y_3181_;
v___y_3160_ = v___x_3192_;
goto v___jp_3153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2___boxed(lean_object* v_currNamespace_3206_, lean_object* v_modifiers_3207_, lean_object* v_shortName_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3206_, v_modifiers_3207_, v_shortName_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec_ref(v_modifiers_3207_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(uint8_t v___x_3217_, lean_object* v_as_3218_, size_t v_i_3219_, size_t v_stop_3220_, lean_object* v_b_3221_){
_start:
{
lean_object* v___y_3223_; uint8_t v___x_3227_; 
v___x_3227_ = lean_usize_dec_eq(v_i_3219_, v_stop_3220_);
if (v___x_3227_ == 0)
{
lean_object* v_fst_3228_; uint8_t v___x_3229_; 
v_fst_3228_ = lean_ctor_get(v_b_3221_, 0);
v___x_3229_ = lean_unbox(v_fst_3228_);
if (v___x_3229_ == 0)
{
lean_object* v_snd_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3239_; 
v_snd_3230_ = lean_ctor_get(v_b_3221_, 1);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_b_3221_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v_b_3221_, 0);
lean_dec(v_unused_3240_);
v___x_3232_ = v_b_3221_;
v_isShared_3233_ = v_isSharedCheck_3239_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_snd_3230_);
lean_dec(v_b_3221_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3239_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
uint8_t v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3237_; 
v___x_3234_ = 1;
v___x_3235_ = lean_box(v___x_3234_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v___x_3235_);
v___x_3237_ = v___x_3232_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_snd_3230_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
v___y_3223_ = v___x_3237_;
goto v___jp_3222_;
}
}
}
else
{
lean_object* v_snd_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3251_; 
v_snd_3241_ = lean_ctor_get(v_b_3221_, 1);
v_isSharedCheck_3251_ = !lean_is_exclusive(v_b_3221_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; 
v_unused_3252_ = lean_ctor_get(v_b_3221_, 0);
lean_dec(v_unused_3252_);
v___x_3243_ = v_b_3221_;
v_isShared_3244_ = v_isSharedCheck_3251_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_snd_3241_);
lean_dec(v_b_3221_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3251_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3249_; 
v___x_3245_ = lean_array_uget_borrowed(v_as_3218_, v_i_3219_);
lean_inc(v___x_3245_);
v___x_3246_ = lean_array_push(v_snd_3241_, v___x_3245_);
v___x_3247_ = lean_box(v___x_3217_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 1, v___x_3246_);
lean_ctor_set(v___x_3243_, 0, v___x_3247_);
v___x_3249_ = v___x_3243_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3247_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v___x_3246_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
v___y_3223_ = v___x_3249_;
goto v___jp_3222_;
}
}
}
}
else
{
return v_b_3221_;
}
v___jp_3222_:
{
size_t v___x_3224_; size_t v___x_3225_; 
v___x_3224_ = ((size_t)1ULL);
v___x_3225_ = lean_usize_add(v_i_3219_, v___x_3224_);
v_i_3219_ = v___x_3225_;
v_b_3221_ = v___y_3223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4___boxed(lean_object* v___x_3253_, lean_object* v_as_3254_, lean_object* v_i_3255_, lean_object* v_stop_3256_, lean_object* v_b_3257_){
_start:
{
uint8_t v___x_19313__boxed_3258_; size_t v_i_boxed_3259_; size_t v_stop_boxed_3260_; lean_object* v_res_3261_; 
v___x_19313__boxed_3258_ = lean_unbox(v___x_3253_);
v_i_boxed_3259_ = lean_unbox_usize(v_i_3255_);
lean_dec(v_i_3255_);
v_stop_boxed_3260_ = lean_unbox_usize(v_stop_3256_);
lean_dec(v_stop_3256_);
v_res_3261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_19313__boxed_3258_, v_as_3254_, v_i_boxed_3259_, v_stop_boxed_3260_, v_b_3257_);
lean_dec_ref(v_as_3254_);
return v_res_3261_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(lean_object* v_a_3262_, lean_object* v_x_3263_){
_start:
{
if (lean_obj_tag(v_x_3263_) == 0)
{
uint8_t v___x_3264_; 
v___x_3264_ = 0;
return v___x_3264_;
}
else
{
lean_object* v_head_3265_; lean_object* v_tail_3266_; uint8_t v___x_3267_; 
v_head_3265_ = lean_ctor_get(v_x_3263_, 0);
v_tail_3266_ = lean_ctor_get(v_x_3263_, 1);
v___x_3267_ = lean_name_eq(v_a_3262_, v_head_3265_);
if (v___x_3267_ == 0)
{
v_x_3263_ = v_tail_3266_;
goto _start;
}
else
{
return v___x_3267_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_expandDeclId_spec__0___boxed(lean_object* v_a_3269_, lean_object* v_x_3270_){
_start:
{
uint8_t v_res_3271_; lean_object* v_r_3272_; 
v_res_3271_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_a_3269_, v_x_3270_);
lean_dec(v_x_3270_);
lean_dec(v_a_3269_);
v_r_3272_ = lean_box(v_res_3271_);
return v_r_3272_;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = ((lean_object*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0));
v___x_3275_ = l_Lean_stringToMessageData(v___x_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(lean_object* v_u_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3284_ = lean_obj_once(&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1, &l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1);
v___x_3285_ = l_Lean_MessageData_ofName(v_u_3276_);
v___x_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_3288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3286_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3288_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___boxed(lean_object* v_u_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(lean_object* v_as_3299_, size_t v_i_3300_, size_t v_stop_3301_, lean_object* v_b_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v_a_3311_; uint8_t v___x_3315_; 
v___x_3315_ = lean_usize_dec_eq(v_i_3300_, v_stop_3301_);
if (v___x_3315_ == 0)
{
lean_object* v___x_3316_; lean_object* v_id_3317_; uint8_t v___x_3318_; 
v___x_3316_ = lean_array_uget_borrowed(v_as_3299_, v_i_3300_);
v_id_3317_ = l_Lean_Syntax_getId(v___x_3316_);
v___x_3318_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_id_3317_, v_b_3302_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3319_, 0, v_id_3317_);
lean_ctor_set(v___x_3319_, 1, v_b_3302_);
v_a_3311_ = v___x_3319_;
goto v___jp_3310_;
}
else
{
lean_object* v_fileName_3320_; lean_object* v_fileMap_3321_; lean_object* v_options_3322_; lean_object* v_currRecDepth_3323_; lean_object* v_maxRecDepth_3324_; lean_object* v_ref_3325_; lean_object* v_currNamespace_3326_; lean_object* v_openDecls_3327_; lean_object* v_initHeartbeats_3328_; lean_object* v_maxHeartbeats_3329_; lean_object* v_quotContext_3330_; lean_object* v_currMacroScope_3331_; uint8_t v_diag_3332_; lean_object* v_cancelTk_x3f_3333_; uint8_t v_suppressElabErrors_3334_; lean_object* v_inheritedTraceOptions_3335_; lean_object* v_ref_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_dec(v_b_3302_);
v_fileName_3320_ = lean_ctor_get(v___y_3307_, 0);
v_fileMap_3321_ = lean_ctor_get(v___y_3307_, 1);
v_options_3322_ = lean_ctor_get(v___y_3307_, 2);
v_currRecDepth_3323_ = lean_ctor_get(v___y_3307_, 3);
v_maxRecDepth_3324_ = lean_ctor_get(v___y_3307_, 4);
v_ref_3325_ = lean_ctor_get(v___y_3307_, 5);
v_currNamespace_3326_ = lean_ctor_get(v___y_3307_, 6);
v_openDecls_3327_ = lean_ctor_get(v___y_3307_, 7);
v_initHeartbeats_3328_ = lean_ctor_get(v___y_3307_, 8);
v_maxHeartbeats_3329_ = lean_ctor_get(v___y_3307_, 9);
v_quotContext_3330_ = lean_ctor_get(v___y_3307_, 10);
v_currMacroScope_3331_ = lean_ctor_get(v___y_3307_, 11);
v_diag_3332_ = lean_ctor_get_uint8(v___y_3307_, sizeof(void*)*14);
v_cancelTk_x3f_3333_ = lean_ctor_get(v___y_3307_, 12);
v_suppressElabErrors_3334_ = lean_ctor_get_uint8(v___y_3307_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3335_ = lean_ctor_get(v___y_3307_, 13);
v_ref_3336_ = l_Lean_replaceRef(v___x_3316_, v_ref_3325_);
lean_inc_ref(v_inheritedTraceOptions_3335_);
lean_inc(v_cancelTk_x3f_3333_);
lean_inc(v_currMacroScope_3331_);
lean_inc(v_quotContext_3330_);
lean_inc(v_maxHeartbeats_3329_);
lean_inc(v_initHeartbeats_3328_);
lean_inc(v_openDecls_3327_);
lean_inc(v_currNamespace_3326_);
lean_inc(v_maxRecDepth_3324_);
lean_inc(v_currRecDepth_3323_);
lean_inc_ref(v_options_3322_);
lean_inc_ref(v_fileMap_3321_);
lean_inc_ref(v_fileName_3320_);
v___x_3337_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3337_, 0, v_fileName_3320_);
lean_ctor_set(v___x_3337_, 1, v_fileMap_3321_);
lean_ctor_set(v___x_3337_, 2, v_options_3322_);
lean_ctor_set(v___x_3337_, 3, v_currRecDepth_3323_);
lean_ctor_set(v___x_3337_, 4, v_maxRecDepth_3324_);
lean_ctor_set(v___x_3337_, 5, v_ref_3336_);
lean_ctor_set(v___x_3337_, 6, v_currNamespace_3326_);
lean_ctor_set(v___x_3337_, 7, v_openDecls_3327_);
lean_ctor_set(v___x_3337_, 8, v_initHeartbeats_3328_);
lean_ctor_set(v___x_3337_, 9, v_maxHeartbeats_3329_);
lean_ctor_set(v___x_3337_, 10, v_quotContext_3330_);
lean_ctor_set(v___x_3337_, 11, v_currMacroScope_3331_);
lean_ctor_set(v___x_3337_, 12, v_cancelTk_x3f_3333_);
lean_ctor_set(v___x_3337_, 13, v_inheritedTraceOptions_3335_);
lean_ctor_set_uint8(v___x_3337_, sizeof(void*)*14, v_diag_3332_);
lean_ctor_set_uint8(v___x_3337_, sizeof(void*)*14 + 1, v_suppressElabErrors_3334_);
v___x_3338_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_id_3317_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___x_3337_, v___y_3308_);
lean_dec_ref(v___x_3337_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref(v___x_3338_);
v_a_3311_ = v_a_3339_;
goto v___jp_3310_;
}
else
{
return v___x_3338_;
}
}
}
else
{
lean_object* v___x_3340_; 
v___x_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3340_, 0, v_b_3302_);
return v___x_3340_;
}
v___jp_3310_:
{
size_t v___x_3312_; size_t v___x_3313_; 
v___x_3312_ = ((size_t)1ULL);
v___x_3313_ = lean_usize_add(v_i_3300_, v___x_3312_);
v_i_3300_ = v___x_3313_;
v_b_3302_ = v_a_3311_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3___boxed(lean_object* v_as_3341_, lean_object* v_i_3342_, lean_object* v_stop_3343_, lean_object* v_b_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
size_t v_i_boxed_3352_; size_t v_stop_boxed_3353_; lean_object* v_res_3354_; 
v_i_boxed_3352_ = lean_unbox_usize(v_i_3342_);
lean_dec(v_i_3342_);
v_stop_boxed_3353_ = lean_unbox_usize(v_stop_3343_);
lean_dec(v_stop_3343_);
v_res_3354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v_as_3341_, v_i_boxed_3352_, v_stop_boxed_3353_, v_b_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec_ref(v_as_3341_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId(lean_object* v_currNamespace_3355_, lean_object* v_currLevelNames_3356_, lean_object* v_declId_3357_, lean_object* v_modifiers_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v___x_3366_; lean_object* v_fst_3367_; lean_object* v_snd_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3463_; 
v___x_3366_ = l_Lean_Elab_expandDeclIdCore(v_declId_3357_);
v_fst_3367_ = lean_ctor_get(v___x_3366_, 0);
v_snd_3368_ = lean_ctor_get(v___x_3366_, 1);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3370_ = v___x_3366_;
v_isShared_3371_ = v_isSharedCheck_3463_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_snd_3368_);
lean_inc(v_fst_3367_);
lean_dec(v___x_3366_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3463_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v_levelNames_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3420_; lean_object* v___y_3431_; uint8_t v___x_3442_; 
v___x_3442_ = l_Lean_Syntax_isNone(v_snd_3368_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; uint8_t v___x_3449_; 
v___x_3443_ = lean_unsigned_to_nat(1u);
v___x_3444_ = l_Lean_Syntax_getArg(v_snd_3368_, v___x_3443_);
lean_dec(v_snd_3368_);
v___x_3445_ = l_Lean_Syntax_getArgs(v___x_3444_);
lean_dec(v___x_3444_);
v___x_3446_ = lean_unsigned_to_nat(0u);
v___x_3447_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__0));
v___x_3448_ = lean_array_get_size(v___x_3445_);
v___x_3449_ = lean_nat_dec_lt(v___x_3446_, v___x_3448_);
if (v___x_3449_ == 0)
{
lean_dec_ref(v___x_3445_);
lean_del_object(v___x_3370_);
v___y_3431_ = v___x_3447_;
goto v___jp_3430_;
}
else
{
lean_object* v___x_3450_; lean_object* v___x_3452_; 
v___x_3450_ = lean_box(v___x_3449_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 1, v___x_3447_);
lean_ctor_set(v___x_3370_, 0, v___x_3450_);
v___x_3452_ = v___x_3370_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3450_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v___x_3447_);
v___x_3452_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
uint8_t v___x_3453_; 
v___x_3453_ = lean_nat_dec_le(v___x_3448_, v___x_3448_);
if (v___x_3453_ == 0)
{
if (v___x_3449_ == 0)
{
lean_dec_ref(v___x_3452_);
lean_dec_ref(v___x_3445_);
v___y_3431_ = v___x_3447_;
goto v___jp_3430_;
}
else
{
size_t v___x_3454_; size_t v___x_3455_; lean_object* v___x_3456_; lean_object* v_snd_3457_; 
v___x_3454_ = ((size_t)0ULL);
v___x_3455_ = lean_usize_of_nat(v___x_3448_);
v___x_3456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3442_, v___x_3445_, v___x_3454_, v___x_3455_, v___x_3452_);
lean_dec_ref(v___x_3445_);
v_snd_3457_ = lean_ctor_get(v___x_3456_, 1);
lean_inc(v_snd_3457_);
lean_dec_ref(v___x_3456_);
v___y_3431_ = v_snd_3457_;
goto v___jp_3430_;
}
}
else
{
size_t v___x_3458_; size_t v___x_3459_; lean_object* v___x_3460_; lean_object* v_snd_3461_; 
v___x_3458_ = ((size_t)0ULL);
v___x_3459_ = lean_usize_of_nat(v___x_3448_);
v___x_3460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3442_, v___x_3445_, v___x_3458_, v___x_3459_, v___x_3452_);
lean_dec_ref(v___x_3445_);
v_snd_3461_ = lean_ctor_get(v___x_3460_, 1);
lean_inc(v_snd_3461_);
lean_dec_ref(v___x_3460_);
v___y_3431_ = v_snd_3461_;
goto v___jp_3430_;
}
}
}
}
else
{
lean_del_object(v___x_3370_);
lean_dec(v_snd_3368_);
v_levelNames_3373_ = v_currLevelNames_3356_;
v___y_3374_ = v_a_3359_;
v___y_3375_ = v_a_3360_;
v___y_3376_ = v_a_3361_;
v___y_3377_ = v_a_3362_;
v___y_3378_ = v_a_3363_;
v___y_3379_ = v_a_3364_;
goto v___jp_3372_;
}
v___jp_3372_:
{
lean_object* v_fileName_3380_; lean_object* v_fileMap_3381_; lean_object* v_options_3382_; lean_object* v_currRecDepth_3383_; lean_object* v_maxRecDepth_3384_; lean_object* v_ref_3385_; lean_object* v_currNamespace_3386_; lean_object* v_openDecls_3387_; lean_object* v_initHeartbeats_3388_; lean_object* v_maxHeartbeats_3389_; lean_object* v_quotContext_3390_; lean_object* v_currMacroScope_3391_; uint8_t v_diag_3392_; lean_object* v_cancelTk_x3f_3393_; uint8_t v_suppressElabErrors_3394_; lean_object* v_inheritedTraceOptions_3395_; lean_object* v_ref_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v_fileName_3380_ = lean_ctor_get(v___y_3378_, 0);
v_fileMap_3381_ = lean_ctor_get(v___y_3378_, 1);
v_options_3382_ = lean_ctor_get(v___y_3378_, 2);
v_currRecDepth_3383_ = lean_ctor_get(v___y_3378_, 3);
v_maxRecDepth_3384_ = lean_ctor_get(v___y_3378_, 4);
v_ref_3385_ = lean_ctor_get(v___y_3378_, 5);
v_currNamespace_3386_ = lean_ctor_get(v___y_3378_, 6);
v_openDecls_3387_ = lean_ctor_get(v___y_3378_, 7);
v_initHeartbeats_3388_ = lean_ctor_get(v___y_3378_, 8);
v_maxHeartbeats_3389_ = lean_ctor_get(v___y_3378_, 9);
v_quotContext_3390_ = lean_ctor_get(v___y_3378_, 10);
v_currMacroScope_3391_ = lean_ctor_get(v___y_3378_, 11);
v_diag_3392_ = lean_ctor_get_uint8(v___y_3378_, sizeof(void*)*14);
v_cancelTk_x3f_3393_ = lean_ctor_get(v___y_3378_, 12);
v_suppressElabErrors_3394_ = lean_ctor_get_uint8(v___y_3378_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3395_ = lean_ctor_get(v___y_3378_, 13);
v_ref_3396_ = l_Lean_replaceRef(v_declId_3357_, v_ref_3385_);
lean_inc_ref(v_inheritedTraceOptions_3395_);
lean_inc(v_cancelTk_x3f_3393_);
lean_inc(v_currMacroScope_3391_);
lean_inc(v_quotContext_3390_);
lean_inc(v_maxHeartbeats_3389_);
lean_inc(v_initHeartbeats_3388_);
lean_inc(v_openDecls_3387_);
lean_inc(v_currNamespace_3386_);
lean_inc(v_maxRecDepth_3384_);
lean_inc(v_currRecDepth_3383_);
lean_inc_ref(v_options_3382_);
lean_inc_ref(v_fileMap_3381_);
lean_inc_ref(v_fileName_3380_);
v___x_3397_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3397_, 0, v_fileName_3380_);
lean_ctor_set(v___x_3397_, 1, v_fileMap_3381_);
lean_ctor_set(v___x_3397_, 2, v_options_3382_);
lean_ctor_set(v___x_3397_, 3, v_currRecDepth_3383_);
lean_ctor_set(v___x_3397_, 4, v_maxRecDepth_3384_);
lean_ctor_set(v___x_3397_, 5, v_ref_3396_);
lean_ctor_set(v___x_3397_, 6, v_currNamespace_3386_);
lean_ctor_set(v___x_3397_, 7, v_openDecls_3387_);
lean_ctor_set(v___x_3397_, 8, v_initHeartbeats_3388_);
lean_ctor_set(v___x_3397_, 9, v_maxHeartbeats_3389_);
lean_ctor_set(v___x_3397_, 10, v_quotContext_3390_);
lean_ctor_set(v___x_3397_, 11, v_currMacroScope_3391_);
lean_ctor_set(v___x_3397_, 12, v_cancelTk_x3f_3393_);
lean_ctor_set(v___x_3397_, 13, v_inheritedTraceOptions_3395_);
lean_ctor_set_uint8(v___x_3397_, sizeof(void*)*14, v_diag_3392_);
lean_ctor_set_uint8(v___x_3397_, sizeof(void*)*14 + 1, v_suppressElabErrors_3394_);
v___x_3398_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3355_, v_modifiers_3358_, v_fst_3367_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___x_3397_, v___y_3379_);
lean_dec_ref(v___x_3397_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3410_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3401_ = v___x_3398_;
v_isShared_3402_ = v_isSharedCheck_3410_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3398_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3410_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v_fst_3403_; lean_object* v_snd_3404_; lean_object* v_docString_x3f_3405_; lean_object* v___x_3406_; lean_object* v___x_3408_; 
v_fst_3403_ = lean_ctor_get(v_a_3399_, 0);
lean_inc(v_fst_3403_);
v_snd_3404_ = lean_ctor_get(v_a_3399_, 1);
lean_inc(v_snd_3404_);
lean_dec(v_a_3399_);
v_docString_x3f_3405_ = lean_ctor_get(v_modifiers_3358_, 1);
lean_inc(v_docString_x3f_3405_);
v___x_3406_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3406_, 0, v_snd_3404_);
lean_ctor_set(v___x_3406_, 1, v_fst_3403_);
lean_ctor_set(v___x_3406_, 2, v_levelNames_3373_);
lean_ctor_set(v___x_3406_, 3, v_docString_x3f_3405_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 0, v___x_3406_);
v___x_3408_ = v___x_3401_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v_levelNames_3373_);
v_a_3411_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3398_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3398_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
v___jp_3419_:
{
if (lean_obj_tag(v___y_3420_) == 0)
{
lean_object* v_a_3421_; 
v_a_3421_ = lean_ctor_get(v___y_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref(v___y_3420_);
v_levelNames_3373_ = v_a_3421_;
v___y_3374_ = v_a_3359_;
v___y_3375_ = v_a_3360_;
v___y_3376_ = v_a_3361_;
v___y_3377_ = v_a_3362_;
v___y_3378_ = v_a_3363_;
v___y_3379_ = v_a_3364_;
goto v___jp_3372_;
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec(v_fst_3367_);
lean_dec(v_currNamespace_3355_);
v_a_3422_ = lean_ctor_get(v___y_3420_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___y_3420_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___y_3420_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___y_3420_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
v___jp_3430_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = lean_array_get_size(v___y_3431_);
v___x_3434_ = lean_nat_dec_lt(v___x_3432_, v___x_3433_);
if (v___x_3434_ == 0)
{
lean_dec_ref(v___y_3431_);
v_levelNames_3373_ = v_currLevelNames_3356_;
v___y_3374_ = v_a_3359_;
v___y_3375_ = v_a_3360_;
v___y_3376_ = v_a_3361_;
v___y_3377_ = v_a_3362_;
v___y_3378_ = v_a_3363_;
v___y_3379_ = v_a_3364_;
goto v___jp_3372_;
}
else
{
uint8_t v___x_3435_; 
v___x_3435_ = lean_nat_dec_le(v___x_3433_, v___x_3433_);
if (v___x_3435_ == 0)
{
if (v___x_3434_ == 0)
{
lean_dec_ref(v___y_3431_);
v_levelNames_3373_ = v_currLevelNames_3356_;
v___y_3374_ = v_a_3359_;
v___y_3375_ = v_a_3360_;
v___y_3376_ = v_a_3361_;
v___y_3377_ = v_a_3362_;
v___y_3378_ = v_a_3363_;
v___y_3379_ = v_a_3364_;
goto v___jp_3372_;
}
else
{
size_t v___x_3436_; size_t v___x_3437_; lean_object* v___x_3438_; 
v___x_3436_ = ((size_t)0ULL);
v___x_3437_ = lean_usize_of_nat(v___x_3433_);
v___x_3438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3431_, v___x_3436_, v___x_3437_, v_currLevelNames_3356_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
lean_dec_ref(v___y_3431_);
v___y_3420_ = v___x_3438_;
goto v___jp_3419_;
}
}
else
{
size_t v___x_3439_; size_t v___x_3440_; lean_object* v___x_3441_; 
v___x_3439_ = ((size_t)0ULL);
v___x_3440_ = lean_usize_of_nat(v___x_3433_);
v___x_3441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3431_, v___x_3439_, v___x_3440_, v_currLevelNames_3356_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
lean_dec_ref(v___y_3431_);
v___y_3420_ = v___x_3441_;
goto v___jp_3419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___boxed(lean_object* v_currNamespace_3464_, lean_object* v_currLevelNames_3465_, lean_object* v_declId_3466_, lean_object* v_modifiers_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Lean_Elab_expandDeclId(v_currNamespace_3464_, v_currLevelNames_3465_, v_declId_3466_, v_modifiers_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
lean_dec(v_a_3471_);
lean_dec_ref(v_a_3470_);
lean_dec(v_a_3469_);
lean_dec_ref(v_a_3468_);
lean_dec_ref(v_modifiers_3467_);
lean_dec(v_declId_3466_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(lean_object* v_00_u03b1_3476_, lean_object* v_u_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v___x_3485_; 
v___x_3485_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___boxed(lean_object* v_00_u03b1_3486_, lean_object* v_u_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(v_00_u03b1_3486_, v_u_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(lean_object* v_00_u03b1_3496_, lean_object* v_msg_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3506_, lean_object* v_msg_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(v_00_u03b1_3506_, v_msg_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(lean_object* v_msgData_3516_, lean_object* v_macroStack_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_3516_, v_macroStack_3517_, v___y_3522_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_3526_, lean_object* v_macroStack_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(v_msgData_3526_, v_macroStack_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(lean_object* v_t_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v___x_3544_; 
v___x_3544_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_3536_, v___y_3542_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___boxed(lean_object* v_t_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(v_t_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(lean_object* v_env_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v___x_3562_; 
v___x_3562_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_3554_, v___y_3558_, v___y_3560_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___boxed(lean_object* v_env_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(v_env_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(lean_object* v_00_u03b1_3572_, lean_object* v_env_3573_, lean_object* v_x_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_3573_, v_x_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3583_, lean_object* v_env_3584_, lean_object* v_x_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(v_00_u03b1_3583_, v_env_3584_, v_x_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(lean_object* v_00_u03b1_3594_, lean_object* v_constName_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___boxed(lean_object* v_00_u03b1_3604_, lean_object* v_constName_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(v_00_u03b1_3604_, v_constName_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(lean_object* v_00_u03b1_3614_, lean_object* v_ref_3615_, lean_object* v_constName_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_3615_, v_constName_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___boxed(lean_object* v_00_u03b1_3625_, lean_object* v_ref_3626_, lean_object* v_constName_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(v_00_u03b1_3625_, v_ref_3626_, v_constName_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v_ref_3626_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(lean_object* v_00_u03b1_3636_, lean_object* v_ref_3637_, lean_object* v_msg_3638_, lean_object* v_declHint_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_3637_, v_msg_3638_, v_declHint_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___boxed(lean_object* v_00_u03b1_3648_, lean_object* v_ref_3649_, lean_object* v_msg_3650_, lean_object* v_declHint_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(v_00_u03b1_3648_, v_ref_3649_, v_msg_3650_, v_declHint_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v_ref_3649_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(lean_object* v_msg_3660_, lean_object* v_declHint_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v___x_3669_; 
v___x_3669_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_3660_, v_declHint_3661_, v___y_3667_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___boxed(lean_object* v_msg_3670_, lean_object* v_declHint_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(v_msg_3670_, v_declHint_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(lean_object* v_00_u03b1_3680_, lean_object* v_ref_3681_, lean_object* v_msg_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_3681_, v_msg_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___boxed(lean_object* v_00_u03b1_3691_, lean_object* v_ref_3692_, lean_object* v_msg_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(v_00_u03b1_3691_, v_ref_3692_, v_msg_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v_ref_3692_);
return v_res_3701_;
}
}
lean_object* runtime_initialize_Lean_DocString_Add(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_EnvLinter_Nolint(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeclModifiers(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_DocString_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_EnvLinter_Nolint(builtin);
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
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* initialize_Lean_Linter_EnvLinter_Nolint(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeclModifiers(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_EnvLinter_Nolint(builtin);
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
