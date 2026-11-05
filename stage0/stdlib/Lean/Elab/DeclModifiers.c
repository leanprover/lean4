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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___impl___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "commentBody"};
static const lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__2_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__2;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__3 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__3_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__16;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__4;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_57_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
uint8_t v___x_705__boxed_90_; lean_object* v_res_91_; 
v___x_705__boxed_90_ = lean_unbox(v___x_86_);
v_res_91_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(v_____do__lift_85_, v___x_705__boxed_90_, v_inst_87_, v_inst_88_, v_____do__lift_89_);
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
uint8_t v___x_749__boxed_112_; lean_object* v_res_113_; 
v___x_749__boxed_112_ = lean_unbox(v___x_104_);
v_res_113_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(v___x_749__boxed_112_, v_inst_105_, v_inst_106_, v_inst_107_, v_inst_108_, v_declName_109_, v_toBind_110_, v_____do__lift_111_);
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
uint8_t v___x_775__boxed_134_; lean_object* v_res_135_; 
v___x_775__boxed_134_ = lean_unbox(v___x_127_);
v_res_135_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(v_toMonadRef_126_, v___x_775__boxed_134_, v_inst_128_, v_inst_129_, v_inst_130_, v_inst_131_, v_toBind_132_, v_declName_133_);
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
uint8_t v___x_809__boxed_158_; lean_object* v_res_159_; 
v___x_809__boxed_158_ = lean_unbox(v___x_154_);
v_res_159_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(v_val_153_, v___x_809__boxed_158_, v_inst_155_, v_inst_156_, v_____r_157_);
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
uint8_t v___x_886__boxed_207_; lean_object* v_res_208_; 
v___x_886__boxed_207_ = lean_unbox(v___x_201_);
v_res_208_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(v_declName_200_, v___x_886__boxed_207_, v_inst_202_, v_inst_203_, v_toBind_204_, v___f_205_, v_____r_206_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(lean_object* v_declName_233_, uint8_t v___x_234_, lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_toBind_237_, lean_object* v___f_238_, lean_object* v_env_239_, lean_object* v___f_240_, lean_object* v_____do__lift_241_){
_start:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
lean_inc(v_declName_233_);
v___x_250_ = l_Lean_privateToUserName(v_declName_233_);
lean_inc_ref(v_env_239_);
v___x_251_ = lean_is_reserved_name(v_env_239_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; uint8_t v___x_253_; 
lean_inc(v_declName_233_);
v___x_252_ = l_Lean_mkPrivateName(v_____do__lift_241_, v_declName_233_);
v___x_253_ = lean_is_reserved_name(v_env_239_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v___f_238_);
lean_dec(v_toBind_237_);
lean_dec_ref(v_inst_236_);
lean_dec_ref(v_inst_235_);
lean_dec(v_declName_233_);
v___x_254_ = lean_box(0);
v___x_255_ = lean_apply_1(v___f_240_, v___x_254_);
return v___x_255_;
}
else
{
lean_dec(v___f_240_);
goto v___jp_242_;
}
}
else
{
lean_dec(v___f_240_);
lean_dec_ref(v_env_239_);
goto v___jp_242_;
}
v___jp_242_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_243_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_244_ = l_Lean_MessageData_ofConstName(v_declName_233_, v___x_234_);
v___x_245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = l_Lean_throwError___redArg(v_inst_235_, v_inst_236_, v___x_247_);
v___x_249_ = lean_apply_4(v_toBind_237_, lean_box(0), lean_box(0), v___x_248_, v___f_238_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___boxed(lean_object* v_declName_256_, lean_object* v___x_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_toBind_260_, lean_object* v___f_261_, lean_object* v_env_262_, lean_object* v___f_263_, lean_object* v_____do__lift_264_){
_start:
{
uint8_t v___x_958__boxed_265_; lean_object* v_res_266_; 
v___x_958__boxed_265_ = lean_unbox(v___x_257_);
v_res_266_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(v_declName_256_, v___x_958__boxed_265_, v_inst_258_, v_inst_259_, v_toBind_260_, v___f_261_, v_env_262_, v___f_263_, v_____do__lift_264_);
lean_dec_ref(v_____do__lift_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8(lean_object* v_toBind_267_, lean_object* v_getEnv_268_, lean_object* v___f_269_, lean_object* v_____r_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lean_apply_4(v_toBind_267_, lean_box(0), lean_box(0), v_getEnv_268_, v___f_269_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__0));
v___x_274_ = l_Lean_stringToMessageData(v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(lean_object* v_declName_275_, uint8_t v___x_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_toBind_279_, lean_object* v___f_280_, lean_object* v___f_281_, lean_object* v_____r_282_){
_start:
{
lean_object* v___x_283_; 
lean_inc(v_declName_275_);
v___x_283_ = l_Lean_privateToUserName_x3f(v_declName_275_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v___f_281_);
v___x_284_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_285_ = l_Lean_MessageData_ofConstName(v_declName_275_, v___x_276_);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = l_Lean_throwError___redArg(v_inst_277_, v_inst_278_, v___x_288_);
v___x_290_ = lean_apply_4(v_toBind_279_, lean_box(0), lean_box(0), v___x_289_, v___f_280_);
return v___x_290_;
}
else
{
lean_object* v_val_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v___f_280_);
lean_dec(v_declName_275_);
v_val_291_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v___x_283_, 1);
v___x_292_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1);
v___x_293_ = l_Lean_MessageData_ofConstName(v_val_291_, v___x_276_);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_throwError___redArg(v_inst_277_, v_inst_278_, v___x_296_);
v___x_298_ = lean_apply_4(v_toBind_279_, lean_box(0), lean_box(0), v___x_297_, v___f_281_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___boxed(lean_object* v_declName_299_, lean_object* v___x_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_toBind_303_, lean_object* v___f_304_, lean_object* v___f_305_, lean_object* v_____r_306_){
_start:
{
uint8_t v___x_1031__boxed_307_; lean_object* v_res_308_; 
v___x_1031__boxed_307_ = lean_unbox(v___x_300_);
v_res_308_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(v_declName_299_, v___x_1031__boxed_307_, v_inst_301_, v_inst_302_, v_toBind_303_, v___f_304_, v___f_305_, v_____r_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10(lean_object* v_toMonadRef_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_toBind_314_, lean_object* v_declName_315_, lean_object* v_toPure_316_, lean_object* v_getEnv_317_, lean_object* v_inst_318_, lean_object* v_env_319_){
_start:
{
uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v_addInfo_322_; lean_object* v_env_323_; lean_object* v___f_324_; lean_object* v___f_325_; lean_object* v___f_326_; lean_object* v___f_327_; lean_object* v___x_328_; lean_object* v___f_329_; uint8_t v___x_330_; uint8_t v___x_331_; 
v___x_320_ = 0;
v___x_321_ = lean_box(v___x_320_);
lean_inc_n(v_toBind_314_, 4);
lean_inc_ref_n(v_inst_313_, 4);
lean_inc_ref(v_inst_312_);
lean_inc_ref(v_inst_311_);
lean_inc_ref_n(v_inst_310_, 4);
lean_inc_ref(v_toMonadRef_309_);
v_addInfo_322_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v_addInfo_322_, 0, v_toMonadRef_309_);
lean_closure_set(v_addInfo_322_, 1, v___x_321_);
lean_closure_set(v_addInfo_322_, 2, v_inst_310_);
lean_closure_set(v_addInfo_322_, 3, v_inst_311_);
lean_closure_set(v_addInfo_322_, 4, v_inst_312_);
lean_closure_set(v_addInfo_322_, 5, v_inst_313_);
lean_closure_set(v_addInfo_322_, 6, v_toBind_314_);
v_env_323_ = l_Lean_Environment_setExporting(v_env_319_, v___x_320_);
lean_inc_ref(v_addInfo_322_);
lean_inc_ref_n(v_env_323_, 4);
lean_inc_n(v_declName_315_, 4);
v___f_324_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__4), 8, 7);
lean_closure_set(v___f_324_, 0, v_declName_315_);
lean_closure_set(v___f_324_, 1, v_toPure_316_);
lean_closure_set(v___f_324_, 2, v_env_323_);
lean_closure_set(v___f_324_, 3, v_inst_310_);
lean_closure_set(v___f_324_, 4, v_inst_313_);
lean_closure_set(v___f_324_, 5, v_addInfo_322_);
lean_closure_set(v___f_324_, 6, v_toBind_314_);
lean_inc_ref(v___f_324_);
v___f_325_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_325_, 0, v___f_324_);
v___f_326_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7), 9, 8);
lean_closure_set(v___f_326_, 0, v_env_323_);
lean_closure_set(v___f_326_, 1, v_declName_315_);
lean_closure_set(v___f_326_, 2, v___f_324_);
lean_closure_set(v___f_326_, 3, v_inst_310_);
lean_closure_set(v___f_326_, 4, v_inst_313_);
lean_closure_set(v___f_326_, 5, v_toBind_314_);
lean_closure_set(v___f_326_, 6, v___f_325_);
lean_closure_set(v___f_326_, 7, v_addInfo_322_);
lean_inc_ref(v___f_326_);
v___f_327_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_327_, 0, v___f_326_);
v___x_328_ = lean_box(v___x_320_);
v___f_329_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___boxed), 9, 8);
lean_closure_set(v___f_329_, 0, v_declName_315_);
lean_closure_set(v___f_329_, 1, v___x_328_);
lean_closure_set(v___f_329_, 2, v_inst_310_);
lean_closure_set(v___f_329_, 3, v_inst_313_);
lean_closure_set(v___f_329_, 4, v_toBind_314_);
lean_closure_set(v___f_329_, 5, v___f_327_);
lean_closure_set(v___f_329_, 6, v_env_323_);
lean_closure_set(v___f_329_, 7, v___f_326_);
v___x_330_ = 1;
v___x_331_ = l_Lean_Environment_contains(v_env_323_, v_declName_315_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v_declName_315_);
lean_dec_ref(v_inst_313_);
lean_dec_ref(v_inst_311_);
lean_dec_ref(v_toMonadRef_309_);
v___x_332_ = lean_apply_4(v_toBind_314_, lean_box(0), lean_box(0), v_getEnv_317_, v___f_329_);
v___x_333_ = l_Lean_withEnv___redArg(v_inst_310_, v_inst_318_, v_inst_312_, v_env_323_, v___x_332_);
return v___x_333_;
}
else
{
lean_object* v___f_334_; lean_object* v___x_335_; lean_object* v___f_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
lean_inc_n(v_toBind_314_, 3);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8), 4, 3);
lean_closure_set(v___f_334_, 0, v_toBind_314_);
lean_closure_set(v___f_334_, 1, v_getEnv_317_);
lean_closure_set(v___f_334_, 2, v___f_329_);
v___x_335_ = lean_box(v___x_330_);
lean_inc_ref(v___f_334_);
lean_inc_ref(v_inst_313_);
lean_inc_ref_n(v_inst_310_, 2);
lean_inc(v_declName_315_);
v___f_336_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_336_, 0, v_declName_315_);
lean_closure_set(v___f_336_, 1, v___x_335_);
lean_closure_set(v___f_336_, 2, v_inst_310_);
lean_closure_set(v___f_336_, 3, v_inst_313_);
lean_closure_set(v___f_336_, 4, v_toBind_314_);
lean_closure_set(v___f_336_, 5, v___f_334_);
lean_closure_set(v___f_336_, 6, v___f_334_);
lean_inc_ref(v_inst_312_);
v___x_337_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(v_toMonadRef_309_, v___x_320_, v_inst_310_, v_inst_311_, v_inst_312_, v_inst_313_, v_toBind_314_, v_declName_315_);
v___x_338_ = lean_apply_4(v_toBind_314_, lean_box(0), lean_box(0), v___x_337_, v___f_336_);
v___x_339_ = l_Lean_withEnv___redArg(v_inst_310_, v_inst_318_, v_inst_312_, v_env_323_, v___x_338_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg(lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_declName_345_){
_start:
{
lean_object* v_toApplicative_346_; lean_object* v_toBind_347_; lean_object* v_getEnv_348_; lean_object* v_toMonadRef_349_; lean_object* v_toPure_350_; lean_object* v___f_351_; lean_object* v___x_352_; 
v_toApplicative_346_ = lean_ctor_get(v_inst_340_, 0);
v_toBind_347_ = lean_ctor_get(v_inst_340_, 1);
lean_inc_n(v_toBind_347_, 2);
v_getEnv_348_ = lean_ctor_get(v_inst_341_, 0);
lean_inc_n(v_getEnv_348_, 2);
v_toMonadRef_349_ = lean_ctor_get(v_inst_342_, 1);
lean_inc_ref(v_toMonadRef_349_);
v_toPure_350_ = lean_ctor_get(v_toApplicative_346_, 1);
lean_inc(v_toPure_350_);
v___f_351_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10), 11, 10);
lean_closure_set(v___f_351_, 0, v_toMonadRef_349_);
lean_closure_set(v___f_351_, 1, v_inst_340_);
lean_closure_set(v___f_351_, 2, v_inst_344_);
lean_closure_set(v___f_351_, 3, v_inst_341_);
lean_closure_set(v___f_351_, 4, v_inst_342_);
lean_closure_set(v___f_351_, 5, v_toBind_347_);
lean_closure_set(v___f_351_, 6, v_declName_345_);
lean_closure_set(v___f_351_, 7, v_toPure_350_);
lean_closure_set(v___f_351_, 8, v_getEnv_348_);
lean_closure_set(v___f_351_, 9, v_inst_343_);
v___x_352_ = lean_apply_4(v_toBind_347_, lean_box(0), lean_box(0), v_getEnv_348_, v___f_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared(lean_object* v_m_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_declName_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(v_inst_354_, v_inst_355_, v_inst_356_, v_inst_357_, v_inst_358_, v_declName_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx___impl(uint8_t v_x_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_box(v_x_361_);
v___x_363_ = lean_obj_tag_nat(v___x_362_);
lean_dec(v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx___impl___boxed(lean_object* v_x_364_){
_start:
{
uint8_t v_x_4__boxed_365_; lean_object* v_res_366_; 
v_x_4__boxed_365_ = lean_unbox(v_x_364_);
v_res_366_ = l_Lean_Elab_Visibility_ctorIdx___impl(v_x_4__boxed_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___redArg(lean_object* v_k_367_){
_start:
{
lean_inc(v_k_367_);
return v_k_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___redArg___boxed(lean_object* v_k_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Elab_Visibility_ctorElim___redArg(v_k_368_);
lean_dec(v_k_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim(lean_object* v_motive_370_, lean_object* v_ctorIdx_371_, uint8_t v_t_372_, lean_object* v_h_373_, lean_object* v_k_374_){
_start:
{
lean_inc(v_k_374_);
return v_k_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___boxed(lean_object* v_motive_375_, lean_object* v_ctorIdx_376_, lean_object* v_t_377_, lean_object* v_h_378_, lean_object* v_k_379_){
_start:
{
uint8_t v_t_boxed_380_; lean_object* v_res_381_; 
v_t_boxed_380_ = lean_unbox(v_t_377_);
v_res_381_ = l_Lean_Elab_Visibility_ctorElim(v_motive_375_, v_ctorIdx_376_, v_t_boxed_380_, v_h_378_, v_k_379_);
lean_dec(v_k_379_);
lean_dec(v_ctorIdx_376_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___redArg(lean_object* v_regular_382_){
_start:
{
lean_inc(v_regular_382_);
return v_regular_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___redArg___boxed(lean_object* v_regular_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Elab_Visibility_regular_elim___redArg(v_regular_383_);
lean_dec(v_regular_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim(lean_object* v_motive_385_, uint8_t v_t_386_, lean_object* v_h_387_, lean_object* v_regular_388_){
_start:
{
lean_inc(v_regular_388_);
return v_regular_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___boxed(lean_object* v_motive_389_, lean_object* v_t_390_, lean_object* v_h_391_, lean_object* v_regular_392_){
_start:
{
uint8_t v_t_boxed_393_; lean_object* v_res_394_; 
v_t_boxed_393_ = lean_unbox(v_t_390_);
v_res_394_ = l_Lean_Elab_Visibility_regular_elim(v_motive_389_, v_t_boxed_393_, v_h_391_, v_regular_392_);
lean_dec(v_regular_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___redArg(lean_object* v_private_395_){
_start:
{
lean_inc(v_private_395_);
return v_private_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___redArg___boxed(lean_object* v_private_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Elab_Visibility_private_elim___redArg(v_private_396_);
lean_dec(v_private_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim(lean_object* v_motive_398_, uint8_t v_t_399_, lean_object* v_h_400_, lean_object* v_private_401_){
_start:
{
lean_inc(v_private_401_);
return v_private_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___boxed(lean_object* v_motive_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_private_405_){
_start:
{
uint8_t v_t_boxed_406_; lean_object* v_res_407_; 
v_t_boxed_406_ = lean_unbox(v_t_403_);
v_res_407_ = l_Lean_Elab_Visibility_private_elim(v_motive_402_, v_t_boxed_406_, v_h_404_, v_private_405_);
lean_dec(v_private_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___redArg(lean_object* v_public_408_){
_start:
{
lean_inc(v_public_408_);
return v_public_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___redArg___boxed(lean_object* v_public_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Elab_Visibility_public_elim___redArg(v_public_409_);
lean_dec(v_public_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim(lean_object* v_motive_411_, uint8_t v_t_412_, lean_object* v_h_413_, lean_object* v_public_414_){
_start:
{
lean_inc(v_public_414_);
return v_public_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___boxed(lean_object* v_motive_415_, lean_object* v_t_416_, lean_object* v_h_417_, lean_object* v_public_418_){
_start:
{
uint8_t v_t_boxed_419_; lean_object* v_res_420_; 
v_t_boxed_419_ = lean_unbox(v_t_416_);
v_res_420_ = l_Lean_Elab_Visibility_public_elim(v_motive_415_, v_t_boxed_419_, v_h_417_, v_public_418_);
lean_dec(v_public_418_);
return v_res_420_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedVisibility_default(void){
_start:
{
uint8_t v___x_421_; 
v___x_421_ = 0;
return v___x_421_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedVisibility(void){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0(uint8_t v_x_426_){
_start:
{
switch(v_x_426_)
{
case 0:
{
lean_object* v___x_427_; 
v___x_427_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__0));
return v___x_427_;
}
case 1:
{
lean_object* v___x_428_; 
v___x_428_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__1));
return v___x_428_;
}
default: 
{
lean_object* v___x_429_; 
v___x_429_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__2));
return v___x_429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0___boxed(lean_object* v_x_430_){
_start:
{
uint8_t v_x_36__boxed_431_; lean_object* v_res_432_; 
v_x_36__boxed_431_ = lean_unbox(v_x_430_);
v_res_432_ = l_Lean_Elab_instToStringVisibility___lam__0(v_x_36__boxed_431_);
return v_res_432_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPrivate(uint8_t v_x_435_){
_start:
{
if (v_x_435_ == 1)
{
uint8_t v___x_436_; 
v___x_436_ = 1;
return v___x_436_;
}
else
{
uint8_t v___x_437_; 
v___x_437_ = 0;
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPrivate___boxed(lean_object* v_x_438_){
_start:
{
uint8_t v_x_17__boxed_439_; uint8_t v_res_440_; lean_object* v_r_441_; 
v_x_17__boxed_439_ = lean_unbox(v_x_438_);
v_res_440_ = l_Lean_Elab_Visibility_isPrivate(v_x_17__boxed_439_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPublic(uint8_t v_x_442_){
_start:
{
if (v_x_442_ == 2)
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
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPublic___boxed(lean_object* v_x_445_){
_start:
{
uint8_t v_x_17__boxed_446_; uint8_t v_res_447_; lean_object* v_r_448_; 
v_x_17__boxed_446_ = lean_unbox(v_x_445_);
v_res_447_ = l_Lean_Elab_Visibility_isPublic(v_x_17__boxed_446_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isInferredPublic(lean_object* v_env_449_, uint8_t v_v_450_){
_start:
{
uint8_t v___y_452_; uint8_t v_isExporting_455_; 
v_isExporting_455_ = lean_ctor_get_uint8(v_env_449_, sizeof(void*)*13);
if (v_isExporting_455_ == 0)
{
lean_object* v___x_456_; uint8_t v_isModule_457_; 
v___x_456_ = l_Lean_Environment_header(v_env_449_);
v_isModule_457_ = lean_ctor_get_uint8(v___x_456_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_456_);
if (v_isModule_457_ == 0)
{
uint8_t v___x_458_; 
v___x_458_ = 1;
v___y_452_ = v___x_458_;
goto v___jp_451_;
}
else
{
uint8_t v___x_459_; 
v___x_459_ = l_Lean_Elab_Visibility_isPublic(v_v_450_);
return v___x_459_;
}
}
else
{
v___y_452_ = v_isExporting_455_;
goto v___jp_451_;
}
v___jp_451_:
{
uint8_t v___x_453_; 
v___x_453_ = l_Lean_Elab_Visibility_isPrivate(v_v_450_);
if (v___x_453_ == 0)
{
return v___y_452_;
}
else
{
uint8_t v___x_454_; 
v___x_454_ = 0;
return v___x_454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isInferredPublic___boxed(lean_object* v_env_460_, lean_object* v_v_461_){
_start:
{
uint8_t v_v_boxed_462_; uint8_t v_res_463_; lean_object* v_r_464_; 
v_v_boxed_462_ = lean_unbox(v_v_461_);
v_res_463_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_460_, v_v_boxed_462_);
lean_dec_ref(v_env_460_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__0(lean_object* v_toPure_465_, lean_object* v_____r_466_){
_start:
{
uint8_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = 2;
v___x_468_ = lean_box(v___x_467_);
v___x_469_ = lean_apply_2(v_toPure_465_, lean_box(0), v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__2(lean_object* v_toPure_470_, lean_object* v_____r_471_){
_start:
{
uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = 1;
v___x_473_ = lean_box(v___x_472_);
v___x_474_ = lean_apply_2(v_toPure_470_, lean_box(0), v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__0));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__2));
v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__10));
v___x_497_ = l_Lean_stringToMessageData(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__12));
v___x_500_ = l_Lean_stringToMessageData(v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3(lean_object* v_vis_x3f_501_, lean_object* v_toPure_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_toBind_509_, lean_object* v___f_510_, lean_object* v___f_511_, uint8_t v_isExample_512_, lean_object* v___f_513_, lean_object* v___f_514_, lean_object* v_env_515_){
_start:
{
if (lean_obj_tag(v_vis_x3f_501_) == 0)
{
uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v___f_514_);
lean_dec(v___f_513_);
lean_dec(v___f_511_);
lean_dec(v___f_510_);
lean_dec(v_toBind_509_);
lean_dec_ref(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec(v_inst_506_);
lean_dec_ref(v_inst_505_);
lean_dec_ref(v_inst_504_);
lean_dec_ref(v_inst_503_);
v___x_519_ = 0;
v___x_520_ = lean_box(v___x_519_);
v___x_521_ = lean_apply_2(v_toPure_502_, lean_box(0), v___x_520_);
return v___x_521_;
}
else
{
lean_object* v_val_522_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___x_545_; uint8_t v___x_546_; 
lean_dec(v_toPure_502_);
v_val_522_ = lean_ctor_get(v_vis_x3f_501_, 0);
lean_inc_n(v_val_522_, 2);
lean_dec_ref_known(v_vis_x3f_501_, 1);
v___x_545_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8));
v___x_546_ = l_Lean_Syntax_isOfKind(v_val_522_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; uint8_t v___x_548_; 
lean_dec(v___f_514_);
lean_dec(v___f_513_);
v___x_547_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9));
lean_inc(v_val_522_);
v___x_548_ = l_Lean_Syntax_isOfKind(v_val_522_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v___f_511_);
lean_dec(v___f_510_);
lean_dec(v_toBind_509_);
lean_dec_ref(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec(v_inst_506_);
lean_dec_ref(v_inst_505_);
v___x_549_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11);
v___x_550_ = l_Lean_throwErrorAt___redArg(v_inst_503_, v_inst_504_, v_val_522_, v___x_549_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; 
lean_dec_ref(v_inst_504_);
v___x_551_ = l_Lean_Syntax_getHeadInfo(v_val_522_);
if (lean_obj_tag(v___x_551_) == 0)
{
uint8_t v_isExporting_552_; 
lean_dec_ref_known(v___x_551_, 4);
v_isExporting_552_ = lean_ctor_get_uint8(v_env_515_, sizeof(void*)*13);
if (v_isExporting_552_ == 0)
{
goto v___jp_540_;
}
else
{
if (v_isExample_512_ == 0)
{
lean_dec(v___f_511_);
goto v___jp_533_;
}
else
{
goto v___jp_540_;
}
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec(v___x_551_);
lean_dec(v_val_522_);
lean_dec(v___f_510_);
lean_dec(v_toBind_509_);
lean_dec_ref(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec(v_inst_506_);
lean_dec_ref(v_inst_505_);
lean_dec_ref(v_inst_503_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_apply_1(v___f_511_, v___x_553_);
return v___x_554_;
}
}
}
else
{
lean_object* v___x_555_; 
lean_dec(v___f_511_);
lean_dec(v___f_510_);
lean_dec_ref(v_inst_504_);
v___x_555_ = l_Lean_Syntax_getHeadInfo(v_val_522_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_556_; uint8_t v_isModule_557_; 
lean_dec_ref_known(v___x_555_, 4);
v___x_556_ = l_Lean_Environment_header(v_env_515_);
v_isModule_557_ = lean_ctor_get_uint8(v___x_556_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_556_);
if (v_isModule_557_ == 0)
{
lean_dec(v_val_522_);
lean_dec(v___f_514_);
lean_dec(v_toBind_509_);
lean_dec_ref(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec(v_inst_506_);
lean_dec_ref(v_inst_505_);
lean_dec_ref(v_inst_503_);
goto v___jp_516_;
}
else
{
uint8_t v_isExporting_558_; 
v_isExporting_558_ = lean_ctor_get_uint8(v_env_515_, sizeof(void*)*13);
if (v_isExporting_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v___f_513_);
v___x_559_ = l_Lean_linter_redundantVisibility;
v___x_560_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13);
v___x_561_ = l_Lean_Linter_logLintIf___redArg(v_inst_503_, v_inst_505_, v_inst_506_, v_inst_507_, v_inst_508_, v___x_559_, v_val_522_, v___x_560_);
v___x_562_ = lean_apply_4(v_toBind_509_, lean_box(0), lean_box(0), v___x_561_, v___f_514_);
return v___x_562_;
}
else
{
lean_dec(v_val_522_);
lean_dec(v___f_514_);
lean_dec(v_toBind_509_);
lean_dec_ref(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec(v_inst_506_);
lean_dec_ref(v_inst_505_);
lean_dec_ref(v_inst_503_);
goto v___jp_516_;
}
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v___x_555_);
lean_dec(v_val_522_);
lean_dec(v___f_514_);
lean_dec(v_toBind_509_);
lean_dec_ref(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec(v_inst_506_);
lean_dec_ref(v_inst_505_);
lean_dec_ref(v_inst_503_);
v___x_563_ = lean_box(0);
v___x_564_ = lean_apply_1(v___f_513_, v___x_563_);
return v___x_564_;
}
}
v___jp_523_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
lean_inc_ref(v___y_526_);
v___x_527_ = l_Lean_stringToMessageData(v___y_526_);
lean_inc_ref(v___y_525_);
v___x_528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_528_, 0, v___y_525_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
lean_inc_ref(v___y_524_);
v___x_531_ = l_Lean_Linter_logLintIf___redArg(v_inst_503_, v_inst_505_, v_inst_506_, v_inst_507_, v_inst_508_, v___y_524_, v_val_522_, v___x_530_);
v___x_532_ = lean_apply_4(v_toBind_509_, lean_box(0), lean_box(0), v___x_531_, v___f_510_);
return v___x_532_;
}
v___jp_533_:
{
lean_object* v___x_534_; uint8_t v_isModule_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_534_ = l_Lean_Environment_header(v_env_515_);
v_isModule_535_ = lean_ctor_get_uint8(v___x_534_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_534_);
v___x_536_ = l_Lean_linter_redundantVisibility;
v___x_537_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3);
if (v_isModule_535_ == 0)
{
lean_object* v___x_538_; 
v___x_538_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4));
v___y_524_ = v___x_536_;
v___y_525_ = v___x_537_;
v___y_526_ = v___x_538_;
goto v___jp_523_;
}
else
{
lean_object* v___x_539_; 
v___x_539_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__5));
v___y_524_ = v___x_536_;
v___y_525_ = v___x_537_;
v___y_526_ = v___x_539_;
goto v___jp_523_;
}
}
v___jp_540_:
{
lean_object* v___x_541_; uint8_t v_isModule_542_; 
v___x_541_ = l_Lean_Environment_header(v_env_515_);
v_isModule_542_ = lean_ctor_get_uint8(v___x_541_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_541_);
if (v_isModule_542_ == 0)
{
lean_dec(v___f_511_);
goto v___jp_533_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec(v_val_522_);
lean_dec(v___f_510_);
lean_dec(v_toBind_509_);
lean_dec_ref(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec(v_inst_506_);
lean_dec_ref(v_inst_505_);
lean_dec_ref(v_inst_503_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_apply_1(v___f_511_, v___x_543_);
return v___x_544_;
}
}
}
v___jp_516_:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_box(0);
v___x_518_ = lean_apply_1(v___f_513_, v___x_517_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___boxed(lean_object* v_vis_x3f_565_, lean_object* v_toPure_566_, lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_toBind_573_, lean_object* v___f_574_, lean_object* v___f_575_, lean_object* v_isExample_576_, lean_object* v___f_577_, lean_object* v___f_578_, lean_object* v_env_579_){
_start:
{
uint8_t v_isExample_boxed_580_; lean_object* v_res_581_; 
v_isExample_boxed_580_ = lean_unbox(v_isExample_576_);
v_res_581_ = l_Lean_Elab_elabVisibility___redArg___lam__3(v_vis_x3f_565_, v_toPure_566_, v_inst_567_, v_inst_568_, v_inst_569_, v_inst_570_, v_inst_571_, v_inst_572_, v_toBind_573_, v___f_574_, v___f_575_, v_isExample_boxed_580_, v___f_577_, v___f_578_, v_env_579_);
lean_dec_ref(v_env_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg(lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_vis_x3f_588_, uint8_t v_isExample_589_){
_start:
{
lean_object* v_toApplicative_590_; lean_object* v_toBind_591_; lean_object* v_getEnv_592_; lean_object* v_toPure_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___x_598_; lean_object* v___f_599_; lean_object* v___x_600_; 
v_toApplicative_590_ = lean_ctor_get(v_inst_582_, 0);
v_toBind_591_ = lean_ctor_get(v_inst_582_, 1);
lean_inc_n(v_toBind_591_, 2);
v_getEnv_592_ = lean_ctor_get(v_inst_584_, 0);
lean_inc(v_getEnv_592_);
v_toPure_593_ = lean_ctor_get(v_toApplicative_590_, 1);
lean_inc_n(v_toPure_593_, 3);
v___f_594_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__0), 2, 1);
lean_closure_set(v___f_594_, 0, v_toPure_593_);
lean_inc_ref(v___f_594_);
v___f_595_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_595_, 0, v___f_594_);
v___f_596_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__2), 2, 1);
lean_closure_set(v___f_596_, 0, v_toPure_593_);
lean_inc_ref(v___f_596_);
v___f_597_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_597_, 0, v___f_596_);
v___x_598_ = lean_box(v_isExample_589_);
v___f_599_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_599_, 0, v_vis_x3f_588_);
lean_closure_set(v___f_599_, 1, v_toPure_593_);
lean_closure_set(v___f_599_, 2, v_inst_582_);
lean_closure_set(v___f_599_, 3, v_inst_583_);
lean_closure_set(v___f_599_, 4, v_inst_586_);
lean_closure_set(v___f_599_, 5, v_inst_587_);
lean_closure_set(v___f_599_, 6, v_inst_585_);
lean_closure_set(v___f_599_, 7, v_inst_584_);
lean_closure_set(v___f_599_, 8, v_toBind_591_);
lean_closure_set(v___f_599_, 9, v___f_595_);
lean_closure_set(v___f_599_, 10, v___f_594_);
lean_closure_set(v___f_599_, 11, v___x_598_);
lean_closure_set(v___f_599_, 12, v___f_596_);
lean_closure_set(v___f_599_, 13, v___f_597_);
v___x_600_ = lean_apply_4(v_toBind_591_, lean_box(0), lean_box(0), v_getEnv_592_, v___f_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___boxed(lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_vis_x3f_607_, lean_object* v_isExample_608_){
_start:
{
uint8_t v_isExample_boxed_609_; lean_object* v_res_610_; 
v_isExample_boxed_609_ = lean_unbox(v_isExample_608_);
v_res_610_ = l_Lean_Elab_elabVisibility___redArg(v_inst_601_, v_inst_602_, v_inst_603_, v_inst_604_, v_inst_605_, v_inst_606_, v_vis_x3f_607_, v_isExample_boxed_609_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility(lean_object* v_m_611_, lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_vis_x3f_618_, uint8_t v_isExample_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_Elab_elabVisibility___redArg(v_inst_612_, v_inst_613_, v_inst_614_, v_inst_615_, v_inst_616_, v_inst_617_, v_vis_x3f_618_, v_isExample_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___boxed(lean_object* v_m_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_vis_x3f_628_, lean_object* v_isExample_629_){
_start:
{
uint8_t v_isExample_boxed_630_; lean_object* v_res_631_; 
v_isExample_boxed_630_ = lean_unbox(v_isExample_629_);
v_res_631_ = l_Lean_Elab_elabVisibility(v_m_621_, v_inst_622_, v_inst_623_, v_inst_624_, v_inst_625_, v_inst_626_, v_inst_627_, v_vis_x3f_628_, v_isExample_boxed_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___impl(uint8_t v_x_632_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_box(v_x_632_);
v___x_634_ = lean_obj_tag_nat(v___x_633_);
lean_dec(v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___impl___boxed(lean_object* v_x_635_){
_start:
{
uint8_t v_x_4__boxed_636_; lean_object* v_res_637_; 
v_x_4__boxed_636_ = lean_unbox(v_x_635_);
v_res_637_ = l_Lean_Elab_RecKind_ctorIdx___impl(v_x_4__boxed_636_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg(lean_object* v_k_638_){
_start:
{
lean_inc(v_k_638_);
return v_k_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg___boxed(lean_object* v_k_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Elab_RecKind_ctorElim___redArg(v_k_639_);
lean_dec(v_k_639_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim(lean_object* v_motive_641_, lean_object* v_ctorIdx_642_, uint8_t v_t_643_, lean_object* v_h_644_, lean_object* v_k_645_){
_start:
{
lean_inc(v_k_645_);
return v_k_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___boxed(lean_object* v_motive_646_, lean_object* v_ctorIdx_647_, lean_object* v_t_648_, lean_object* v_h_649_, lean_object* v_k_650_){
_start:
{
uint8_t v_t_boxed_651_; lean_object* v_res_652_; 
v_t_boxed_651_ = lean_unbox(v_t_648_);
v_res_652_ = l_Lean_Elab_RecKind_ctorElim(v_motive_646_, v_ctorIdx_647_, v_t_boxed_651_, v_h_649_, v_k_650_);
lean_dec(v_k_650_);
lean_dec(v_ctorIdx_647_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg(lean_object* v_partial_653_){
_start:
{
lean_inc(v_partial_653_);
return v_partial_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg___boxed(lean_object* v_partial_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_Elab_RecKind_partial_elim___redArg(v_partial_654_);
lean_dec(v_partial_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim(lean_object* v_motive_656_, uint8_t v_t_657_, lean_object* v_h_658_, lean_object* v_partial_659_){
_start:
{
lean_inc(v_partial_659_);
return v_partial_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___boxed(lean_object* v_motive_660_, lean_object* v_t_661_, lean_object* v_h_662_, lean_object* v_partial_663_){
_start:
{
uint8_t v_t_boxed_664_; lean_object* v_res_665_; 
v_t_boxed_664_ = lean_unbox(v_t_661_);
v_res_665_ = l_Lean_Elab_RecKind_partial_elim(v_motive_660_, v_t_boxed_664_, v_h_662_, v_partial_663_);
lean_dec(v_partial_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg(lean_object* v_nonrec_666_){
_start:
{
lean_inc(v_nonrec_666_);
return v_nonrec_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg___boxed(lean_object* v_nonrec_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Elab_RecKind_nonrec_elim___redArg(v_nonrec_667_);
lean_dec(v_nonrec_667_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim(lean_object* v_motive_669_, uint8_t v_t_670_, lean_object* v_h_671_, lean_object* v_nonrec_672_){
_start:
{
lean_inc(v_nonrec_672_);
return v_nonrec_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___boxed(lean_object* v_motive_673_, lean_object* v_t_674_, lean_object* v_h_675_, lean_object* v_nonrec_676_){
_start:
{
uint8_t v_t_boxed_677_; lean_object* v_res_678_; 
v_t_boxed_677_ = lean_unbox(v_t_674_);
v_res_678_ = l_Lean_Elab_RecKind_nonrec_elim(v_motive_673_, v_t_boxed_677_, v_h_675_, v_nonrec_676_);
lean_dec(v_nonrec_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg(lean_object* v_default_679_){
_start:
{
lean_inc(v_default_679_);
return v_default_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg___boxed(lean_object* v_default_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Elab_RecKind_default_elim___redArg(v_default_680_);
lean_dec(v_default_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim(lean_object* v_motive_682_, uint8_t v_t_683_, lean_object* v_h_684_, lean_object* v_default_685_){
_start:
{
lean_inc(v_default_685_);
return v_default_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___boxed(lean_object* v_motive_686_, lean_object* v_t_687_, lean_object* v_h_688_, lean_object* v_default_689_){
_start:
{
uint8_t v_t_boxed_690_; lean_object* v_res_691_; 
v_t_boxed_690_ = lean_unbox(v_t_687_);
v_res_691_ = l_Lean_Elab_RecKind_default_elim(v_motive_686_, v_t_boxed_690_, v_h_688_, v_default_689_);
lean_dec(v_default_689_);
return v_res_691_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind_default(void){
_start:
{
uint8_t v___x_692_; 
v___x_692_ = 0;
return v___x_692_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind(void){
_start:
{
uint8_t v___x_693_; 
v___x_693_ = 0;
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___impl(uint8_t v_x_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_box(v_x_694_);
v___x_696_ = lean_obj_tag_nat(v___x_695_);
lean_dec(v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___impl___boxed(lean_object* v_x_697_){
_start:
{
uint8_t v_x_4__boxed_698_; lean_object* v_res_699_; 
v_x_4__boxed_698_ = lean_unbox(v_x_697_);
v_res_699_ = l_Lean_Elab_ComputeKind_ctorIdx___impl(v_x_4__boxed_698_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg(lean_object* v_k_700_){
_start:
{
lean_inc(v_k_700_);
return v_k_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg___boxed(lean_object* v_k_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Elab_ComputeKind_ctorElim___redArg(v_k_701_);
lean_dec(v_k_701_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim(lean_object* v_motive_703_, lean_object* v_ctorIdx_704_, uint8_t v_t_705_, lean_object* v_h_706_, lean_object* v_k_707_){
_start:
{
lean_inc(v_k_707_);
return v_k_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___boxed(lean_object* v_motive_708_, lean_object* v_ctorIdx_709_, lean_object* v_t_710_, lean_object* v_h_711_, lean_object* v_k_712_){
_start:
{
uint8_t v_t_boxed_713_; lean_object* v_res_714_; 
v_t_boxed_713_ = lean_unbox(v_t_710_);
v_res_714_ = l_Lean_Elab_ComputeKind_ctorElim(v_motive_708_, v_ctorIdx_709_, v_t_boxed_713_, v_h_711_, v_k_712_);
lean_dec(v_k_712_);
lean_dec(v_ctorIdx_709_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg(lean_object* v_regular_715_){
_start:
{
lean_inc(v_regular_715_);
return v_regular_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg___boxed(lean_object* v_regular_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Elab_ComputeKind_regular_elim___redArg(v_regular_716_);
lean_dec(v_regular_716_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim(lean_object* v_motive_718_, uint8_t v_t_719_, lean_object* v_h_720_, lean_object* v_regular_721_){
_start:
{
lean_inc(v_regular_721_);
return v_regular_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___boxed(lean_object* v_motive_722_, lean_object* v_t_723_, lean_object* v_h_724_, lean_object* v_regular_725_){
_start:
{
uint8_t v_t_boxed_726_; lean_object* v_res_727_; 
v_t_boxed_726_ = lean_unbox(v_t_723_);
v_res_727_ = l_Lean_Elab_ComputeKind_regular_elim(v_motive_722_, v_t_boxed_726_, v_h_724_, v_regular_725_);
lean_dec(v_regular_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg(lean_object* v_meta_728_){
_start:
{
lean_inc(v_meta_728_);
return v_meta_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg___boxed(lean_object* v_meta_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Elab_ComputeKind_meta_elim___redArg(v_meta_729_);
lean_dec(v_meta_729_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim(lean_object* v_motive_731_, uint8_t v_t_732_, lean_object* v_h_733_, lean_object* v_meta_734_){
_start:
{
lean_inc(v_meta_734_);
return v_meta_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___boxed(lean_object* v_motive_735_, lean_object* v_t_736_, lean_object* v_h_737_, lean_object* v_meta_738_){
_start:
{
uint8_t v_t_boxed_739_; lean_object* v_res_740_; 
v_t_boxed_739_ = lean_unbox(v_t_736_);
v_res_740_ = l_Lean_Elab_ComputeKind_meta_elim(v_motive_735_, v_t_boxed_739_, v_h_737_, v_meta_738_);
lean_dec(v_meta_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(lean_object* v_noncomputable_741_){
_start:
{
lean_inc(v_noncomputable_741_);
return v_noncomputable_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg___boxed(lean_object* v_noncomputable_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(v_noncomputable_742_);
lean_dec(v_noncomputable_742_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim(lean_object* v_motive_744_, uint8_t v_t_745_, lean_object* v_h_746_, lean_object* v_noncomputable_747_){
_start:
{
lean_inc(v_noncomputable_747_);
return v_noncomputable_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___boxed(lean_object* v_motive_748_, lean_object* v_t_749_, lean_object* v_h_750_, lean_object* v_noncomputable_751_){
_start:
{
uint8_t v_t_boxed_752_; lean_object* v_res_753_; 
v_t_boxed_752_ = lean_unbox(v_t_749_);
v_res_753_ = l_Lean_Elab_ComputeKind_noncomputable_elim(v_motive_748_, v_t_boxed_752_, v_h_750_, v_noncomputable_751_);
lean_dec(v_noncomputable_751_);
return v_res_753_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind_default(void){
_start:
{
uint8_t v___x_754_; 
v___x_754_ = 0;
return v___x_754_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind(void){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = 0;
return v___x_755_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqComputeKind_beq(uint8_t v_x_756_, uint8_t v_y_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_758_ = lean_box(v_x_756_);
v___x_759_ = lean_obj_tag_nat(v___x_758_);
lean_dec(v___x_758_);
v___x_760_ = lean_box(v_y_757_);
v___x_761_ = lean_obj_tag_nat(v___x_760_);
lean_dec(v___x_760_);
v___x_762_ = lean_nat_dec_eq(v___x_759_, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqComputeKind_beq___boxed(lean_object* v_x_763_, lean_object* v_y_764_){
_start:
{
uint8_t v_x_24__boxed_765_; uint8_t v_y_25__boxed_766_; uint8_t v_res_767_; lean_object* v_r_768_; 
v_x_24__boxed_765_ = lean_unbox(v_x_763_);
v_y_25__boxed_766_ = lean_unbox(v_y_764_);
v_res_767_ = l_Lean_Elab_instBEqComputeKind_beq(v_x_24__boxed_765_, v_y_25__boxed_766_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
static lean_object* _init_l_Lean_Elab_instReprComputeKind_repr___closed__6(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_unsigned_to_nat(2u);
v___x_781_ = lean_nat_to_int(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_Elab_instReprComputeKind_repr___closed__7(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_unsigned_to_nat(1u);
v___x_783_ = lean_nat_to_int(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprComputeKind_repr(uint8_t v_x_784_, lean_object* v_prec_785_){
_start:
{
lean_object* v___y_787_; lean_object* v___y_794_; lean_object* v___y_801_; 
switch(v_x_784_)
{
case 0:
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = lean_unsigned_to_nat(1024u);
v___x_808_ = lean_nat_dec_le(v___x_807_, v_prec_785_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
v___x_809_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_787_ = v___x_809_;
goto v___jp_786_;
}
else
{
lean_object* v___x_810_; 
v___x_810_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_787_ = v___x_810_;
goto v___jp_786_;
}
}
case 1:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = lean_unsigned_to_nat(1024u);
v___x_812_ = lean_nat_dec_le(v___x_811_, v_prec_785_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
v___x_813_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_794_ = v___x_813_;
goto v___jp_793_;
}
else
{
lean_object* v___x_814_; 
v___x_814_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_794_ = v___x_814_;
goto v___jp_793_;
}
}
default: 
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = lean_unsigned_to_nat(1024u);
v___x_816_ = lean_nat_dec_le(v___x_815_, v_prec_785_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
v___x_817_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_801_ = v___x_817_;
goto v___jp_800_;
}
else
{
lean_object* v___x_818_; 
v___x_818_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_801_ = v___x_818_;
goto v___jp_800_;
}
}
}
v___jp_786_:
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_788_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__1));
lean_inc(v___y_787_);
v___x_789_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_789_, 0, v___y_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = 0;
v___x_791_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*1, v___x_790_);
v___x_792_ = l_Repr_addAppParen(v___x_791_, v_prec_785_);
return v___x_792_;
}
v___jp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_795_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__3));
lean_inc(v___y_794_);
v___x_796_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_796_, 0, v___y_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = 0;
v___x_798_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*1, v___x_797_);
v___x_799_ = l_Repr_addAppParen(v___x_798_, v_prec_785_);
return v___x_799_;
}
v___jp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_802_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__5));
lean_inc(v___y_801_);
v___x_803_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_803_, 0, v___y_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = 0;
v___x_805_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*1, v___x_804_);
v___x_806_ = l_Repr_addAppParen(v___x_805_, v_prec_785_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprComputeKind_repr___boxed(lean_object* v_x_819_, lean_object* v_prec_820_){
_start:
{
uint8_t v_x_171__boxed_821_; lean_object* v_res_822_; 
v_x_171__boxed_821_ = lean_unbox(v_x_819_);
v_res_822_ = l_Lean_Elab_instReprComputeKind_repr(v_x_171__boxed_821_, v_prec_820_);
lean_dec(v_prec_820_);
return v_res_822_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object* v_m_837_){
_start:
{
uint8_t v_visibility_838_; uint8_t v___x_839_; 
v_visibility_838_ = lean_ctor_get_uint8(v_m_837_, sizeof(void*)*3);
v___x_839_ = l_Lean_Elab_Visibility_isPrivate(v_visibility_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPrivate___boxed(lean_object* v_m_840_){
_start:
{
uint8_t v_res_841_; lean_object* v_r_842_; 
v_res_841_ = l_Lean_Elab_Modifiers_isPrivate(v_m_840_);
lean_dec_ref(v_m_840_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPublic(lean_object* v_m_843_){
_start:
{
uint8_t v_visibility_844_; uint8_t v___x_845_; 
v_visibility_844_ = lean_ctor_get_uint8(v_m_843_, sizeof(void*)*3);
v___x_845_ = l_Lean_Elab_Visibility_isPublic(v_visibility_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPublic___boxed(lean_object* v_m_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l_Lean_Elab_Modifiers_isPublic(v_m_846_);
lean_dec_ref(v_m_846_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isInferredPublic(lean_object* v_env_849_, lean_object* v_m_850_){
_start:
{
uint8_t v_visibility_851_; uint8_t v___x_852_; 
v_visibility_851_ = lean_ctor_get_uint8(v_m_850_, sizeof(void*)*3);
v___x_852_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_849_, v_visibility_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isInferredPublic___boxed(lean_object* v_env_853_, lean_object* v_m_854_){
_start:
{
uint8_t v_res_855_; lean_object* v_r_856_; 
v_res_855_ = l_Lean_Elab_Modifiers_isInferredPublic(v_env_853_, v_m_854_);
lean_dec_ref(v_m_854_);
lean_dec_ref(v_env_853_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object* v_x_857_){
_start:
{
uint8_t v_recKind_858_; 
v_recKind_858_ = lean_ctor_get_uint8(v_x_857_, sizeof(void*)*3 + 3);
if (v_recKind_858_ == 0)
{
uint8_t v___x_859_; 
v___x_859_ = 1;
return v___x_859_;
}
else
{
uint8_t v___x_860_; 
v___x_860_ = 0;
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPartial___boxed(lean_object* v_x_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l_Lean_Elab_Modifiers_isPartial(v_x_861_);
lean_dec_ref(v_x_861_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNonrec(lean_object* v_x_864_){
_start:
{
uint8_t v_recKind_865_; 
v_recKind_865_ = lean_ctor_get_uint8(v_x_864_, sizeof(void*)*3 + 3);
if (v_recKind_865_ == 1)
{
uint8_t v___x_866_; 
v___x_866_ = 1;
return v___x_866_;
}
else
{
uint8_t v___x_867_; 
v___x_867_ = 0;
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNonrec___boxed(lean_object* v_x_868_){
_start:
{
uint8_t v_res_869_; lean_object* v_r_870_; 
v_res_869_ = l_Lean_Elab_Modifiers_isNonrec(v_x_868_);
lean_dec_ref(v_x_868_);
v_r_870_ = lean_box(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isMeta(lean_object* v_m_871_){
_start:
{
uint8_t v_computeKind_872_; 
v_computeKind_872_ = lean_ctor_get_uint8(v_m_871_, sizeof(void*)*3 + 2);
if (v_computeKind_872_ == 1)
{
uint8_t v___x_873_; 
v___x_873_ = 1;
return v___x_873_;
}
else
{
uint8_t v___x_874_; 
v___x_874_ = 0;
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isMeta___boxed(lean_object* v_m_875_){
_start:
{
uint8_t v_res_876_; lean_object* v_r_877_; 
v_res_876_ = l_Lean_Elab_Modifiers_isMeta(v_m_875_);
lean_dec_ref(v_m_875_);
v_r_877_ = lean_box(v_res_876_);
return v_r_877_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNoncomputable(lean_object* v_m_878_){
_start:
{
uint8_t v_computeKind_879_; 
v_computeKind_879_ = lean_ctor_get_uint8(v_m_878_, sizeof(void*)*3 + 2);
if (v_computeKind_879_ == 2)
{
uint8_t v___x_880_; 
v___x_880_ = 1;
return v___x_880_;
}
else
{
uint8_t v___x_881_; 
v___x_881_ = 0;
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNoncomputable___boxed(lean_object* v_m_882_){
_start:
{
uint8_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = l_Lean_Elab_Modifiers_isNoncomputable(v_m_882_);
lean_dec_ref(v_m_882_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addAttr(lean_object* v_modifiers_885_, lean_object* v_attr_886_){
_start:
{
lean_object* v_stx_887_; lean_object* v_docString_x3f_888_; uint8_t v_visibility_889_; uint8_t v_isProtected_890_; uint8_t v_computeKind_891_; uint8_t v_recKind_892_; uint8_t v_isUnsafe_893_; lean_object* v_attrs_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_902_; 
v_stx_887_ = lean_ctor_get(v_modifiers_885_, 0);
v_docString_x3f_888_ = lean_ctor_get(v_modifiers_885_, 1);
v_visibility_889_ = lean_ctor_get_uint8(v_modifiers_885_, sizeof(void*)*3);
v_isProtected_890_ = lean_ctor_get_uint8(v_modifiers_885_, sizeof(void*)*3 + 1);
v_computeKind_891_ = lean_ctor_get_uint8(v_modifiers_885_, sizeof(void*)*3 + 2);
v_recKind_892_ = lean_ctor_get_uint8(v_modifiers_885_, sizeof(void*)*3 + 3);
v_isUnsafe_893_ = lean_ctor_get_uint8(v_modifiers_885_, sizeof(void*)*3 + 4);
v_attrs_894_ = lean_ctor_get(v_modifiers_885_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v_modifiers_885_);
if (v_isSharedCheck_902_ == 0)
{
v___x_896_ = v_modifiers_885_;
v_isShared_897_ = v_isSharedCheck_902_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_attrs_894_);
lean_inc(v_docString_x3f_888_);
lean_inc(v_stx_887_);
lean_dec(v_modifiers_885_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_902_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_array_push(v_attrs_894_, v_attr_886_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 2, v___x_898_);
v___x_900_ = v___x_896_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_stx_887_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_docString_x3f_888_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v___x_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*3, v_visibility_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*3 + 1, v_isProtected_890_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*3 + 2, v_computeKind_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*3 + 3, v_recKind_892_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*3 + 4, v_isUnsafe_893_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addFirstAttr(lean_object* v_modifiers_903_, lean_object* v_attr_904_){
_start:
{
lean_object* v_stx_905_; lean_object* v_docString_x3f_906_; uint8_t v_visibility_907_; uint8_t v_isProtected_908_; uint8_t v_computeKind_909_; uint8_t v_recKind_910_; uint8_t v_isUnsafe_911_; lean_object* v_attrs_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_923_; 
v_stx_905_ = lean_ctor_get(v_modifiers_903_, 0);
v_docString_x3f_906_ = lean_ctor_get(v_modifiers_903_, 1);
v_visibility_907_ = lean_ctor_get_uint8(v_modifiers_903_, sizeof(void*)*3);
v_isProtected_908_ = lean_ctor_get_uint8(v_modifiers_903_, sizeof(void*)*3 + 1);
v_computeKind_909_ = lean_ctor_get_uint8(v_modifiers_903_, sizeof(void*)*3 + 2);
v_recKind_910_ = lean_ctor_get_uint8(v_modifiers_903_, sizeof(void*)*3 + 3);
v_isUnsafe_911_ = lean_ctor_get_uint8(v_modifiers_903_, sizeof(void*)*3 + 4);
v_attrs_912_ = lean_ctor_get(v_modifiers_903_, 2);
v_isSharedCheck_923_ = !lean_is_exclusive(v_modifiers_903_);
if (v_isSharedCheck_923_ == 0)
{
v___x_914_ = v_modifiers_903_;
v_isShared_915_ = v_isSharedCheck_923_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_attrs_912_);
lean_inc(v_docString_x3f_906_);
lean_inc(v_stx_905_);
lean_dec(v_modifiers_903_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_923_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_mk_empty_array_with_capacity(v___x_916_);
v___x_918_ = lean_array_push(v___x_917_, v_attr_904_);
v___x_919_ = l_Array_append___redArg(v___x_918_, v_attrs_912_);
lean_dec_ref(v_attrs_912_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 2, v___x_919_);
v___x_921_ = v___x_914_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_stx_905_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_docString_x3f_906_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v___x_919_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3, v_visibility_907_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3 + 1, v_isProtected_908_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3 + 2, v_computeKind_909_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3 + 3, v_recKind_910_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3 + 4, v_isUnsafe_911_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(lean_object* v_p_924_, lean_object* v_as_925_, size_t v_i_926_, size_t v_stop_927_, lean_object* v_b_928_){
_start:
{
lean_object* v___y_930_; uint8_t v___x_934_; 
v___x_934_ = lean_usize_dec_eq(v_i_926_, v_stop_927_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_935_ = lean_array_uget_borrowed(v_as_925_, v_i_926_);
lean_inc_ref(v_p_924_);
lean_inc(v___x_935_);
v___x_936_ = lean_apply_1(v_p_924_, v___x_935_);
v___x_937_ = lean_unbox(v___x_936_);
if (v___x_937_ == 0)
{
v___y_930_ = v_b_928_;
goto v___jp_929_;
}
else
{
lean_object* v___x_938_; 
lean_inc(v___x_935_);
v___x_938_ = lean_array_push(v_b_928_, v___x_935_);
v___y_930_ = v___x_938_;
goto v___jp_929_;
}
}
else
{
lean_dec_ref(v_p_924_);
return v_b_928_;
}
v___jp_929_:
{
size_t v___x_931_; size_t v___x_932_; 
v___x_931_ = ((size_t)1ULL);
v___x_932_ = lean_usize_add(v_i_926_, v___x_931_);
v_i_926_ = v___x_932_;
v_b_928_ = v___y_930_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0___boxed(lean_object* v_p_939_, lean_object* v_as_940_, lean_object* v_i_941_, lean_object* v_stop_942_, lean_object* v_b_943_){
_start:
{
size_t v_i_boxed_944_; size_t v_stop_boxed_945_; lean_object* v_res_946_; 
v_i_boxed_944_ = lean_unbox_usize(v_i_941_);
lean_dec(v_i_941_);
v_stop_boxed_945_ = lean_unbox_usize(v_stop_942_);
lean_dec(v_stop_942_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_939_, v_as_940_, v_i_boxed_944_, v_stop_boxed_945_, v_b_943_);
lean_dec_ref(v_as_940_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object* v_modifiers_947_, lean_object* v_p_948_){
_start:
{
lean_object* v_stx_949_; lean_object* v_docString_x3f_950_; uint8_t v_visibility_951_; uint8_t v_isProtected_952_; uint8_t v_computeKind_953_; uint8_t v_recKind_954_; uint8_t v_isUnsafe_955_; lean_object* v_attrs_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_973_; 
v_stx_949_ = lean_ctor_get(v_modifiers_947_, 0);
v_docString_x3f_950_ = lean_ctor_get(v_modifiers_947_, 1);
v_visibility_951_ = lean_ctor_get_uint8(v_modifiers_947_, sizeof(void*)*3);
v_isProtected_952_ = lean_ctor_get_uint8(v_modifiers_947_, sizeof(void*)*3 + 1);
v_computeKind_953_ = lean_ctor_get_uint8(v_modifiers_947_, sizeof(void*)*3 + 2);
v_recKind_954_ = lean_ctor_get_uint8(v_modifiers_947_, sizeof(void*)*3 + 3);
v_isUnsafe_955_ = lean_ctor_get_uint8(v_modifiers_947_, sizeof(void*)*3 + 4);
v_attrs_956_ = lean_ctor_get(v_modifiers_947_, 2);
v_isSharedCheck_973_ = !lean_is_exclusive(v_modifiers_947_);
if (v_isSharedCheck_973_ == 0)
{
v___x_958_ = v_modifiers_947_;
v_isShared_959_ = v_isSharedCheck_973_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_attrs_956_);
lean_inc(v_docString_x3f_950_);
lean_inc(v_stx_949_);
lean_dec(v_modifiers_947_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_973_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = lean_array_get_size(v_attrs_956_);
v___x_962_ = ((lean_object*)(l_Lean_Elab_instInhabitedModifiers_default___closed__0));
v___x_963_ = lean_nat_dec_lt(v___x_960_, v___x_961_);
if (v___x_963_ == 0)
{
lean_object* v___x_965_; 
lean_dec_ref(v_attrs_956_);
lean_dec_ref(v_p_948_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 2, v___x_962_);
v___x_965_ = v___x_958_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_stx_949_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_docString_x3f_950_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v___x_962_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3, v_visibility_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3 + 1, v_isProtected_952_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3 + 2, v_computeKind_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3 + 3, v_recKind_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3 + 4, v_isUnsafe_955_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
else
{
size_t v___x_967_; size_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_967_ = ((size_t)0ULL);
v___x_968_ = lean_usize_of_nat(v___x_961_);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_948_, v_attrs_956_, v___x_967_, v___x_968_, v___x_962_);
lean_dec_ref(v_attrs_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 2, v___x_969_);
v___x_971_ = v___x_958_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_stx_949_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_docString_x3f_950_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v___x_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3, v_visibility_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 1, v_isProtected_952_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 2, v_computeKind_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 3, v_recKind_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 4, v_isUnsafe_955_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__1(lean_object* v___f_1118_, lean_object* v___f_1119_, lean_object* v_m_1120_){
_start:
{
lean_object* v_docString_x3f_1121_; uint8_t v_visibility_1122_; uint8_t v_isProtected_1123_; uint8_t v_computeKind_1124_; uint8_t v_recKind_1125_; uint8_t v_isUnsafe_1126_; lean_object* v_attrs_1127_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1173_; 
v_docString_x3f_1121_ = lean_ctor_get(v_m_1120_, 1);
lean_inc(v_docString_x3f_1121_);
v_visibility_1122_ = lean_ctor_get_uint8(v_m_1120_, sizeof(void*)*3);
v_isProtected_1123_ = lean_ctor_get_uint8(v_m_1120_, sizeof(void*)*3 + 1);
v_computeKind_1124_ = lean_ctor_get_uint8(v_m_1120_, sizeof(void*)*3 + 2);
v_recKind_1125_ = lean_ctor_get_uint8(v_m_1120_, sizeof(void*)*3 + 3);
v_isUnsafe_1126_ = lean_ctor_get_uint8(v_m_1120_, sizeof(void*)*3 + 4);
v_attrs_1127_ = lean_ctor_get(v_m_1120_, 2);
lean_inc_ref(v_attrs_1127_);
lean_dec_ref(v_m_1120_);
if (lean_obj_tag(v_docString_x3f_1121_) == 0)
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_box(0);
v___y_1173_ = v___x_1177_;
goto v___jp_1172_;
}
else
{
lean_object* v_val_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v_val_1178_ = lean_ctor_get(v_docString_x3f_1121_, 0);
lean_inc(v_val_1178_);
lean_dec_ref_known(v_docString_x3f_1121_, 1);
v___x_1179_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__32));
v___x_1180_ = lean_box(0);
v___x_1181_ = 0;
v___x_1182_ = l_Lean_Syntax_formatStx(v_val_1178_, v___x_1180_, v___x_1181_);
v___x_1183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1179_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__34));
v___x_1185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_box(0);
v___x_1187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___y_1173_ = v___x_1187_;
goto v___jp_1172_;
}
v___jp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v_components_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; 
lean_inc(v___y_1130_);
v___x_1131_ = l_List_appendTR___redArg(v___y_1129_, v___y_1130_);
v___x_1132_ = lean_array_to_list(v_attrs_1127_);
v___x_1133_ = lean_box(0);
v___x_1134_ = l_List_mapTR_loop___redArg(v___f_1118_, v___x_1132_, v___x_1133_);
v_components_1135_ = l_List_appendTR___redArg(v___x_1131_, v___x_1134_);
v___x_1136_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__3));
v___x_1137_ = l_Std_Format_joinSep___redArg(v___f_1119_, v_components_1135_, v___x_1136_);
v___x_1138_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__6, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__6_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6);
v___x_1139_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__7));
v___x_1140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v___x_1137_);
v___x_1141_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__8));
v___x_1142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1138_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = 0;
v___x_1145_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*1, v___x_1144_);
return v___x_1145_;
}
v___jp_1146_:
{
lean_object* v___x_1149_; 
lean_inc(v___y_1148_);
v___x_1149_ = l_List_appendTR___redArg(v___y_1147_, v___y_1148_);
if (v_isUnsafe_1126_ == 0)
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_box(0);
v___y_1129_ = v___x_1149_;
v___y_1130_ = v___x_1150_;
goto v___jp_1128_;
}
else
{
lean_object* v___x_1151_; 
v___x_1151_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__11));
v___y_1129_ = v___x_1149_;
v___y_1130_ = v___x_1151_;
goto v___jp_1128_;
}
}
v___jp_1152_:
{
lean_object* v___x_1155_; 
lean_inc(v___y_1154_);
v___x_1155_ = l_List_appendTR___redArg(v___y_1153_, v___y_1154_);
switch(v_recKind_1125_)
{
case 0:
{
lean_object* v___x_1156_; 
v___x_1156_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__14));
v___y_1147_ = v___x_1155_;
v___y_1148_ = v___x_1156_;
goto v___jp_1146_;
}
case 1:
{
lean_object* v___x_1157_; 
v___x_1157_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__17));
v___y_1147_ = v___x_1155_;
v___y_1148_ = v___x_1157_;
goto v___jp_1146_;
}
default: 
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_box(0);
v___y_1147_ = v___x_1155_;
v___y_1148_ = v___x_1158_;
goto v___jp_1146_;
}
}
}
v___jp_1159_:
{
lean_object* v___x_1162_; 
lean_inc(v___y_1161_);
v___x_1162_ = l_List_appendTR___redArg(v___y_1160_, v___y_1161_);
switch(v_computeKind_1124_)
{
case 0:
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_box(0);
v___y_1153_ = v___x_1162_;
v___y_1154_ = v___x_1163_;
goto v___jp_1152_;
}
case 1:
{
lean_object* v___x_1164_; 
v___x_1164_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__20));
v___y_1153_ = v___x_1162_;
v___y_1154_ = v___x_1164_;
goto v___jp_1152_;
}
default: 
{
lean_object* v___x_1165_; 
v___x_1165_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__23));
v___y_1153_ = v___x_1162_;
v___y_1154_ = v___x_1165_;
goto v___jp_1152_;
}
}
}
v___jp_1166_:
{
lean_object* v___x_1169_; 
lean_inc(v___y_1168_);
v___x_1169_ = l_List_appendTR___redArg(v___y_1167_, v___y_1168_);
if (v_isProtected_1123_ == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_box(0);
v___y_1160_ = v___x_1169_;
v___y_1161_ = v___x_1170_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1171_; 
v___x_1171_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__26));
v___y_1160_ = v___x_1169_;
v___y_1161_ = v___x_1171_;
goto v___jp_1159_;
}
}
v___jp_1172_:
{
switch(v_visibility_1122_)
{
case 0:
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_box(0);
v___y_1167_ = v___y_1173_;
v___y_1168_ = v___x_1174_;
goto v___jp_1166_;
}
case 1:
{
lean_object* v___x_1175_; 
v___x_1175_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__28));
v___y_1167_ = v___y_1173_;
v___y_1168_ = v___x_1175_;
goto v___jp_1166_;
}
default: 
{
lean_object* v___x_1176_; 
v___x_1176_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__30));
v___y_1167_ = v___y_1173_;
v___y_1168_ = v___x_1176_;
goto v___jp_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lam__0(lean_object* v_f_1194_){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = l_Std_Format_defWidth;
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = l_Std_Format_pretty(v_f_1194_, v___x_1195_, v___x_1196_, v___x_1196_);
return v___x_1197_;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = ((lean_object*)(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0));
v___x_1205_ = l_Lean_stringToMessageData(v___x_1204_);
return v___x_1205_;
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
lean_object* v_val_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1257_; 
v_val_1215_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1217_ = v___x_1212_;
v_isShared_1218_ = v_isSharedCheck_1257_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_val_1215_);
lean_dec(v___x_1212_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1257_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_unsigned_to_nat(1u);
v___x_1228_ = l_Lean_Syntax_getArg(v_val_1215_, v___x_1227_);
if (lean_obj_tag(v___x_1228_) == 1)
{
lean_object* v_kind_1229_; 
v_kind_1229_ = lean_ctor_get(v___x_1228_, 1);
lean_inc(v_kind_1229_);
if (lean_obj_tag(v_kind_1229_) == 1)
{
lean_object* v_pre_1230_; 
v_pre_1230_ = lean_ctor_get(v_kind_1229_, 0);
lean_inc(v_pre_1230_);
if (lean_obj_tag(v_pre_1230_) == 1)
{
lean_object* v_pre_1231_; 
v_pre_1231_ = lean_ctor_get(v_pre_1230_, 0);
lean_inc(v_pre_1231_);
if (lean_obj_tag(v_pre_1231_) == 1)
{
lean_object* v_pre_1232_; 
v_pre_1232_ = lean_ctor_get(v_pre_1231_, 0);
lean_inc(v_pre_1232_);
if (lean_obj_tag(v_pre_1232_) == 1)
{
lean_object* v_pre_1233_; 
v_pre_1233_ = lean_ctor_get(v_pre_1232_, 0);
if (lean_obj_tag(v_pre_1233_) == 0)
{
lean_object* v_args_1234_; lean_object* v_str_1235_; lean_object* v_str_1236_; lean_object* v_str_1237_; lean_object* v_str_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v_args_1234_ = lean_ctor_get(v___x_1228_, 2);
lean_inc_ref(v_args_1234_);
lean_dec_ref_known(v___x_1228_, 3);
v_str_1235_ = lean_ctor_get(v_kind_1229_, 1);
lean_inc_ref(v_str_1235_);
lean_dec_ref_known(v_kind_1229_, 2);
v_str_1236_ = lean_ctor_get(v_pre_1230_, 1);
lean_inc_ref(v_str_1236_);
lean_dec_ref_known(v_pre_1230_, 2);
v_str_1237_ = lean_ctor_get(v_pre_1231_, 1);
lean_inc_ref(v_str_1237_);
lean_dec_ref_known(v_pre_1231_, 2);
v_str_1238_ = lean_ctor_get(v_pre_1232_, 1);
lean_inc_ref(v_str_1238_);
lean_dec_ref_known(v_pre_1232_, 2);
v___x_1239_ = ((lean_object*)(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_));
v___x_1240_ = lean_string_dec_eq(v_str_1238_, v___x_1239_);
lean_dec_ref(v_str_1238_);
if (v___x_1240_ == 0)
{
lean_dec_ref(v_str_1237_);
lean_dec_ref(v_str_1236_);
lean_dec_ref(v_str_1235_);
lean_dec_ref(v_args_1234_);
lean_del_object(v___x_1217_);
goto v___jp_1219_;
}
else
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6));
v___x_1242_ = lean_string_dec_eq(v_str_1237_, v___x_1241_);
lean_dec_ref(v_str_1237_);
if (v___x_1242_ == 0)
{
lean_dec_ref(v_str_1236_);
lean_dec_ref(v_str_1235_);
lean_dec_ref(v_args_1234_);
lean_del_object(v___x_1217_);
goto v___jp_1219_;
}
else
{
lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7));
v___x_1244_ = lean_string_dec_eq(v_str_1236_, v___x_1243_);
lean_dec_ref(v_str_1236_);
if (v___x_1244_ == 0)
{
lean_dec_ref(v_str_1235_);
lean_dec_ref(v_args_1234_);
lean_del_object(v___x_1217_);
goto v___jp_1219_;
}
else
{
lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = ((lean_object*)(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__2));
v___x_1246_ = lean_string_dec_eq(v_str_1235_, v___x_1245_);
lean_dec_ref(v_str_1235_);
if (v___x_1246_ == 0)
{
lean_dec_ref(v_args_1234_);
lean_del_object(v___x_1217_);
goto v___jp_1219_;
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1247_ = lean_array_get_size(v_args_1234_);
v___x_1248_ = lean_unsigned_to_nat(2u);
v___x_1249_ = lean_nat_dec_eq(v___x_1247_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_dec_ref(v_args_1234_);
lean_del_object(v___x_1217_);
goto v___jp_1219_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_array_fget(v_args_1234_, v___x_1250_);
lean_dec_ref(v_args_1234_);
if (lean_obj_tag(v___x_1251_) == 2)
{
lean_object* v_val_1252_; lean_object* v___x_1254_; 
lean_inc(v_toPure_1211_);
lean_dec(v_val_1215_);
lean_dec_ref(v_inst_1208_);
lean_dec_ref(v_inst_1207_);
v_val_1252_ = lean_ctor_get(v___x_1251_, 1);
lean_inc_ref(v_val_1252_);
lean_dec_ref_known(v___x_1251_, 2);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v_val_1252_);
v___x_1254_ = v___x_1217_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_val_1252_);
v___x_1254_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_apply_2(v_toPure_1211_, lean_box(0), v___x_1254_);
return v___x_1255_;
}
}
else
{
lean_dec(v___x_1251_);
lean_del_object(v___x_1217_);
goto v___jp_1219_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1232_, 2);
lean_dec_ref_known(v_pre_1231_, 2);
lean_dec_ref_known(v_pre_1230_, 2);
lean_dec_ref_known(v_kind_1229_, 2);
lean_dec_ref_known(v___x_1228_, 3);
lean_del_object(v___x_1217_);
goto v___jp_1219_;
}
}
else
{
lean_dec(v_pre_1232_);
lean_dec_ref_known(v_pre_1231_, 2);
lean_dec_ref_known(v_pre_1230_, 2);
lean_dec_ref_known(v_kind_1229_, 2);
lean_dec_ref_known(v___x_1228_, 3);
lean_del_object(v___x_1217_);
goto v___jp_1219_;
}
}
else
{
lean_dec_ref_known(v_pre_1230_, 2);
lean_dec(v_pre_1231_);
lean_dec_ref_known(v_kind_1229_, 2);
lean_dec_ref_known(v___x_1228_, 3);
lean_del_object(v___x_1217_);
goto v___jp_1219_;
}
}
else
{
lean_dec_ref_known(v_kind_1229_, 2);
lean_dec(v_pre_1230_);
lean_dec_ref_known(v___x_1228_, 3);
lean_del_object(v___x_1217_);
goto v___jp_1219_;
}
}
else
{
lean_dec_ref_known(v___x_1228_, 3);
lean_dec(v_kind_1229_);
lean_del_object(v___x_1217_);
goto v___jp_1219_;
}
}
else
{
lean_dec(v___x_1228_);
lean_del_object(v___x_1217_);
goto v___jp_1219_;
}
v___jp_1219_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1220_ = lean_obj_once(&l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1, &l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1_once, _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1);
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = l_Lean_Syntax_getArg(v_val_1215_, v___x_1221_);
v___x_1223_ = l_Lean_MessageData_ofSyntax(v___x_1222_);
v___x_1224_ = l_Lean_indentD(v___x_1223_);
v___x_1225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1220_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = l_Lean_throwErrorAt___redArg(v_inst_1207_, v_inst_1208_, v_val_1215_, v___x_1225_);
return v___x_1226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___boxed(lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_optDocComment_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1258_, v_inst_1259_, v_optDocComment_1260_);
lean_dec(v_optDocComment_1260_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f(lean_object* v_m_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_optDocComment_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1263_, v_inst_1264_, v_optDocComment_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___boxed(lean_object* v_m_1267_, lean_object* v_inst_1268_, lean_object* v_inst_1269_, lean_object* v_optDocComment_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Elab_expandOptDocComment_x3f(v_m_1267_, v_inst_1268_, v_inst_1269_, v_optDocComment_1270_);
lean_dec(v_optDocComment_1270_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0(lean_object* v_stx_1272_, lean_object* v___y_1273_, uint8_t v_visibility_1274_, uint8_t v___y_1275_, uint8_t v___y_1276_, uint8_t v___y_1277_, lean_object* v_toPure_1278_, lean_object* v_unsafeStx_1279_, lean_object* v_attrs_1280_){
_start:
{
uint8_t v___y_1282_; uint8_t v___x_1285_; 
v___x_1285_ = l_Lean_Syntax_isNone(v_unsafeStx_1279_);
if (v___x_1285_ == 0)
{
uint8_t v___x_1286_; 
v___x_1286_ = 1;
v___y_1282_ = v___x_1286_;
goto v___jp_1281_;
}
else
{
uint8_t v___x_1287_; 
v___x_1287_ = 0;
v___y_1282_ = v___x_1287_;
goto v___jp_1281_;
}
v___jp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1283_, 0, v_stx_1272_);
lean_ctor_set(v___x_1283_, 1, v___y_1273_);
lean_ctor_set(v___x_1283_, 2, v_attrs_1280_);
lean_ctor_set_uint8(v___x_1283_, sizeof(void*)*3, v_visibility_1274_);
lean_ctor_set_uint8(v___x_1283_, sizeof(void*)*3 + 1, v___y_1275_);
lean_ctor_set_uint8(v___x_1283_, sizeof(void*)*3 + 2, v___y_1276_);
lean_ctor_set_uint8(v___x_1283_, sizeof(void*)*3 + 3, v___y_1277_);
lean_ctor_set_uint8(v___x_1283_, sizeof(void*)*3 + 4, v___y_1282_);
v___x_1284_ = lean_apply_2(v_toPure_1278_, lean_box(0), v___x_1283_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0___boxed(lean_object* v_stx_1288_, lean_object* v___y_1289_, lean_object* v_visibility_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v_toPure_1294_, lean_object* v_unsafeStx_1295_, lean_object* v_attrs_1296_){
_start:
{
uint8_t v_visibility_boxed_1297_; uint8_t v___y_305__boxed_1298_; uint8_t v___y_306__boxed_1299_; uint8_t v___y_307__boxed_1300_; lean_object* v_res_1301_; 
v_visibility_boxed_1297_ = lean_unbox(v_visibility_1290_);
v___y_305__boxed_1298_ = lean_unbox(v___y_1291_);
v___y_306__boxed_1299_ = lean_unbox(v___y_1292_);
v___y_307__boxed_1300_ = lean_unbox(v___y_1293_);
v_res_1301_ = l_Lean_Elab_elabModifiers___redArg___lam__0(v_stx_1288_, v___y_1289_, v_visibility_boxed_1297_, v___y_305__boxed_1298_, v___y_306__boxed_1299_, v___y_307__boxed_1300_, v_toPure_1294_, v_unsafeStx_1295_, v_attrs_1296_);
lean_dec(v_unsafeStx_1295_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__1(lean_object* v___f_1302_, lean_object* v_attrs_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_apply_1(v___f_1302_, v_attrs_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3(lean_object* v_stx_1305_, lean_object* v___y_1306_, uint8_t v___y_1307_, uint8_t v___y_1308_, lean_object* v_toPure_1309_, lean_object* v_unsafeStx_1310_, lean_object* v_attrsStx_1311_, lean_object* v___x_1312_, lean_object* v_toBind_1313_, lean_object* v_inst_1314_, lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_protectedStx_1326_, uint8_t v_visibility_1327_){
_start:
{
uint8_t v___y_1329_; uint8_t v___x_1344_; 
v___x_1344_ = l_Lean_Syntax_isNone(v_protectedStx_1326_);
if (v___x_1344_ == 0)
{
uint8_t v___x_1345_; 
v___x_1345_ = 1;
v___y_1329_ = v___x_1345_;
goto v___jp_1328_;
}
else
{
uint8_t v___x_1346_; 
v___x_1346_ = 0;
v___y_1329_ = v___x_1346_;
goto v___jp_1328_;
}
v___jp_1328_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___f_1334_; lean_object* v___x_1335_; 
v___x_1330_ = lean_box(v_visibility_1327_);
v___x_1331_ = lean_box(v___y_1329_);
v___x_1332_ = lean_box(v___y_1307_);
v___x_1333_ = lean_box(v___y_1308_);
lean_inc(v_toPure_1309_);
v___f_1334_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_1334_, 0, v_stx_1305_);
lean_closure_set(v___f_1334_, 1, v___y_1306_);
lean_closure_set(v___f_1334_, 2, v___x_1330_);
lean_closure_set(v___f_1334_, 3, v___x_1331_);
lean_closure_set(v___f_1334_, 4, v___x_1332_);
lean_closure_set(v___f_1334_, 5, v___x_1333_);
lean_closure_set(v___f_1334_, 6, v_toPure_1309_);
lean_closure_set(v___f_1334_, 7, v_unsafeStx_1310_);
v___x_1335_ = l_Lean_Syntax_getOptional_x3f(v_attrsStx_1311_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v___f_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec(v_inst_1325_);
lean_dec(v_inst_1324_);
lean_dec_ref(v_inst_1323_);
lean_dec(v_inst_1322_);
lean_dec_ref(v_inst_1321_);
lean_dec_ref(v_inst_1320_);
lean_dec_ref(v_inst_1319_);
lean_dec_ref(v_inst_1318_);
lean_dec_ref(v_inst_1317_);
lean_dec_ref(v_inst_1316_);
lean_dec_ref(v_inst_1315_);
lean_dec_ref(v_inst_1314_);
v___f_1336_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1336_, 0, v___f_1334_);
v___x_1337_ = lean_mk_empty_array_with_capacity(v___x_1312_);
v___x_1338_ = lean_apply_2(v_toPure_1309_, lean_box(0), v___x_1337_);
v___x_1339_ = lean_apply_4(v_toBind_1313_, lean_box(0), lean_box(0), v___x_1338_, v___f_1336_);
return v___x_1339_;
}
else
{
lean_object* v_val_1340_; lean_object* v___f_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec(v_toPure_1309_);
v_val_1340_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_val_1340_);
lean_dec_ref_known(v___x_1335_, 1);
v___f_1341_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1341_, 0, v___f_1334_);
v___x_1342_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_1314_, v_inst_1315_, v_inst_1316_, v_inst_1317_, v_inst_1318_, v_inst_1319_, v_inst_1320_, v_inst_1321_, v_inst_1322_, v_inst_1323_, v_inst_1324_, v_inst_1325_, v_val_1340_);
lean_dec(v_val_1340_);
v___x_1343_ = lean_apply_4(v_toBind_1313_, lean_box(0), lean_box(0), v___x_1342_, v___f_1341_);
return v___x_1343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_stx_1347_ = _args[0];
lean_object* v___y_1348_ = _args[1];
lean_object* v___y_1349_ = _args[2];
lean_object* v___y_1350_ = _args[3];
lean_object* v_toPure_1351_ = _args[4];
lean_object* v_unsafeStx_1352_ = _args[5];
lean_object* v_attrsStx_1353_ = _args[6];
lean_object* v___x_1354_ = _args[7];
lean_object* v_toBind_1355_ = _args[8];
lean_object* v_inst_1356_ = _args[9];
lean_object* v_inst_1357_ = _args[10];
lean_object* v_inst_1358_ = _args[11];
lean_object* v_inst_1359_ = _args[12];
lean_object* v_inst_1360_ = _args[13];
lean_object* v_inst_1361_ = _args[14];
lean_object* v_inst_1362_ = _args[15];
lean_object* v_inst_1363_ = _args[16];
lean_object* v_inst_1364_ = _args[17];
lean_object* v_inst_1365_ = _args[18];
lean_object* v_inst_1366_ = _args[19];
lean_object* v_inst_1367_ = _args[20];
lean_object* v_protectedStx_1368_ = _args[21];
lean_object* v_visibility_1369_ = _args[22];
_start:
{
uint8_t v___y_335__boxed_1370_; uint8_t v___y_336__boxed_1371_; uint8_t v_visibility_boxed_1372_; lean_object* v_res_1373_; 
v___y_335__boxed_1370_ = lean_unbox(v___y_1349_);
v___y_336__boxed_1371_ = lean_unbox(v___y_1350_);
v_visibility_boxed_1372_ = lean_unbox(v_visibility_1369_);
v_res_1373_ = l_Lean_Elab_elabModifiers___redArg___lam__3(v_stx_1347_, v___y_1348_, v___y_335__boxed_1370_, v___y_336__boxed_1371_, v_toPure_1351_, v_unsafeStx_1352_, v_attrsStx_1353_, v___x_1354_, v_toBind_1355_, v_inst_1356_, v_inst_1357_, v_inst_1358_, v_inst_1359_, v_inst_1360_, v_inst_1361_, v_inst_1362_, v_inst_1363_, v_inst_1364_, v_inst_1365_, v_inst_1366_, v_inst_1367_, v_protectedStx_1368_, v_visibility_boxed_1372_);
lean_dec(v_protectedStx_1368_);
lean_dec(v___x_1354_);
lean_dec(v_attrsStx_1353_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg(lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_inst_1386_, lean_object* v_inst_1387_, lean_object* v_inst_1388_, lean_object* v_inst_1389_, lean_object* v_inst_1390_, lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_inst_1395_, lean_object* v_stx_1396_, uint8_t v_isExample_1397_){
_start:
{
lean_object* v_toApplicative_1398_; lean_object* v_toBind_1399_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v_toPure_1405_; lean_object* v___x_1406_; lean_object* v_docCommentStx_1407_; lean_object* v___x_1408_; lean_object* v_attrsStx_1409_; lean_object* v___x_1410_; lean_object* v_visibilityStx_1411_; lean_object* v___x_1412_; lean_object* v_protectedStx_1413_; uint8_t v___y_1415_; lean_object* v___y_1416_; uint8_t v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1433_; uint8_t v___y_1434_; uint8_t v___y_1435_; uint8_t v___y_1447_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v_toApplicative_1398_ = lean_ctor_get(v_inst_1384_, 0);
v_toBind_1399_ = lean_ctor_get(v_inst_1384_, 1);
lean_inc(v_toBind_1399_);
v_toPure_1405_ = lean_ctor_get(v_toApplicative_1398_, 1);
v___x_1406_ = lean_unsigned_to_nat(0u);
v_docCommentStx_1407_ = l_Lean_Syntax_getArg(v_stx_1396_, v___x_1406_);
v___x_1408_ = lean_unsigned_to_nat(1u);
v_attrsStx_1409_ = l_Lean_Syntax_getArg(v_stx_1396_, v___x_1408_);
v___x_1410_ = lean_unsigned_to_nat(2u);
v_visibilityStx_1411_ = l_Lean_Syntax_getArg(v_stx_1396_, v___x_1410_);
v___x_1412_ = lean_unsigned_to_nat(3u);
v_protectedStx_1413_ = l_Lean_Syntax_getArg(v_stx_1396_, v___x_1412_);
v___x_1460_ = lean_unsigned_to_nat(4u);
v___x_1461_ = l_Lean_Syntax_getArg(v_stx_1396_, v___x_1460_);
v___x_1462_ = l_Lean_Syntax_isNone(v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1463_ = l_Lean_Syntax_getArg(v___x_1461_, v___x_1406_);
lean_dec(v___x_1461_);
v___x_1464_ = l_Lean_Syntax_getKind(v___x_1463_);
v___x_1465_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__1));
v___x_1466_ = lean_name_eq(v___x_1464_, v___x_1465_);
lean_dec(v___x_1464_);
if (v___x_1466_ == 0)
{
uint8_t v___x_1467_; 
v___x_1467_ = 2;
v___y_1447_ = v___x_1467_;
goto v___jp_1446_;
}
else
{
uint8_t v___x_1468_; 
v___x_1468_ = 1;
v___y_1447_ = v___x_1468_;
goto v___jp_1446_;
}
}
else
{
uint8_t v___x_1469_; 
lean_dec(v___x_1461_);
v___x_1469_ = 0;
v___y_1447_ = v___x_1469_;
goto v___jp_1446_;
}
v___jp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = l_Lean_Elab_elabVisibility___redArg(v_inst_1384_, v_inst_1387_, v_inst_1385_, v_inst_1392_, v_inst_1394_, v_inst_1393_, v___y_1402_, v_isExample_1397_);
v___x_1404_ = lean_apply_4(v_toBind_1399_, lean_box(0), lean_box(0), v___x_1403_, v___y_1401_);
return v___x_1404_;
}
v___jp_1414_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___f_1421_; lean_object* v___x_1422_; 
v___x_1419_ = lean_box(v___y_1417_);
v___x_1420_ = lean_box(v___y_1415_);
lean_inc_ref(v_inst_1394_);
lean_inc(v_inst_1393_);
lean_inc_ref(v_inst_1392_);
lean_inc_ref(v_inst_1387_);
lean_inc_ref(v_inst_1385_);
lean_inc_ref(v_inst_1384_);
lean_inc(v_toBind_1399_);
lean_inc(v_toPure_1405_);
v___f_1421_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__3___boxed), 23, 22);
lean_closure_set(v___f_1421_, 0, v_stx_1396_);
lean_closure_set(v___f_1421_, 1, v___y_1418_);
lean_closure_set(v___f_1421_, 2, v___x_1419_);
lean_closure_set(v___f_1421_, 3, v___x_1420_);
lean_closure_set(v___f_1421_, 4, v_toPure_1405_);
lean_closure_set(v___f_1421_, 5, v___y_1416_);
lean_closure_set(v___f_1421_, 6, v_attrsStx_1409_);
lean_closure_set(v___f_1421_, 7, v___x_1406_);
lean_closure_set(v___f_1421_, 8, v_toBind_1399_);
lean_closure_set(v___f_1421_, 9, v_inst_1384_);
lean_closure_set(v___f_1421_, 10, v_inst_1385_);
lean_closure_set(v___f_1421_, 11, v_inst_1386_);
lean_closure_set(v___f_1421_, 12, v_inst_1387_);
lean_closure_set(v___f_1421_, 13, v_inst_1389_);
lean_closure_set(v___f_1421_, 14, v_inst_1390_);
lean_closure_set(v___f_1421_, 15, v_inst_1391_);
lean_closure_set(v___f_1421_, 16, v_inst_1392_);
lean_closure_set(v___f_1421_, 17, v_inst_1393_);
lean_closure_set(v___f_1421_, 18, v_inst_1394_);
lean_closure_set(v___f_1421_, 19, v_inst_1395_);
lean_closure_set(v___f_1421_, 20, v_inst_1388_);
lean_closure_set(v___f_1421_, 21, v_protectedStx_1413_);
v___x_1422_ = l_Lean_Syntax_getOptional_x3f(v_visibilityStx_1411_);
lean_dec(v_visibilityStx_1411_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_box(0);
v___y_1401_ = v___f_1421_;
v___y_1402_ = v___x_1423_;
goto v___jp_1400_;
}
else
{
lean_object* v_val_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
v_val_1424_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1422_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_val_1424_);
lean_dec(v___x_1422_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_val_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
v___y_1401_ = v___f_1421_;
v___y_1402_ = v___x_1429_;
goto v___jp_1400_;
}
}
}
}
v___jp_1432_:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_Syntax_getOptional_x3f(v_docCommentStx_1407_);
lean_dec(v_docCommentStx_1407_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_box(0);
v___y_1415_ = v___y_1435_;
v___y_1416_ = v___y_1433_;
v___y_1417_ = v___y_1434_;
v___y_1418_ = v___x_1437_;
goto v___jp_1414_;
}
else
{
lean_object* v_val_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
v_val_1438_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1436_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_val_1438_);
lean_dec(v___x_1436_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_val_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
v___y_1415_ = v___y_1435_;
v___y_1416_ = v___y_1433_;
v___y_1417_ = v___y_1434_;
v___y_1418_ = v___x_1443_;
goto v___jp_1414_;
}
}
}
}
v___jp_1446_:
{
lean_object* v___x_1448_; lean_object* v_unsafeStx_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1448_ = lean_unsigned_to_nat(5u);
v_unsafeStx_1449_ = l_Lean_Syntax_getArg(v_stx_1396_, v___x_1448_);
v___x_1450_ = lean_unsigned_to_nat(6u);
v___x_1451_ = l_Lean_Syntax_getArg(v_stx_1396_, v___x_1450_);
v___x_1452_ = l_Lean_Syntax_isNone(v___x_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1453_ = l_Lean_Syntax_getArg(v___x_1451_, v___x_1406_);
lean_dec(v___x_1451_);
v___x_1454_ = l_Lean_Syntax_getKind(v___x_1453_);
v___x_1455_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__0));
v___x_1456_ = lean_name_eq(v___x_1454_, v___x_1455_);
lean_dec(v___x_1454_);
if (v___x_1456_ == 0)
{
uint8_t v___x_1457_; 
v___x_1457_ = 1;
v___y_1433_ = v_unsafeStx_1449_;
v___y_1434_ = v___y_1447_;
v___y_1435_ = v___x_1457_;
goto v___jp_1432_;
}
else
{
uint8_t v___x_1458_; 
v___x_1458_ = 0;
v___y_1433_ = v_unsafeStx_1449_;
v___y_1434_ = v___y_1447_;
v___y_1435_ = v___x_1458_;
goto v___jp_1432_;
}
}
else
{
uint8_t v___x_1459_; 
lean_dec(v___x_1451_);
v___x_1459_ = 2;
v___y_1433_ = v_unsafeStx_1449_;
v___y_1434_ = v___y_1447_;
v___y_1435_ = v___x_1459_;
goto v___jp_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___boxed(lean_object* v_inst_1470_, lean_object* v_inst_1471_, lean_object* v_inst_1472_, lean_object* v_inst_1473_, lean_object* v_inst_1474_, lean_object* v_inst_1475_, lean_object* v_inst_1476_, lean_object* v_inst_1477_, lean_object* v_inst_1478_, lean_object* v_inst_1479_, lean_object* v_inst_1480_, lean_object* v_inst_1481_, lean_object* v_stx_1482_, lean_object* v_isExample_1483_){
_start:
{
uint8_t v_isExample_boxed_1484_; lean_object* v_res_1485_; 
v_isExample_boxed_1484_ = lean_unbox(v_isExample_1483_);
v_res_1485_ = l_Lean_Elab_elabModifiers___redArg(v_inst_1470_, v_inst_1471_, v_inst_1472_, v_inst_1473_, v_inst_1474_, v_inst_1475_, v_inst_1476_, v_inst_1477_, v_inst_1478_, v_inst_1479_, v_inst_1480_, v_inst_1481_, v_stx_1482_, v_isExample_boxed_1484_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object* v_m_1486_, lean_object* v_inst_1487_, lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_inst_1490_, lean_object* v_inst_1491_, lean_object* v_inst_1492_, lean_object* v_inst_1493_, lean_object* v_inst_1494_, lean_object* v_inst_1495_, lean_object* v_inst_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_stx_1499_, uint8_t v_isExample_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_Elab_elabModifiers___redArg(v_inst_1487_, v_inst_1488_, v_inst_1489_, v_inst_1490_, v_inst_1491_, v_inst_1492_, v_inst_1493_, v_inst_1494_, v_inst_1495_, v_inst_1496_, v_inst_1497_, v_inst_1498_, v_stx_1499_, v_isExample_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___boxed(lean_object* v_m_1502_, lean_object* v_inst_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_inst_1513_, lean_object* v_inst_1514_, lean_object* v_stx_1515_, lean_object* v_isExample_1516_){
_start:
{
uint8_t v_isExample_boxed_1517_; lean_object* v_res_1518_; 
v_isExample_boxed_1517_ = lean_unbox(v_isExample_1516_);
v_res_1518_ = l_Lean_Elab_elabModifiers(v_m_1502_, v_inst_1503_, v_inst_1504_, v_inst_1505_, v_inst_1506_, v_inst_1507_, v_inst_1508_, v_inst_1509_, v_inst_1510_, v_inst_1511_, v_inst_1512_, v_inst_1513_, v_inst_1514_, v_stx_1515_, v_isExample_boxed_1517_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__0(lean_object* v_toPure_1519_, lean_object* v_declName_1520_, lean_object* v_____r_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_apply_2(v_toPure_1519_, lean_box(0), v_declName_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__1(lean_object* v_declName_1523_, lean_object* v_env_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_addProtected(v_env_1524_, v_declName_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2(lean_object* v_modifiers_1526_, lean_object* v_toPure_1527_, lean_object* v_declName_1528_, lean_object* v_modifyEnv_1529_, lean_object* v___f_1530_, lean_object* v_toBind_1531_, lean_object* v___f_1532_, lean_object* v_____r_1533_){
_start:
{
uint8_t v_isProtected_1534_; 
v_isProtected_1534_ = lean_ctor_get_uint8(v_modifiers_1526_, sizeof(void*)*3 + 1);
if (v_isProtected_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_dec(v___f_1532_);
lean_dec(v_toBind_1531_);
lean_dec_ref(v___f_1530_);
lean_dec(v_modifyEnv_1529_);
v___x_1535_ = lean_apply_2(v_toPure_1527_, lean_box(0), v_declName_1528_);
return v___x_1535_;
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec(v_declName_1528_);
lean_dec(v_toPure_1527_);
v___x_1536_ = lean_apply_1(v_modifyEnv_1529_, v___f_1530_);
v___x_1537_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1536_, v___f_1532_);
return v___x_1537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2___boxed(lean_object* v_modifiers_1538_, lean_object* v_toPure_1539_, lean_object* v_declName_1540_, lean_object* v_modifyEnv_1541_, lean_object* v___f_1542_, lean_object* v_toBind_1543_, lean_object* v___f_1544_, lean_object* v_____r_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Elab_applyVisibility___redArg___lam__2(v_modifiers_1538_, v_toPure_1539_, v_declName_1540_, v_modifyEnv_1541_, v___f_1542_, v_toBind_1543_, v___f_1544_, v_____r_1545_);
lean_dec_ref(v_modifiers_1538_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__3(lean_object* v_toPure_1547_, lean_object* v_modifiers_1548_, lean_object* v_modifyEnv_1549_, lean_object* v_toBind_1550_, lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v_____r_1556_, lean_object* v_declName_1557_){
_start:
{
lean_object* v___f_1558_; lean_object* v___f_1559_; lean_object* v___f_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_inc_n(v_declName_1557_, 3);
lean_inc(v_toPure_1547_);
v___f_1558_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1558_, 0, v_toPure_1547_);
lean_closure_set(v___f_1558_, 1, v_declName_1557_);
v___f_1559_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1559_, 0, v_declName_1557_);
lean_inc(v_toBind_1550_);
v___f_1560_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1560_, 0, v_modifiers_1548_);
lean_closure_set(v___f_1560_, 1, v_toPure_1547_);
lean_closure_set(v___f_1560_, 2, v_declName_1557_);
lean_closure_set(v___f_1560_, 3, v_modifyEnv_1549_);
lean_closure_set(v___f_1560_, 4, v___f_1559_);
lean_closure_set(v___f_1560_, 5, v_toBind_1550_);
lean_closure_set(v___f_1560_, 6, v___f_1558_);
v___x_1561_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(v_inst_1551_, v_inst_1552_, v_inst_1553_, v_inst_1554_, v_inst_1555_, v_declName_1557_);
v___x_1562_ = lean_apply_4(v_toBind_1550_, lean_box(0), lean_box(0), v___x_1561_, v___f_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4(lean_object* v_declName_1563_, lean_object* v___f_1564_, lean_object* v_____do__lift_1565_){
_start:
{
lean_object* v_declName_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_declName_1566_ = l_Lean_mkPrivateName(v_____do__lift_1565_, v_declName_1563_);
v___x_1567_ = lean_box(0);
v___x_1568_ = lean_apply_2(v___f_1564_, v___x_1567_, v_declName_1566_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4___boxed(lean_object* v_declName_1569_, lean_object* v___f_1570_, lean_object* v_____do__lift_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Elab_applyVisibility___redArg___lam__4(v_declName_1569_, v___f_1570_, v_____do__lift_1571_);
lean_dec_ref(v_____do__lift_1571_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5(lean_object* v_modifiers_1573_, lean_object* v_toBind_1574_, lean_object* v_getEnv_1575_, lean_object* v___f_1576_, lean_object* v___f_1577_, lean_object* v_declName_1578_, lean_object* v_____do__lift_1579_){
_start:
{
uint8_t v_visibility_1580_; uint8_t v___x_1581_; 
v_visibility_1580_ = lean_ctor_get_uint8(v_modifiers_1573_, sizeof(void*)*3);
v___x_1581_ = l_Lean_Elab_Visibility_isInferredPublic(v_____do__lift_1579_, v_visibility_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_dec(v_declName_1578_);
lean_dec(v___f_1577_);
v___x_1582_ = lean_apply_4(v_toBind_1574_, lean_box(0), lean_box(0), v_getEnv_1575_, v___f_1576_);
return v___x_1582_;
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec(v___f_1576_);
lean_dec(v_getEnv_1575_);
lean_dec(v_toBind_1574_);
v___x_1583_ = lean_box(0);
v___x_1584_ = lean_apply_2(v___f_1577_, v___x_1583_, v_declName_1578_);
return v___x_1584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5___boxed(lean_object* v_modifiers_1585_, lean_object* v_toBind_1586_, lean_object* v_getEnv_1587_, lean_object* v___f_1588_, lean_object* v___f_1589_, lean_object* v_declName_1590_, lean_object* v_____do__lift_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_Elab_applyVisibility___redArg___lam__5(v_modifiers_1585_, v_toBind_1586_, v_getEnv_1587_, v___f_1588_, v___f_1589_, v_declName_1590_, v_____do__lift_1591_);
lean_dec_ref(v_____do__lift_1591_);
lean_dec_ref(v_modifiers_1585_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg(lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_modifiers_1598_, lean_object* v_declName_1599_){
_start:
{
lean_object* v_toApplicative_1600_; lean_object* v_toBind_1601_; lean_object* v_getEnv_1602_; lean_object* v_modifyEnv_1603_; lean_object* v_toPure_1604_; lean_object* v___f_1605_; lean_object* v___f_1606_; lean_object* v___f_1607_; lean_object* v___x_1608_; 
v_toApplicative_1600_ = lean_ctor_get(v_inst_1593_, 0);
v_toBind_1601_ = lean_ctor_get(v_inst_1593_, 1);
lean_inc_n(v_toBind_1601_, 3);
v_getEnv_1602_ = lean_ctor_get(v_inst_1594_, 0);
lean_inc_n(v_getEnv_1602_, 2);
v_modifyEnv_1603_ = lean_ctor_get(v_inst_1594_, 1);
lean_inc(v_modifyEnv_1603_);
v_toPure_1604_ = lean_ctor_get(v_toApplicative_1600_, 1);
lean_inc(v_toPure_1604_);
lean_inc_ref(v_modifiers_1598_);
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__3), 11, 9);
lean_closure_set(v___f_1605_, 0, v_toPure_1604_);
lean_closure_set(v___f_1605_, 1, v_modifiers_1598_);
lean_closure_set(v___f_1605_, 2, v_modifyEnv_1603_);
lean_closure_set(v___f_1605_, 3, v_toBind_1601_);
lean_closure_set(v___f_1605_, 4, v_inst_1593_);
lean_closure_set(v___f_1605_, 5, v_inst_1594_);
lean_closure_set(v___f_1605_, 6, v_inst_1595_);
lean_closure_set(v___f_1605_, 7, v_inst_1596_);
lean_closure_set(v___f_1605_, 8, v_inst_1597_);
lean_inc_ref(v___f_1605_);
lean_inc(v_declName_1599_);
v___f_1606_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_1606_, 0, v_declName_1599_);
lean_closure_set(v___f_1606_, 1, v___f_1605_);
v___f_1607_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1607_, 0, v_modifiers_1598_);
lean_closure_set(v___f_1607_, 1, v_toBind_1601_);
lean_closure_set(v___f_1607_, 2, v_getEnv_1602_);
lean_closure_set(v___f_1607_, 3, v___f_1606_);
lean_closure_set(v___f_1607_, 4, v___f_1605_);
lean_closure_set(v___f_1607_, 5, v_declName_1599_);
v___x_1608_ = lean_apply_4(v_toBind_1601_, lean_box(0), lean_box(0), v_getEnv_1602_, v___f_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility(lean_object* v_m_1609_, lean_object* v_inst_1610_, lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_inst_1614_, lean_object* v_modifiers_1615_, lean_object* v_declName_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1610_, v_inst_1611_, v_inst_1612_, v_inst_1613_, v_inst_1614_, v_modifiers_1615_, v_declName_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0(lean_object* v_toPure_1618_, lean_object* v_____s_1619_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_box(0);
v___x_1621_ = lean_apply_2(v_toPure_1618_, lean_box(0), v___x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1(lean_object* v___x_1622_, lean_object* v_toPure_1623_, lean_object* v_r_1624_){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1622_);
v___x_1626_ = lean_apply_2(v_toPure_1623_, lean_box(0), v___x_1625_);
return v___x_1626_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0));
v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
return v___x_1629_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2));
v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4));
v___x_1635_ = l_Lean_stringToMessageData(v___x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2(lean_object* v_pre_1636_, lean_object* v_declName_1637_, lean_object* v___x_1638_, lean_object* v_toPure_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_toBind_1642_, lean_object* v___f_1643_, lean_object* v_a_1644_, lean_object* v_x_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
lean_inc(v_a_1644_);
lean_inc(v_pre_1636_);
v___x_1647_ = l_Lean_Name_append(v_pre_1636_, v_a_1644_);
v___x_1648_ = lean_name_eq(v___x_1647_, v_declName_1637_);
lean_dec(v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec(v_a_1644_);
lean_dec(v___f_1643_);
lean_dec(v_toBind_1642_);
lean_dec_ref(v_inst_1641_);
lean_dec_ref(v_inst_1640_);
lean_dec(v_declName_1637_);
lean_dec(v_pre_1636_);
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1638_);
v___x_1650_ = lean_apply_2(v_toPure_1639_, lean_box(0), v___x_1649_);
return v___x_1650_;
}
else
{
lean_object* v___x_1651_; uint8_t v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_dec(v_toPure_1639_);
v___x_1651_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1652_ = 0;
v___x_1653_ = l_Lean_MessageData_ofConstName(v_declName_1637_, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1651_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = l_Lean_MessageData_ofName(v_pre_1636_);
v___x_1658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_1660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = l_Lean_MessageData_ofName(v_a_1644_);
v___x_1662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = l_Lean_throwError___redArg(v_inst_1640_, v_inst_1641_, v___x_1664_);
v___x_1666_ = lean_apply_4(v_toBind_1642_, lean_box(0), lean_box(0), v___x_1665_, v___f_1643_);
return v___x_1666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(lean_object* v_pre_1667_, uint8_t v___x_1668_, lean_object* v_toPure_1669_, lean_object* v_declName_1670_, lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_toBind_1673_, lean_object* v___f_1674_, lean_object* v_____do__lift_1675_){
_start:
{
lean_object* v_fieldNames_1676_; lean_object* v___x_1677_; lean_object* v___f_1678_; lean_object* v___f_1679_; size_t v_sz_1680_; size_t v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_inc(v_pre_1667_);
v_fieldNames_1676_ = l_Lean_getStructureFieldsFlattened(v_____do__lift_1675_, v_pre_1667_, v___x_1668_);
v___x_1677_ = lean_box(0);
lean_inc(v_toPure_1669_);
v___f_1678_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1678_, 0, v___x_1677_);
lean_closure_set(v___f_1678_, 1, v_toPure_1669_);
lean_inc(v_toBind_1673_);
lean_inc_ref(v_inst_1671_);
v___f_1679_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2), 11, 8);
lean_closure_set(v___f_1679_, 0, v_pre_1667_);
lean_closure_set(v___f_1679_, 1, v_declName_1670_);
lean_closure_set(v___f_1679_, 2, v___x_1677_);
lean_closure_set(v___f_1679_, 3, v_toPure_1669_);
lean_closure_set(v___f_1679_, 4, v_inst_1671_);
lean_closure_set(v___f_1679_, 5, v_inst_1672_);
lean_closure_set(v___f_1679_, 6, v_toBind_1673_);
lean_closure_set(v___f_1679_, 7, v___f_1678_);
v_sz_1680_ = lean_array_size(v_fieldNames_1676_);
v___x_1681_ = ((size_t)0ULL);
v___x_1682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1671_, v_fieldNames_1676_, v___f_1679_, v_sz_1680_, v___x_1681_, v___x_1677_);
v___x_1683_ = lean_apply_4(v_toBind_1673_, lean_box(0), lean_box(0), v___x_1682_, v___f_1674_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed(lean_object* v_pre_1684_, lean_object* v___x_1685_, lean_object* v_toPure_1686_, lean_object* v_declName_1687_, lean_object* v_inst_1688_, lean_object* v_inst_1689_, lean_object* v_toBind_1690_, lean_object* v___f_1691_, lean_object* v_____do__lift_1692_){
_start:
{
uint8_t v___x_469__boxed_1693_; lean_object* v_res_1694_; 
v___x_469__boxed_1693_ = lean_unbox(v___x_1685_);
v_res_1694_ = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(v_pre_1684_, v___x_469__boxed_1693_, v_toPure_1686_, v_declName_1687_, v_inst_1688_, v_inst_1689_, v_toBind_1690_, v___f_1691_, v_____do__lift_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4(lean_object* v_pre_1695_, lean_object* v_toPure_1696_, lean_object* v_declName_1697_, lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_toBind_1700_, lean_object* v___f_1701_, lean_object* v_getEnv_1702_, lean_object* v_____do__lift_1703_){
_start:
{
uint8_t v___x_1704_; 
lean_inc(v_pre_1695_);
v___x_1704_ = l_Lean_isStructure(v_____do__lift_1703_, v_pre_1695_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_dec(v_getEnv_1702_);
lean_dec(v___f_1701_);
lean_dec(v_toBind_1700_);
lean_dec_ref(v_inst_1699_);
lean_dec_ref(v_inst_1698_);
lean_dec(v_declName_1697_);
lean_dec(v_pre_1695_);
v___x_1705_ = lean_box(0);
v___x_1706_ = lean_apply_2(v_toPure_1696_, lean_box(0), v___x_1705_);
return v___x_1706_;
}
else
{
lean_object* v___x_1707_; lean_object* v___f_1708_; lean_object* v___x_1709_; 
v___x_1707_ = lean_box(v___x_1704_);
lean_inc(v_toBind_1700_);
v___f_1708_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1708_, 0, v_pre_1695_);
lean_closure_set(v___f_1708_, 1, v___x_1707_);
lean_closure_set(v___f_1708_, 2, v_toPure_1696_);
lean_closure_set(v___f_1708_, 3, v_declName_1697_);
lean_closure_set(v___f_1708_, 4, v_inst_1698_);
lean_closure_set(v___f_1708_, 5, v_inst_1699_);
lean_closure_set(v___f_1708_, 6, v_toBind_1700_);
lean_closure_set(v___f_1708_, 7, v___f_1701_);
v___x_1709_ = lean_apply_4(v_toBind_1700_, lean_box(0), lean_box(0), v_getEnv_1702_, v___f_1708_);
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg(lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_declName_1713_){
_start:
{
if (lean_obj_tag(v_declName_1713_) == 1)
{
lean_object* v_toApplicative_1714_; lean_object* v_toBind_1715_; lean_object* v_toPure_1716_; lean_object* v_pre_1717_; lean_object* v_getEnv_1718_; lean_object* v___f_1719_; lean_object* v___f_1720_; lean_object* v___x_1721_; 
v_toApplicative_1714_ = lean_ctor_get(v_inst_1710_, 0);
v_toBind_1715_ = lean_ctor_get(v_inst_1710_, 1);
lean_inc_n(v_toBind_1715_, 2);
v_toPure_1716_ = lean_ctor_get(v_toApplicative_1714_, 1);
lean_inc_n(v_toPure_1716_, 2);
v_pre_1717_ = lean_ctor_get(v_declName_1713_, 0);
lean_inc(v_pre_1717_);
v_getEnv_1718_ = lean_ctor_get(v_inst_1711_, 0);
lean_inc_n(v_getEnv_1718_, 2);
lean_dec_ref(v_inst_1711_);
v___f_1719_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1719_, 0, v_toPure_1716_);
v___f_1720_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1720_, 0, v_pre_1717_);
lean_closure_set(v___f_1720_, 1, v_toPure_1716_);
lean_closure_set(v___f_1720_, 2, v_declName_1713_);
lean_closure_set(v___f_1720_, 3, v_inst_1710_);
lean_closure_set(v___f_1720_, 4, v_inst_1712_);
lean_closure_set(v___f_1720_, 5, v_toBind_1715_);
lean_closure_set(v___f_1720_, 6, v___f_1719_);
lean_closure_set(v___f_1720_, 7, v_getEnv_1718_);
v___x_1721_ = lean_apply_4(v_toBind_1715_, lean_box(0), lean_box(0), v_getEnv_1718_, v___f_1720_);
return v___x_1721_;
}
else
{
lean_object* v_toApplicative_1722_; lean_object* v_toPure_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v_toApplicative_1722_ = lean_ctor_get(v_inst_1710_, 0);
lean_inc_ref(v_toApplicative_1722_);
lean_dec(v_declName_1713_);
lean_dec_ref(v_inst_1712_);
lean_dec_ref(v_inst_1711_);
lean_dec_ref(v_inst_1710_);
v_toPure_1723_ = lean_ctor_get(v_toApplicative_1722_, 1);
lean_inc(v_toPure_1723_);
lean_dec_ref(v_toApplicative_1722_);
v___x_1724_ = lean_box(0);
v___x_1725_ = lean_apply_2(v_toPure_1723_, lean_box(0), v___x_1724_);
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField(lean_object* v_m_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_inst_1729_, lean_object* v_declName_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1727_, v_inst_1728_, v_inst_1729_, v_declName_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__0(lean_object* v_declName_1732_, lean_object* v_shortName_1733_, lean_object* v_toPure_1734_, lean_object* v_____r_1735_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1736_, 0, v_declName_1732_);
lean_ctor_set(v___x_1736_, 1, v_shortName_1733_);
v___x_1737_ = lean_apply_2(v_toPure_1734_, lean_box(0), v___x_1736_);
return v___x_1737_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0));
v___x_1740_ = l_Lean_stringToMessageData(v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2(lean_object* v_modifiers_1741_, lean_object* v_shortName_1742_, lean_object* v_toPure_1743_, lean_object* v_currNamespace_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_toBind_1747_, lean_object* v_declName_1748_){
_start:
{
uint8_t v_isProtected_1749_; 
v_isProtected_1749_ = lean_ctor_get_uint8(v_modifiers_1741_, sizeof(void*)*3 + 1);
if (v_isProtected_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v_toBind_1747_);
lean_dec_ref(v_inst_1746_);
lean_dec_ref(v_inst_1745_);
lean_dec(v_currNamespace_1744_);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v_declName_1748_);
lean_ctor_set(v___x_1750_, 1, v_shortName_1742_);
v___x_1751_ = lean_apply_2(v_toPure_1743_, lean_box(0), v___x_1750_);
return v___x_1751_;
}
else
{
if (lean_obj_tag(v_currNamespace_1744_) == 1)
{
lean_object* v_str_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec(v_toBind_1747_);
lean_dec_ref(v_inst_1746_);
lean_dec_ref(v_inst_1745_);
v_str_1752_ = lean_ctor_get(v_currNamespace_1744_, 1);
lean_inc_ref(v_str_1752_);
lean_dec_ref_known(v_currNamespace_1744_, 2);
v___x_1753_ = lean_box(0);
v___x_1754_ = l_Lean_Name_str___override(v___x_1753_, v_str_1752_);
v___x_1755_ = l_Lean_Name_append(v___x_1754_, v_shortName_1742_);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v_declName_1748_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = lean_apply_2(v_toPure_1743_, lean_box(0), v___x_1756_);
return v___x_1757_;
}
else
{
lean_object* v___f_1758_; uint8_t v___x_1759_; 
lean_dec(v_currNamespace_1744_);
lean_inc(v_toPure_1743_);
lean_inc(v_shortName_1742_);
lean_inc(v_declName_1748_);
v___f_1758_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1758_, 0, v_declName_1748_);
lean_closure_set(v___f_1758_, 1, v_shortName_1742_);
lean_closure_set(v___f_1758_, 2, v_toPure_1743_);
v___x_1759_ = l_Lean_Name_isAtomic(v_shortName_1742_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec_ref(v___f_1758_);
lean_dec(v_toBind_1747_);
lean_dec_ref(v_inst_1746_);
lean_dec_ref(v_inst_1745_);
v___x_1760_ = lean_box(0);
v___x_1761_ = l_Lean_Elab_mkDeclName___redArg___lam__0(v_declName_1748_, v_shortName_1742_, v_toPure_1743_, v___x_1760_);
return v___x_1761_;
}
else
{
lean_object* v___f_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec(v_declName_1748_);
lean_dec(v_toPure_1743_);
lean_dec(v_shortName_1742_);
v___f_1762_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1762_, 0, v___f_1758_);
v___x_1763_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_1764_ = l_Lean_throwError___redArg(v_inst_1745_, v_inst_1746_, v___x_1763_);
v___x_1765_ = lean_apply_4(v_toBind_1747_, lean_box(0), lean_box(0), v___x_1764_, v___f_1762_);
return v___x_1765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2___boxed(lean_object* v_modifiers_1766_, lean_object* v_shortName_1767_, lean_object* v_toPure_1768_, lean_object* v_currNamespace_1769_, lean_object* v_inst_1770_, lean_object* v_inst_1771_, lean_object* v_toBind_1772_, lean_object* v_declName_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Elab_mkDeclName___redArg___lam__2(v_modifiers_1766_, v_shortName_1767_, v_toPure_1768_, v_currNamespace_1769_, v_inst_1770_, v_inst_1771_, v_toBind_1772_, v_declName_1773_);
lean_dec_ref(v_modifiers_1766_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__1(lean_object* v_inst_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_modifiers_1780_, lean_object* v___y_1781_, lean_object* v_toBind_1782_, lean_object* v___f_1783_, lean_object* v_____r_1784_){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1775_, v_inst_1776_, v_inst_1777_, v_inst_1778_, v_inst_1779_, v_modifiers_1780_, v___y_1781_);
v___x_1786_ = lean_apply_4(v_toBind_1782_, lean_box(0), lean_box(0), v___x_1785_, v___f_1783_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3(lean_object* v_modifiers_1787_, lean_object* v_toPure_1788_, lean_object* v_inst_1789_, lean_object* v_inst_1790_, lean_object* v_toBind_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v___y_1795_, lean_object* v_____r_1796_, lean_object* v_shortName_1797_, lean_object* v_currNamespace_1798_){
_start:
{
lean_object* v___f_1799_; lean_object* v___f_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_inc_n(v_toBind_1791_, 2);
lean_inc_ref_n(v_inst_1790_, 2);
lean_inc_ref_n(v_inst_1789_, 2);
lean_inc_ref(v_modifiers_1787_);
v___f_1799_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1799_, 0, v_modifiers_1787_);
lean_closure_set(v___f_1799_, 1, v_shortName_1797_);
lean_closure_set(v___f_1799_, 2, v_toPure_1788_);
lean_closure_set(v___f_1799_, 3, v_currNamespace_1798_);
lean_closure_set(v___f_1799_, 4, v_inst_1789_);
lean_closure_set(v___f_1799_, 5, v_inst_1790_);
lean_closure_set(v___f_1799_, 6, v_toBind_1791_);
lean_inc(v___y_1795_);
lean_inc_ref(v_inst_1792_);
v___f_1800_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1800_, 0, v_inst_1789_);
lean_closure_set(v___f_1800_, 1, v_inst_1792_);
lean_closure_set(v___f_1800_, 2, v_inst_1790_);
lean_closure_set(v___f_1800_, 3, v_inst_1793_);
lean_closure_set(v___f_1800_, 4, v_inst_1794_);
lean_closure_set(v___f_1800_, 5, v_modifiers_1787_);
lean_closure_set(v___f_1800_, 6, v___y_1795_);
lean_closure_set(v___f_1800_, 7, v_toBind_1791_);
lean_closure_set(v___f_1800_, 8, v___f_1799_);
v___x_1801_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1789_, v_inst_1792_, v_inst_1790_, v___y_1795_);
v___x_1802_ = lean_apply_4(v_toBind_1791_, lean_box(0), lean_box(0), v___x_1801_, v___f_1800_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__4(lean_object* v___f_1803_, lean_object* v_shortName_1804_, lean_object* v_currNamespace_1805_, lean_object* v_____r_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_apply_3(v___f_1803_, v_____r_1806_, v_shortName_1804_, v_currNamespace_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5(lean_object* v_modifiers_1808_, lean_object* v_toPure_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_toBind_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_inst_1815_, uint8_t v_isRootName_1816_, lean_object* v_shortName_1817_, lean_object* v_currNamespace_1818_, lean_object* v_name_1819_, lean_object* v___x_1820_, lean_object* v_imported_1821_, lean_object* v_ctx_1822_, lean_object* v_scopes_1823_, lean_object* v_____r_1824_){
_start:
{
lean_object* v___y_1826_; 
if (v_isRootName_1816_ == 0)
{
lean_object* v___x_1845_; 
lean_dec(v_scopes_1823_);
lean_dec(v_ctx_1822_);
lean_dec(v_imported_1821_);
lean_inc(v_shortName_1817_);
lean_inc(v_currNamespace_1818_);
v___x_1845_ = l_Lean_Name_append(v_currNamespace_1818_, v_shortName_1817_);
v___y_1826_ = v___x_1845_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1846_ = lean_box(0);
lean_inc(v_name_1819_);
v___x_1847_ = l_Lean_Name_replacePrefix(v_name_1819_, v___x_1820_, v___x_1846_);
v___x_1848_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
lean_ctor_set(v___x_1848_, 1, v_imported_1821_);
lean_ctor_set(v___x_1848_, 2, v_ctx_1822_);
lean_ctor_set(v___x_1848_, 3, v_scopes_1823_);
v___x_1849_ = l_Lean_MacroScopesView_review(v___x_1848_);
v___y_1826_ = v___x_1849_;
goto v___jp_1825_;
}
v___jp_1825_:
{
lean_object* v___f_1827_; 
lean_inc(v___y_1826_);
lean_inc_ref(v_inst_1815_);
lean_inc(v_inst_1814_);
lean_inc_ref(v_inst_1813_);
lean_inc(v_toBind_1812_);
lean_inc_ref(v_inst_1811_);
lean_inc_ref(v_inst_1810_);
lean_inc(v_toPure_1809_);
lean_inc_ref(v_modifiers_1808_);
v___f_1827_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__3), 12, 9);
lean_closure_set(v___f_1827_, 0, v_modifiers_1808_);
lean_closure_set(v___f_1827_, 1, v_toPure_1809_);
lean_closure_set(v___f_1827_, 2, v_inst_1810_);
lean_closure_set(v___f_1827_, 3, v_inst_1811_);
lean_closure_set(v___f_1827_, 4, v_toBind_1812_);
lean_closure_set(v___f_1827_, 5, v_inst_1813_);
lean_closure_set(v___f_1827_, 6, v_inst_1814_);
lean_closure_set(v___f_1827_, 7, v_inst_1815_);
lean_closure_set(v___f_1827_, 8, v___y_1826_);
if (v_isRootName_1816_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec_ref(v___f_1827_);
lean_dec(v_name_1819_);
v___x_1828_ = lean_box(0);
v___x_1829_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1808_, v_toPure_1809_, v_inst_1810_, v_inst_1811_, v_toBind_1812_, v_inst_1813_, v_inst_1814_, v_inst_1815_, v___y_1826_, v___x_1828_, v_shortName_1817_, v_currNamespace_1818_);
return v___x_1829_;
}
else
{
if (lean_obj_tag(v_name_1819_) == 1)
{
lean_object* v_pre_1830_; lean_object* v_str_1831_; lean_object* v___x_1832_; lean_object* v_shortName_1833_; lean_object* v_currNamespace_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec_ref(v___f_1827_);
lean_dec(v_currNamespace_1818_);
lean_dec(v_shortName_1817_);
v_pre_1830_ = lean_ctor_get(v_name_1819_, 0);
lean_inc(v_pre_1830_);
v_str_1831_ = lean_ctor_get(v_name_1819_, 1);
lean_inc_ref(v_str_1831_);
lean_dec_ref_known(v_name_1819_, 2);
v___x_1832_ = lean_box(0);
v_shortName_1833_ = l_Lean_Name_str___override(v___x_1832_, v_str_1831_);
v_currNamespace_1834_ = l_Lean_Name_replacePrefix(v_pre_1830_, v___x_1820_, v___x_1832_);
v___x_1835_ = lean_box(0);
v___x_1836_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1808_, v_toPure_1809_, v_inst_1810_, v_inst_1811_, v_toBind_1812_, v_inst_1813_, v_inst_1814_, v_inst_1815_, v___y_1826_, v___x_1835_, v_shortName_1833_, v_currNamespace_1834_);
return v___x_1836_;
}
else
{
lean_object* v___f_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec(v___y_1826_);
lean_dec_ref(v_inst_1815_);
lean_dec(v_inst_1814_);
lean_dec_ref(v_inst_1813_);
lean_dec(v_toPure_1809_);
lean_dec_ref(v_modifiers_1808_);
v___f_1837_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__4), 4, 3);
lean_closure_set(v___f_1837_, 0, v___f_1827_);
lean_closure_set(v___f_1837_, 1, v_shortName_1817_);
lean_closure_set(v___f_1837_, 2, v_currNamespace_1818_);
v___x_1838_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1839_ = l_Lean_MessageData_ofName(v_name_1819_);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = l_Lean_throwError___redArg(v_inst_1810_, v_inst_1811_, v___x_1842_);
v___x_1844_ = lean_apply_4(v_toBind_1812_, lean_box(0), lean_box(0), v___x_1843_, v___f_1837_);
return v___x_1844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_modifiers_1850_ = _args[0];
lean_object* v_toPure_1851_ = _args[1];
lean_object* v_inst_1852_ = _args[2];
lean_object* v_inst_1853_ = _args[3];
lean_object* v_toBind_1854_ = _args[4];
lean_object* v_inst_1855_ = _args[5];
lean_object* v_inst_1856_ = _args[6];
lean_object* v_inst_1857_ = _args[7];
lean_object* v_isRootName_1858_ = _args[8];
lean_object* v_shortName_1859_ = _args[9];
lean_object* v_currNamespace_1860_ = _args[10];
lean_object* v_name_1861_ = _args[11];
lean_object* v___x_1862_ = _args[12];
lean_object* v_imported_1863_ = _args[13];
lean_object* v_ctx_1864_ = _args[14];
lean_object* v_scopes_1865_ = _args[15];
lean_object* v_____r_1866_ = _args[16];
_start:
{
uint8_t v_isRootName_boxed_1867_; lean_object* v_res_1868_; 
v_isRootName_boxed_1867_ = lean_unbox(v_isRootName_1858_);
v_res_1868_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1850_, v_toPure_1851_, v_inst_1852_, v_inst_1853_, v_toBind_1854_, v_inst_1855_, v_inst_1856_, v_inst_1857_, v_isRootName_boxed_1867_, v_shortName_1859_, v_currNamespace_1860_, v_name_1861_, v___x_1862_, v_imported_1863_, v_ctx_1864_, v_scopes_1865_, v_____r_1866_);
lean_dec(v___x_1862_);
return v_res_1868_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___closed__3(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__2));
v___x_1874_ = l_Lean_stringToMessageData(v___x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg(lean_object* v_inst_1875_, lean_object* v_inst_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_, lean_object* v_inst_1879_, lean_object* v_currNamespace_1880_, lean_object* v_modifiers_1881_, lean_object* v_shortName_1882_){
_start:
{
lean_object* v_view_1883_; lean_object* v_toApplicative_1884_; lean_object* v_name_1885_; lean_object* v_imported_1886_; lean_object* v_ctx_1887_; lean_object* v_scopes_1888_; lean_object* v_toBind_1889_; lean_object* v_toPure_1890_; lean_object* v___x_1891_; uint8_t v_isRootName_1892_; lean_object* v___x_1893_; lean_object* v___f_1894_; uint8_t v___x_1895_; 
lean_inc_n(v_shortName_1882_, 2);
v_view_1883_ = l_Lean_extractMacroScopes(v_shortName_1882_);
v_toApplicative_1884_ = lean_ctor_get(v_inst_1875_, 0);
v_name_1885_ = lean_ctor_get(v_view_1883_, 0);
lean_inc_n(v_name_1885_, 2);
v_imported_1886_ = lean_ctor_get(v_view_1883_, 1);
lean_inc_n(v_imported_1886_, 2);
v_ctx_1887_ = lean_ctor_get(v_view_1883_, 2);
lean_inc_n(v_ctx_1887_, 2);
v_scopes_1888_ = lean_ctor_get(v_view_1883_, 3);
lean_inc_n(v_scopes_1888_, 2);
lean_dec_ref(v_view_1883_);
v_toBind_1889_ = lean_ctor_get(v_inst_1875_, 1);
lean_inc_n(v_toBind_1889_, 2);
v_toPure_1890_ = lean_ctor_get(v_toApplicative_1884_, 1);
v___x_1891_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_1892_ = l_Lean_Name_isPrefixOf(v___x_1891_, v_name_1885_);
v___x_1893_ = lean_box(v_isRootName_1892_);
lean_inc(v_currNamespace_1880_);
lean_inc_ref(v_inst_1879_);
lean_inc(v_inst_1878_);
lean_inc_ref(v_inst_1876_);
lean_inc_ref(v_inst_1877_);
lean_inc_ref(v_inst_1875_);
lean_inc(v_toPure_1890_);
lean_inc_ref(v_modifiers_1881_);
v___f_1894_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1894_, 0, v_modifiers_1881_);
lean_closure_set(v___f_1894_, 1, v_toPure_1890_);
lean_closure_set(v___f_1894_, 2, v_inst_1875_);
lean_closure_set(v___f_1894_, 3, v_inst_1877_);
lean_closure_set(v___f_1894_, 4, v_toBind_1889_);
lean_closure_set(v___f_1894_, 5, v_inst_1876_);
lean_closure_set(v___f_1894_, 6, v_inst_1878_);
lean_closure_set(v___f_1894_, 7, v_inst_1879_);
lean_closure_set(v___f_1894_, 8, v___x_1893_);
lean_closure_set(v___f_1894_, 9, v_shortName_1882_);
lean_closure_set(v___f_1894_, 10, v_currNamespace_1880_);
lean_closure_set(v___f_1894_, 11, v_name_1885_);
lean_closure_set(v___f_1894_, 12, v___x_1891_);
lean_closure_set(v___f_1894_, 13, v_imported_1886_);
lean_closure_set(v___f_1894_, 14, v_ctx_1887_);
lean_closure_set(v___f_1894_, 15, v_scopes_1888_);
v___x_1895_ = lean_name_eq(v_name_1885_, v___x_1891_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_inc(v_toPure_1890_);
lean_dec_ref(v___f_1894_);
v___x_1896_ = lean_box(0);
v___x_1897_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1881_, v_toPure_1890_, v_inst_1875_, v_inst_1877_, v_toBind_1889_, v_inst_1876_, v_inst_1878_, v_inst_1879_, v_isRootName_1892_, v_shortName_1882_, v_currNamespace_1880_, v_name_1885_, v___x_1891_, v_imported_1886_, v_ctx_1887_, v_scopes_1888_, v___x_1896_);
return v___x_1897_;
}
else
{
lean_object* v___f_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
lean_dec(v_scopes_1888_);
lean_dec(v_ctx_1887_);
lean_dec(v_imported_1886_);
lean_dec(v_name_1885_);
lean_dec(v_shortName_1882_);
lean_dec_ref(v_modifiers_1881_);
lean_dec(v_currNamespace_1880_);
lean_dec_ref(v_inst_1879_);
lean_dec(v_inst_1878_);
lean_dec_ref(v_inst_1876_);
v___f_1898_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1898_, 0, v___f_1894_);
v___x_1899_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_1900_ = l_Lean_throwError___redArg(v_inst_1875_, v_inst_1877_, v___x_1899_);
v___x_1901_ = lean_apply_4(v_toBind_1889_, lean_box(0), lean_box(0), v___x_1900_, v___f_1898_);
return v___x_1901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName(lean_object* v_m_1902_, lean_object* v_inst_1903_, lean_object* v_inst_1904_, lean_object* v_inst_1905_, lean_object* v_inst_1906_, lean_object* v_inst_1907_, lean_object* v_currNamespace_1908_, lean_object* v_modifiers_1909_, lean_object* v_shortName_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_Elab_mkDeclName___redArg(v_inst_1903_, v_inst_1904_, v_inst_1905_, v_inst_1906_, v_inst_1907_, v_currNamespace_1908_, v_modifiers_1909_, v_shortName_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore(lean_object* v_declId_1921_){
_start:
{
uint8_t v___x_1922_; 
v___x_1922_ = l_Lean_Syntax_isIdent(v_declId_1921_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v_id_1925_; lean_object* v___x_1926_; lean_object* v_optUnivDeclStx_1927_; lean_object* v___x_1928_; 
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = l_Lean_Syntax_getArg(v_declId_1921_, v___x_1923_);
v_id_1925_ = l_Lean_Syntax_getId(v___x_1924_);
lean_dec(v___x_1924_);
v___x_1926_ = lean_unsigned_to_nat(1u);
v_optUnivDeclStx_1927_ = l_Lean_Syntax_getArg(v_declId_1921_, v___x_1926_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v_id_1925_);
lean_ctor_set(v___x_1928_, 1, v_optUnivDeclStx_1927_);
return v___x_1928_;
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = l_Lean_Syntax_getId(v_declId_1921_);
v___x_1930_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__3));
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
return v___x_1931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore___boxed(lean_object* v_declId_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_Elab_expandDeclIdCore(v_declId_1932_);
lean_dec(v_declId_1932_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(lean_object* v_msgData_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; lean_object* v_env_1941_; uint8_t v___x_1942_; lean_object* v_env_1943_; lean_object* v___x_1944_; lean_object* v_toCold_1945_; lean_object* v_mctx_1946_; lean_object* v_lctx_1947_; lean_object* v_options_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1940_ = lean_st_ref_get(v___y_1938_);
v_env_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc_ref(v_env_1941_);
lean_dec(v___x_1940_);
v___x_1942_ = 0;
v_env_1943_ = l_Lean_Environment_setRecordingDeps(v_env_1941_, v___x_1942_);
v___x_1944_ = lean_st_ref_get(v___y_1936_);
v_toCold_1945_ = lean_ctor_get(v___y_1937_, 0);
v_mctx_1946_ = lean_ctor_get(v___x_1944_, 0);
lean_inc_ref(v_mctx_1946_);
lean_dec(v___x_1944_);
v_lctx_1947_ = lean_ctor_get(v___y_1935_, 2);
v_options_1948_ = lean_ctor_get(v_toCold_1945_, 2);
lean_inc_ref(v_options_1948_);
lean_inc_ref(v_lctx_1947_);
v___x_1949_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1949_, 0, v_env_1943_);
lean_ctor_set(v___x_1949_, 1, v_mctx_1946_);
lean_ctor_set(v___x_1949_, 2, v_lctx_1947_);
lean_ctor_set(v___x_1949_, 3, v_options_1948_);
v___x_1950_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
lean_ctor_set(v___x_1950_, 1, v_msgData_1934_);
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msgData_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
return v_res_1958_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(lean_object* v_opts_1959_, lean_object* v_opt_1960_){
_start:
{
lean_object* v_name_1961_; lean_object* v_defValue_1962_; lean_object* v_map_1963_; lean_object* v___x_1964_; 
v_name_1961_ = lean_ctor_get(v_opt_1960_, 0);
v_defValue_1962_ = lean_ctor_get(v_opt_1960_, 1);
v_map_1963_ = lean_ctor_get(v_opts_1959_, 0);
v___x_1964_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1963_, v_name_1961_);
if (lean_obj_tag(v___x_1964_) == 0)
{
uint8_t v___x_1965_; 
v___x_1965_ = lean_unbox(v_defValue_1962_);
return v___x_1965_;
}
else
{
lean_object* v_val_1966_; 
v_val_1966_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_val_1966_);
lean_dec_ref_known(v___x_1964_, 1);
if (lean_obj_tag(v_val_1966_) == 1)
{
uint8_t v_v_1967_; 
v_v_1967_ = lean_ctor_get_uint8(v_val_1966_, 0);
lean_dec_ref_known(v_val_1966_, 0);
return v_v_1967_;
}
else
{
uint8_t v___x_1968_; 
lean_dec(v_val_1966_);
v___x_1968_ = lean_unbox(v_defValue_1962_);
return v___x_1968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_opts_1969_, lean_object* v_opt_1970_){
_start:
{
uint8_t v_res_1971_; lean_object* v_r_1972_; 
v_res_1971_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_opts_1969_, v_opt_1970_);
lean_dec_ref(v_opt_1970_);
lean_dec_ref(v_opts_1969_);
v_r_1972_ = lean_box(v_res_1971_);
return v_r_1972_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = lean_box(1);
v___x_1974_ = l_Lean_MessageData_ofFormat(v___x_1973_);
return v___x_1974_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2));
v___x_1979_ = l_Lean_MessageData_ofFormat(v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(lean_object* v_x_1980_, lean_object* v_x_1981_){
_start:
{
if (lean_obj_tag(v_x_1981_) == 0)
{
return v_x_1980_;
}
else
{
lean_object* v_head_1982_; lean_object* v_tail_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2005_; 
v_head_1982_ = lean_ctor_get(v_x_1981_, 0);
v_tail_1983_ = lean_ctor_get(v_x_1981_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_x_1981_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1985_ = v_x_1981_;
v_isShared_1986_ = v_isSharedCheck_2005_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_tail_1983_);
lean_inc(v_head_1982_);
lean_dec(v_x_1981_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2005_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_before_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2003_; 
v_before_1987_ = lean_ctor_get(v_head_1982_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_head_1982_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; 
v_unused_2004_ = lean_ctor_get(v_head_1982_, 1);
lean_dec(v_unused_2004_);
v___x_1989_ = v_head_1982_;
v_isShared_1990_ = v_isSharedCheck_2003_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_before_1987_);
lean_dec(v_head_1982_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2003_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1991_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_1990_ == 0)
{
lean_ctor_set_tag(v___x_1989_, 7);
lean_ctor_set(v___x_1989_, 1, v___x_1991_);
lean_ctor_set(v___x_1989_, 0, v_x_1980_);
v___x_1993_ = v___x_1989_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_x_1980_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3);
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 7);
lean_ctor_set(v___x_1985_, 1, v___x_1994_);
lean_ctor_set(v___x_1985_, 0, v___x_1993_);
v___x_1996_ = v___x_1985_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1997_ = l_Lean_MessageData_ofSyntax(v_before_1987_);
v___x_1998_ = l_Lean_indentD(v___x_1997_);
v___x_1999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1996_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v_x_1980_ = v___x_1999_;
v_x_1981_ = v_tail_1983_;
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
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1));
v___x_2010_ = l_Lean_MessageData_ofFormat(v___x_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_2011_, lean_object* v_macroStack_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2015_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2013_);
v___x_2016_ = l_Lean_Elab_pp_macroStack;
v___x_2017_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v___x_2015_, v___x_2016_);
lean_dec_ref(v___x_2015_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
lean_dec(v_macroStack_2012_);
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_msgData_2011_);
return v___x_2018_;
}
else
{
if (lean_obj_tag(v_macroStack_2012_) == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v_msgData_2011_);
return v___x_2019_;
}
else
{
lean_object* v_head_2020_; lean_object* v_after_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2036_; 
v_head_2020_ = lean_ctor_get(v_macroStack_2012_, 0);
lean_inc(v_head_2020_);
v_after_2021_ = lean_ctor_get(v_head_2020_, 1);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_head_2020_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v_head_2020_, 0);
lean_dec(v_unused_2037_);
v___x_2023_ = v_head_2020_;
v_isShared_2024_ = v_isSharedCheck_2036_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_after_2021_);
lean_dec(v_head_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2036_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2025_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_2024_ == 0)
{
lean_ctor_set_tag(v___x_2023_, 7);
lean_ctor_set(v___x_2023_, 1, v___x_2025_);
lean_ctor_set(v___x_2023_, 0, v_msgData_2011_);
v___x_2027_ = v___x_2023_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_msgData_2011_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v_msgData_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2028_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_2029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2027_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = l_Lean_MessageData_ofSyntax(v_after_2021_);
v___x_2031_ = l_Lean_indentD(v___x_2030_);
v_msgData_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2032_, 0, v___x_2029_);
lean_ctor_set(v_msgData_2032_, 1, v___x_2031_);
v___x_2033_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(v_msgData_2032_, v_macroStack_2012_);
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_2038_, lean_object* v_macroStack_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_2038_, v_macroStack_2039_, v___y_2040_);
lean_dec_ref(v___y_2040_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(lean_object* v_msg_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v_ref_2051_; lean_object* v_macroStack_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v_a_2055_; lean_object* v___x_2056_; lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2065_; 
v_ref_2051_ = lean_ctor_get(v___y_2048_, 2);
v_macroStack_2052_ = lean_ctor_get(v___y_2044_, 1);
v___x_2053_ = l_Lean_Elab_getBetterRef(v_ref_2051_, v_macroStack_2052_);
v___x_2054_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msg_2043_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref(v___x_2054_);
lean_inc(v_macroStack_2052_);
v___x_2056_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_a_2055_, v_macroStack_2052_, v___y_2048_);
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2065_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2065_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2053_);
lean_ctor_set(v___x_2061_, 1, v_a_2057_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 1);
lean_ctor_set(v___x_2059_, 0, v___x_2061_);
v___x_2063_ = v___x_2059_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg___boxed(lean_object* v_msg_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
return v_res_2074_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17___redArg___closed__0(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0);
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17___redArg(){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17___redArg___closed__0);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17___redArg___boxed(lean_object* v___dummy_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17___redArg();
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(lean_object* v_env_2081_, lean_object* v_declName_2082_, lean_object* v___f_2083_, lean_object* v_addInfo_2084_, lean_object* v_____r_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v___x_2093_; uint8_t v___x_2094_; uint8_t v___x_2095_; 
lean_inc(v_declName_2082_);
v___x_2093_ = l_Lean_mkPrivateName(v_env_2081_, v_declName_2082_);
v___x_2094_ = 1;
lean_inc(v___x_2093_);
v___x_2095_ = l_Lean_Environment_contains(v_env_2081_, v___x_2093_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_dec(v___x_2093_);
lean_dec_ref(v_addInfo_2084_);
lean_dec(v_declName_2082_);
v___x_2096_ = lean_box(0);
lean_inc(v___y_2091_);
lean_inc_ref(v___y_2090_);
lean_inc(v___y_2089_);
lean_inc_ref(v___y_2088_);
lean_inc(v___y_2087_);
lean_inc_ref(v___y_2086_);
v___x_2097_ = lean_apply_8(v___f_2083_, v___x_2096_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, lean_box(0));
return v___x_2097_;
}
else
{
lean_object* v___x_2098_; 
lean_dec_ref(v___f_2083_);
lean_inc(v___y_2091_);
lean_inc_ref(v___y_2090_);
lean_inc(v___y_2089_);
lean_inc_ref(v___y_2088_);
lean_inc(v___y_2087_);
lean_inc_ref(v___y_2086_);
v___x_2098_ = lean_apply_8(v_addInfo_2084_, v___x_2093_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, lean_box(0));
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_dec_ref_known(v___x_2098_, 1);
v___x_2099_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1);
v___x_2100_ = l_Lean_MessageData_ofConstName(v_declName_2082_, v___x_2094_);
v___x_2101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2099_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2101_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2103_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
return v___x_2104_;
}
else
{
lean_dec(v_declName_2082_);
return v___x_2098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed(lean_object* v_env_2105_, lean_object* v_declName_2106_, lean_object* v___f_2107_, lean_object* v_addInfo_2108_, lean_object* v_____r_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(v_env_2105_, v_declName_2106_, v___f_2107_, v_addInfo_2108_, v_____r_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(lean_object* v_declName_2118_, uint8_t v___x_2119_, lean_object* v___f_2120_, lean_object* v_env_2121_, lean_object* v_____do__lift_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
lean_inc(v_declName_2118_);
v___x_2137_ = l_Lean_privateToUserName(v_declName_2118_);
lean_inc_ref(v_env_2121_);
v___x_2138_ = lean_is_reserved_name(v_env_2121_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
lean_inc(v_declName_2118_);
v___x_2139_ = l_Lean_mkPrivateName(v_____do__lift_2122_, v_declName_2118_);
v___x_2140_ = lean_is_reserved_name(v_env_2121_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_dec(v_declName_2118_);
v___x_2141_ = lean_box(0);
lean_inc(v___y_2128_);
lean_inc_ref(v___y_2127_);
lean_inc(v___y_2126_);
lean_inc_ref(v___y_2125_);
lean_inc(v___y_2124_);
lean_inc_ref(v___y_2123_);
v___x_2142_ = lean_apply_8(v___f_2120_, v___x_2141_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, lean_box(0));
return v___x_2142_;
}
else
{
lean_dec_ref(v___f_2120_);
goto v___jp_2130_;
}
}
else
{
lean_dec_ref(v_env_2121_);
lean_dec_ref(v___f_2120_);
goto v___jp_2130_;
}
v___jp_2130_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2131_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2132_ = l_Lean_MessageData_ofConstName(v_declName_2118_, v___x_2119_);
v___x_2133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2131_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3);
v___x_2135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2133_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2135_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
return v___x_2136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed(lean_object* v_declName_2143_, lean_object* v___x_2144_, lean_object* v___f_2145_, lean_object* v_env_2146_, lean_object* v_____do__lift_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
uint8_t v___x_16679__boxed_2155_; lean_object* v_res_2156_; 
v___x_16679__boxed_2155_ = lean_unbox(v___x_2144_);
v_res_2156_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(v_declName_2143_, v___x_16679__boxed_2155_, v___f_2145_, v_env_2146_, v_____do__lift_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec_ref(v_____do__lift_2147_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(lean_object* v_t_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; lean_object* v_infoState_2161_; uint8_t v_enabled_2162_; 
v___x_2160_ = lean_st_ref_get(v___y_2158_);
v_infoState_2161_ = lean_ctor_get(v___x_2160_, 8);
lean_inc_ref(v_infoState_2161_);
lean_dec(v___x_2160_);
v_enabled_2162_ = lean_ctor_get_uint8(v_infoState_2161_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2161_);
if (v_enabled_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_dec_ref(v_t_2157_);
v___x_2163_ = lean_box(0);
v___x_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
return v___x_2164_;
}
else
{
lean_object* v___x_2165_; lean_object* v_infoState_2166_; lean_object* v_env_2167_; lean_object* v_nextMacroScope_2168_; lean_object* v_ngen_2169_; lean_object* v_auxDeclNGen_2170_; lean_object* v_traceState_2171_; lean_object* v_cache_2172_; lean_object* v_recordedDeps_2173_; lean_object* v_messages_2174_; lean_object* v_snapshotTasks_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2197_; 
v___x_2165_ = lean_st_ref_take(v___y_2158_);
v_infoState_2166_ = lean_ctor_get(v___x_2165_, 8);
v_env_2167_ = lean_ctor_get(v___x_2165_, 0);
v_nextMacroScope_2168_ = lean_ctor_get(v___x_2165_, 1);
v_ngen_2169_ = lean_ctor_get(v___x_2165_, 2);
v_auxDeclNGen_2170_ = lean_ctor_get(v___x_2165_, 3);
v_traceState_2171_ = lean_ctor_get(v___x_2165_, 4);
v_cache_2172_ = lean_ctor_get(v___x_2165_, 5);
v_recordedDeps_2173_ = lean_ctor_get(v___x_2165_, 6);
v_messages_2174_ = lean_ctor_get(v___x_2165_, 7);
v_snapshotTasks_2175_ = lean_ctor_get(v___x_2165_, 9);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2177_ = v___x_2165_;
v_isShared_2178_ = v_isSharedCheck_2197_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_snapshotTasks_2175_);
lean_inc(v_infoState_2166_);
lean_inc(v_messages_2174_);
lean_inc(v_recordedDeps_2173_);
lean_inc(v_cache_2172_);
lean_inc(v_traceState_2171_);
lean_inc(v_auxDeclNGen_2170_);
lean_inc(v_ngen_2169_);
lean_inc(v_nextMacroScope_2168_);
lean_inc(v_env_2167_);
lean_dec(v___x_2165_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2197_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
uint8_t v_enabled_2179_; lean_object* v_assignment_2180_; lean_object* v_lazyAssignment_2181_; lean_object* v_trees_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2196_; 
v_enabled_2179_ = lean_ctor_get_uint8(v_infoState_2166_, sizeof(void*)*3);
v_assignment_2180_ = lean_ctor_get(v_infoState_2166_, 0);
v_lazyAssignment_2181_ = lean_ctor_get(v_infoState_2166_, 1);
v_trees_2182_ = lean_ctor_get(v_infoState_2166_, 2);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_infoState_2166_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2184_ = v_infoState_2166_;
v_isShared_2185_ = v_isSharedCheck_2196_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_trees_2182_);
lean_inc(v_lazyAssignment_2181_);
lean_inc(v_assignment_2180_);
lean_dec(v_infoState_2166_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2196_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2186_ = lean_box(0);
v___x_2187_ = l_Lean_PersistentArray_push___redArg(v_trees_2182_, v_t_2157_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 2, v___x_2187_);
v___x_2189_ = v___x_2184_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_assignment_2180_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_lazyAssignment_2181_);
lean_ctor_set(v_reuseFailAlloc_2195_, 2, v___x_2187_);
lean_ctor_set_uint8(v_reuseFailAlloc_2195_, sizeof(void*)*3, v_enabled_2179_);
v___x_2189_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2191_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 8, v___x_2189_);
v___x_2191_ = v___x_2177_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_env_2167_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_nextMacroScope_2168_);
lean_ctor_set(v_reuseFailAlloc_2194_, 2, v_ngen_2169_);
lean_ctor_set(v_reuseFailAlloc_2194_, 3, v_auxDeclNGen_2170_);
lean_ctor_set(v_reuseFailAlloc_2194_, 4, v_traceState_2171_);
lean_ctor_set(v_reuseFailAlloc_2194_, 5, v_cache_2172_);
lean_ctor_set(v_reuseFailAlloc_2194_, 6, v_recordedDeps_2173_);
lean_ctor_set(v_reuseFailAlloc_2194_, 7, v_messages_2174_);
lean_ctor_set(v_reuseFailAlloc_2194_, 8, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2194_, 9, v_snapshotTasks_2175_);
v___x_2191_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = lean_st_ref_put(v___y_2158_, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2186_);
return v___x_2193_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg___boxed(lean_object* v_t_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_2198_, v___y_2199_);
lean_dec(v___y_2199_);
return v_res_2201_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_unsigned_to_nat(32u);
v___x_2203_ = lean_mk_empty_array_with_capacity(v___x_2202_);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1(void){
_start:
{
size_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2205_ = ((size_t)5ULL);
v___x_2206_ = lean_unsigned_to_nat(0u);
v___x_2207_ = lean_unsigned_to_nat(32u);
v___x_2208_ = lean_mk_empty_array_with_capacity(v___x_2207_);
v___x_2209_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0);
v___x_2210_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___x_2208_);
lean_ctor_set(v___x_2210_, 2, v___x_2206_);
lean_ctor_set(v___x_2210_, 3, v___x_2206_);
lean_ctor_set_usize(v___x_2210_, 4, v___x_2205_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(lean_object* v_t_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; lean_object* v_infoState_2220_; uint8_t v_enabled_2221_; 
v___x_2219_ = lean_st_ref_get(v___y_2217_);
v_infoState_2220_ = lean_ctor_get(v___x_2219_, 8);
lean_inc_ref(v_infoState_2220_);
lean_dec(v___x_2219_);
v_enabled_2221_ = lean_ctor_get_uint8(v_infoState_2220_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2220_);
if (v_enabled_2221_ == 0)
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec_ref(v_t_2211_);
v___x_2222_ = lean_box(0);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
return v___x_2223_;
}
else
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1);
v___x_2225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2225_, 0, v_t_2211_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v___x_2225_, v___y_2217_);
return v___x_2226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___boxed(lean_object* v_t_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v_t_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
if (lean_obj_tag(v_a_2236_) == 0)
{
lean_object* v___x_2238_; 
v___x_2238_ = l_List_reverse___redArg(v_a_2237_);
return v___x_2238_;
}
else
{
lean_object* v_head_2239_; lean_object* v_tail_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2249_; 
v_head_2239_ = lean_ctor_get(v_a_2236_, 0);
v_tail_2240_ = lean_ctor_get(v_a_2236_, 1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_a_2236_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2242_ = v_a_2236_;
v_isShared_2243_ = v_isSharedCheck_2249_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_tail_2240_);
lean_inc(v_head_2239_);
lean_dec(v_a_2236_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2249_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; lean_object* v___x_2246_; 
v___x_2244_ = l_Lean_mkLevelParam(v_head_2239_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 1, v_a_2237_);
lean_ctor_set(v___x_2242_, 0, v___x_2244_);
v___x_2246_ = v___x_2242_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2244_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_a_2237_);
v___x_2246_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
v_a_2236_ = v_tail_2240_;
v_a_2237_ = v___x_2246_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
return v___x_2251_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__1(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0);
v___x_2253_ = lean_unsigned_to_nat(0u);
v___x_2254_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
lean_ctor_set(v___x_2254_, 2, v___x_2253_);
lean_ctor_set(v___x_2254_, 3, v___x_2253_);
lean_ctor_set(v___x_2254_, 4, v___x_2252_);
lean_ctor_set(v___x_2254_, 5, v___x_2252_);
lean_ctor_set(v___x_2254_, 6, v___x_2252_);
lean_ctor_set(v___x_2254_, 7, v___x_2252_);
lean_ctor_set(v___x_2254_, 8, v___x_2252_);
lean_ctor_set(v___x_2254_, 9, v___x_2252_);
lean_ctor_set(v___x_2254_, 10, v___x_2252_);
return v___x_2254_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__2(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2255_ = lean_box(1);
v___x_2256_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3);
v___x_2257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0);
v___x_2258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set(v___x_2258_, 1, v___x_2256_);
lean_ctor_set(v___x_2258_, 2, v___x_2255_);
return v___x_2258_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4(void){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__3));
v___x_2261_ = l_Lean_stringToMessageData(v___x_2260_);
return v___x_2261_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__6(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__5));
v___x_2264_ = l_Lean_stringToMessageData(v___x_2263_);
return v___x_2264_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__8(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__7));
v___x_2267_ = l_Lean_stringToMessageData(v___x_2266_);
return v___x_2267_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__10(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__9));
v___x_2270_ = l_Lean_stringToMessageData(v___x_2269_);
return v___x_2270_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__12(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__11));
v___x_2273_ = l_Lean_stringToMessageData(v___x_2272_);
return v___x_2273_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__14(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__13));
v___x_2276_ = l_Lean_stringToMessageData(v___x_2275_);
return v___x_2276_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__16(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__15));
v___x_2279_ = l_Lean_stringToMessageData(v___x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg(lean_object* v_msg_2280_, lean_object* v_declHint_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v_env_2286_; uint8_t v___x_2287_; 
v___x_2284_ = lean_box(0);
v___x_2285_ = lean_st_ref_get(v___y_2282_);
v_env_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc_ref(v_env_2286_);
lean_dec(v___x_2285_);
v___x_2287_ = l_Lean_Name_isAnonymous(v_declHint_2281_);
if (v___x_2287_ == 0)
{
uint8_t v_isExporting_2288_; 
v_isExporting_2288_ = lean_ctor_get_uint8(v_env_2286_, sizeof(void*)*13);
if (v_isExporting_2288_ == 0)
{
lean_object* v___x_2289_; 
lean_dec_ref(v_env_2286_);
lean_dec(v_declHint_2281_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v_msg_2280_);
return v___x_2289_;
}
else
{
lean_object* v___x_2290_; uint8_t v___x_2291_; 
lean_inc_ref(v_env_2286_);
v___x_2290_ = l_Lean_Environment_setExporting(v_env_2286_, v___x_2287_);
lean_inc(v_declHint_2281_);
lean_inc_ref(v___x_2290_);
v___x_2291_ = l_Lean_Environment_contains(v___x_2290_, v_declHint_2281_, v_isExporting_2288_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; 
lean_dec_ref(v___x_2290_);
lean_dec_ref(v_env_2286_);
lean_dec(v_declHint_2281_);
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v_msg_2280_);
return v___x_2292_;
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v_c_2298_; lean_object* v___x_2299_; 
v___x_2293_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__1);
v___x_2294_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__2);
v___x_2295_ = l_Lean_Options_empty;
lean_inc_ref(v___x_2290_);
v___x_2296_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2290_);
lean_ctor_set(v___x_2296_, 1, v___x_2293_);
lean_ctor_set(v___x_2296_, 2, v___x_2294_);
lean_ctor_set(v___x_2296_, 3, v___x_2295_);
lean_inc(v_declHint_2281_);
v___x_2297_ = l_Lean_MessageData_ofConstName(v_declHint_2281_, v___x_2287_);
v_c_2298_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2298_, 0, v___x_2296_);
lean_ctor_set(v_c_2298_, 1, v___x_2297_);
v___x_2299_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_2290_, v_declHint_2281_);
lean_dec_ref(v___x_2290_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
lean_dec_ref(v_env_2286_);
lean_dec(v_declHint_2281_);
v___x_2300_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
lean_ctor_set(v___x_2301_, 1, v_c_2298_);
v___x_2302_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__6);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = l_Lean_MessageData_note(v___x_2303_);
v___x_2305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2305_, 0, v_msg_2280_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
else
{
lean_object* v_val_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2341_; 
v_val_2307_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2309_ = v___x_2299_;
v_isShared_2310_ = v_isSharedCheck_2341_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_val_2307_);
lean_dec(v___x_2299_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2341_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v_moduleNames_2312_; lean_object* v_mod_2313_; uint8_t v___x_2314_; 
v___x_2311_ = l_Lean_Environment_header(v_env_2286_);
lean_dec_ref(v_env_2286_);
v_moduleNames_2312_ = lean_ctor_get(v___x_2311_, 4);
lean_inc_ref(v_moduleNames_2312_);
lean_dec_ref(v___x_2311_);
v_mod_2313_ = lean_array_get(v___x_2284_, v_moduleNames_2312_, v_val_2307_);
lean_dec(v_val_2307_);
lean_dec_ref(v_moduleNames_2312_);
v___x_2314_ = l_Lean_isPrivateName(v_declHint_2281_);
lean_dec(v_declHint_2281_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2315_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__8);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
lean_ctor_set(v___x_2316_, 1, v_c_2298_);
v___x_2317_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__10);
v___x_2318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = l_Lean_MessageData_ofName(v_mod_2313_);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2318_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__12);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = l_Lean_MessageData_note(v___x_2322_);
v___x_2324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2324_, 0, v_msg_2280_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set_tag(v___x_2309_, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2324_);
v___x_2326_ = v___x_2309_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2328_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4);
v___x_2329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v_c_2298_);
v___x_2330_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__14);
v___x_2331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = l_Lean_MessageData_ofName(v_mod_2313_);
v___x_2333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__16);
v___x_2335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = l_Lean_MessageData_note(v___x_2335_);
v___x_2337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2337_, 0, v_msg_2280_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set_tag(v___x_2309_, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2337_);
v___x_2339_ = v___x_2309_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2342_; 
lean_dec_ref(v_env_2286_);
lean_dec(v_declHint_2281_);
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v_msg_2280_);
return v___x_2342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___boxed(lean_object* v_msg_2343_, lean_object* v_declHint_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg(v_msg_2343_, v_declHint_2344_, v___y_2345_);
lean_dec(v___y_2345_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25(lean_object* v_msg_2348_, lean_object* v_declHint_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___x_2357_; lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2367_; 
v___x_2357_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg(v_msg_2348_, v_declHint_2349_, v___y_2355_);
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2360_ = v___x_2357_;
v_isShared_2361_ = v_isSharedCheck_2367_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2357_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2367_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2362_ = l_Lean_unknownIdentifierMessageTag;
v___x_2363_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
lean_ctor_set(v___x_2363_, 1, v_a_2358_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2363_);
v___x_2365_ = v___x_2360_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25___boxed(lean_object* v_msg_2368_, lean_object* v_declHint_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25(v_msg_2368_, v_declHint_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___redArg(lean_object* v_ref_2378_, lean_object* v_msg_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_toCold_2387_; lean_object* v_currRecDepth_2388_; lean_object* v_ref_2389_; uint16_t v_optionFlags_2390_; uint8_t v_suppressElabErrors_2391_; uint8_t v_checkDeprecated_2392_; uint8_t v_isRecordingDeps_2393_; lean_object* v_ref_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_toCold_2387_ = lean_ctor_get(v___y_2384_, 0);
v_currRecDepth_2388_ = lean_ctor_get(v___y_2384_, 1);
v_ref_2389_ = lean_ctor_get(v___y_2384_, 2);
v_optionFlags_2390_ = lean_ctor_get_uint16(v___y_2384_, sizeof(void*)*3);
v_suppressElabErrors_2391_ = lean_ctor_get_uint8(v___y_2384_, sizeof(void*)*3 + 2);
v_checkDeprecated_2392_ = lean_ctor_get_uint8(v___y_2384_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2393_ = lean_ctor_get_uint8(v___y_2384_, sizeof(void*)*3 + 4);
v_ref_2394_ = l_Lean_replaceRef(v_ref_2378_, v_ref_2389_);
lean_inc(v_currRecDepth_2388_);
lean_inc_ref(v_toCold_2387_);
v___x_2395_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2395_, 0, v_toCold_2387_);
lean_ctor_set(v___x_2395_, 1, v_currRecDepth_2388_);
lean_ctor_set(v___x_2395_, 2, v_ref_2394_);
lean_ctor_set_uint16(v___x_2395_, sizeof(void*)*3, v_optionFlags_2390_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*3 + 2, v_suppressElabErrors_2391_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*3 + 3, v_checkDeprecated_2392_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*3 + 4, v_isRecordingDeps_2393_);
v___x_2396_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___x_2395_, v___y_2385_);
lean_dec_ref_known(v___x_2395_, 3);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___redArg___boxed(lean_object* v_ref_2397_, lean_object* v_msg_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___redArg(v_ref_2397_, v_msg_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v_ref_2397_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___redArg(lean_object* v_ref_2407_, lean_object* v_msg_2408_, lean_object* v_declHint_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v___x_2417_; lean_object* v_a_2418_; lean_object* v___x_2419_; 
v___x_2417_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25(v_msg_2408_, v_declHint_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref(v___x_2417_);
v___x_2419_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___redArg(v_ref_2407_, v_a_2418_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___redArg___boxed(lean_object* v_ref_2420_, lean_object* v_msg_2421_, lean_object* v_declHint_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___redArg(v_ref_2420_, v_msg_2421_, v_declHint_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v_ref_2420_);
return v_res_2430_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__1(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__0));
v___x_2433_ = l_Lean_stringToMessageData(v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg(lean_object* v_ref_2434_, lean_object* v_constName_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; uint8_t v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2443_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__1);
v___x_2444_ = 0;
lean_inc(v_constName_2435_);
v___x_2445_ = l_Lean_MessageData_ofConstName(v_constName_2435_, v___x_2444_);
v___x_2446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2443_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___redArg(v_ref_2434_, v___x_2448_, v_constName_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___boxed(lean_object* v_ref_2450_, lean_object* v_constName_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg(v_ref_2450_, v_constName_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v_ref_2450_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___redArg(lean_object* v_constName_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_ref_2468_; lean_object* v___x_2469_; 
v_ref_2468_ = lean_ctor_get(v___y_2465_, 2);
v___x_2469_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg(v_ref_2468_, v_constName_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___redArg___boxed(lean_object* v_constName_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___redArg(v_constName_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(lean_object* v_constName_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v___x_2487_; lean_object* v_env_2488_; uint8_t v___x_2489_; lean_object* v___x_2490_; 
v___x_2487_ = lean_st_ref_get(v___y_2485_);
v_env_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc_ref(v_env_2488_);
lean_dec(v___x_2487_);
v___x_2489_ = 0;
lean_inc(v_constName_2479_);
v___x_2490_ = l_Lean_Environment_findConstVal_x3f(v_env_2488_, v_constName_2479_, v___x_2489_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___redArg(v_constName_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
return v___x_2491_;
}
else
{
lean_object* v_val_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_dec(v_constName_2479_);
v_val_2492_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2490_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_val_2492_);
lean_dec(v___x_2490_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
lean_ctor_set_tag(v___x_2494_, 0);
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_val_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14___boxed(lean_object* v_constName_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(lean_object* v_constName_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v___x_2517_; 
lean_inc(v_constName_2509_);
v___x_2517_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2529_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2529_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2529_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v_levelParams_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2527_; 
v_levelParams_2522_ = lean_ctor_get(v_a_2518_, 1);
lean_inc(v_levelParams_2522_);
lean_dec(v_a_2518_);
v___x_2523_ = lean_box(0);
v___x_2524_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(v_levelParams_2522_, v___x_2523_);
v___x_2525_ = l_Lean_mkConst(v_constName_2509_, v___x_2524_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2525_);
v___x_2527_ = v___x_2520_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2525_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec(v_constName_2509_);
v_a_2530_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2517_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2517_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_constName_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_constName_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(uint8_t v___x_2547_, lean_object* v_declName_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_ref_2556_; lean_object* v___x_2557_; 
v_ref_2556_ = lean_ctor_get(v___y_2553_, 2);
v___x_2557_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_declName_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___x_2557_, 1);
v___x_2559_ = lean_box(0);
lean_inc(v_ref_2556_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
lean_ctor_set(v___x_2560_, 1, v_ref_2556_);
v___x_2561_ = lean_unsigned_to_nat(32u);
v___x_2562_ = lean_mk_empty_array_with_capacity(v___x_2561_);
lean_dec_ref(v___x_2562_);
v___x_2563_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4);
v___x_2564_ = lean_box(0);
v___x_2565_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2565_, 0, v___x_2560_);
lean_ctor_set(v___x_2565_, 1, v___x_2563_);
lean_ctor_set(v___x_2565_, 2, v___x_2564_);
lean_ctor_set(v___x_2565_, 3, v_a_2558_);
lean_ctor_set_uint8(v___x_2565_, sizeof(void*)*4, v___x_2547_);
lean_ctor_set_uint8(v___x_2565_, sizeof(void*)*4 + 1, v___x_2547_);
v___x_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
v___x_2567_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v___x_2566_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
return v___x_2567_;
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
v_a_2568_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2557_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2557_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v___x_2576_, lean_object* v_declName_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
uint8_t v___x_17405__boxed_2585_; lean_object* v_res_2586_; 
v___x_17405__boxed_2585_ = lean_unbox(v___x_2576_);
v_res_2586_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(v___x_17405__boxed_2585_, v_declName_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(lean_object* v___f_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v___x_2595_; lean_object* v_env_2596_; lean_object* v___x_2597_; 
v___x_2595_ = lean_st_ref_get(v___y_2593_);
v_env_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc_ref(v_env_2596_);
lean_dec(v___x_2595_);
v___x_2597_ = lean_apply_8(v___f_2587_, v_env_2596_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, lean_box(0));
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed(lean_object* v___f_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(v___f_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
return v_res_2606_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0);
v___x_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17___redArg();
return v___x_2611_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__4(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = lean_unsigned_to_nat(0u);
v___x_2615_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
lean_ctor_set(v___x_2616_, 2, v___x_2614_);
return v___x_2616_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2617_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__4, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__4_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__4);
v___x_2618_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
v___x_2619_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2620_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
v___x_2621_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
lean_ctor_set(v___x_2621_, 1, v___x_2619_);
lean_ctor_set(v___x_2621_, 2, v___x_2618_);
lean_ctor_set(v___x_2621_, 3, v___x_2619_);
lean_ctor_set(v___x_2621_, 4, v___x_2619_);
lean_ctor_set(v___x_2621_, 5, v___x_2619_);
lean_ctor_set(v___x_2621_, 6, v___x_2619_);
lean_ctor_set(v___x_2621_, 7, v___x_2617_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(lean_object* v_env_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; lean_object* v_nextMacroScope_2627_; lean_object* v_ngen_2628_; lean_object* v_auxDeclNGen_2629_; lean_object* v_traceState_2630_; lean_object* v_recordedDeps_2631_; lean_object* v_messages_2632_; lean_object* v_infoState_2633_; lean_object* v_snapshotTasks_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2660_; 
v___x_2626_ = lean_st_ref_take(v___y_2624_);
v_nextMacroScope_2627_ = lean_ctor_get(v___x_2626_, 1);
v_ngen_2628_ = lean_ctor_get(v___x_2626_, 2);
v_auxDeclNGen_2629_ = lean_ctor_get(v___x_2626_, 3);
v_traceState_2630_ = lean_ctor_get(v___x_2626_, 4);
v_recordedDeps_2631_ = lean_ctor_get(v___x_2626_, 6);
v_messages_2632_ = lean_ctor_get(v___x_2626_, 7);
v_infoState_2633_ = lean_ctor_get(v___x_2626_, 8);
v_snapshotTasks_2634_ = lean_ctor_get(v___x_2626_, 9);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; lean_object* v_unused_2662_; 
v_unused_2661_ = lean_ctor_get(v___x_2626_, 5);
lean_dec(v_unused_2661_);
v_unused_2662_ = lean_ctor_get(v___x_2626_, 0);
lean_dec(v_unused_2662_);
v___x_2636_ = v___x_2626_;
v_isShared_2637_ = v_isSharedCheck_2660_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_snapshotTasks_2634_);
lean_inc(v_infoState_2633_);
lean_inc(v_messages_2632_);
lean_inc(v_recordedDeps_2631_);
lean_inc(v_traceState_2630_);
lean_inc(v_auxDeclNGen_2629_);
lean_inc(v_ngen_2628_);
lean_inc(v_nextMacroScope_2627_);
lean_dec(v___x_2626_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2660_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
v___x_2638_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 5, v___x_2638_);
lean_ctor_set(v___x_2636_, 0, v_env_2622_);
v___x_2640_ = v___x_2636_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_env_2622_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v_nextMacroScope_2627_);
lean_ctor_set(v_reuseFailAlloc_2659_, 2, v_ngen_2628_);
lean_ctor_set(v_reuseFailAlloc_2659_, 3, v_auxDeclNGen_2629_);
lean_ctor_set(v_reuseFailAlloc_2659_, 4, v_traceState_2630_);
lean_ctor_set(v_reuseFailAlloc_2659_, 5, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2659_, 6, v_recordedDeps_2631_);
lean_ctor_set(v_reuseFailAlloc_2659_, 7, v_messages_2632_);
lean_ctor_set(v_reuseFailAlloc_2659_, 8, v_infoState_2633_);
lean_ctor_set(v_reuseFailAlloc_2659_, 9, v_snapshotTasks_2634_);
v___x_2640_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v_mctx_2643_; lean_object* v_zetaDeltaFVarIds_2644_; lean_object* v_postponed_2645_; lean_object* v_diag_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2657_; 
v___x_2641_ = lean_st_ref_put(v___y_2624_, v___x_2640_);
v___x_2642_ = lean_st_ref_take(v___y_2623_);
v_mctx_2643_ = lean_ctor_get(v___x_2642_, 0);
v_zetaDeltaFVarIds_2644_ = lean_ctor_get(v___x_2642_, 2);
v_postponed_2645_ = lean_ctor_get(v___x_2642_, 3);
v_diag_2646_ = lean_ctor_get(v___x_2642_, 4);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2657_ == 0)
{
lean_object* v_unused_2658_; 
v_unused_2658_ = lean_ctor_get(v___x_2642_, 1);
lean_dec(v_unused_2658_);
v___x_2648_ = v___x_2642_;
v_isShared_2649_ = v_isSharedCheck_2657_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_diag_2646_);
lean_inc(v_postponed_2645_);
lean_inc(v_zetaDeltaFVarIds_2644_);
lean_inc(v_mctx_2643_);
lean_dec(v___x_2642_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2657_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2650_ = lean_box(0);
v___x_2651_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__5, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__5_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__5);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 1, v___x_2651_);
v___x_2653_ = v___x_2648_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_mctx_2643_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2656_, 2, v_zetaDeltaFVarIds_2644_);
lean_ctor_set(v_reuseFailAlloc_2656_, 3, v_postponed_2645_);
lean_ctor_set(v_reuseFailAlloc_2656_, 4, v_diag_2646_);
v___x_2653_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = lean_st_ref_put(v___y_2623_, v___x_2653_);
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2650_);
return v___x_2655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___boxed(lean_object* v_env_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec(v___y_2664_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(lean_object* v_env_2668_, lean_object* v_x_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v___x_2677_; lean_object* v_env_2678_; lean_object* v_a_2680_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2677_ = lean_st_ref_get(v___y_2675_);
v_env_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc_ref(v_env_2678_);
lean_dec(v___x_2677_);
v___x_2690_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2668_, v___y_2673_, v___y_2675_);
lean_dec_ref(v___x_2690_);
lean_inc(v___y_2675_);
lean_inc_ref(v___y_2674_);
lean_inc(v___y_2673_);
lean_inc_ref(v___y_2672_);
lean_inc(v___y_2671_);
lean_inc_ref(v___y_2670_);
v___x_2691_ = lean_apply_7(v_x_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, lean_box(0));
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2691_, 1);
v___x_2693_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2678_, v___y_2673_, v___y_2675_);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2700_ == 0)
{
lean_object* v_unused_2701_; 
v_unused_2701_ = lean_ctor_get(v___x_2693_, 0);
lean_dec(v_unused_2701_);
v___x_2695_ = v___x_2693_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_dec(v___x_2693_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v_a_2692_);
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2692_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
else
{
lean_object* v_a_2702_; 
v_a_2702_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2691_, 1);
v_a_2680_ = v_a_2702_;
goto v___jp_2679_;
}
v___jp_2679_:
{
lean_object* v___x_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
v___x_2681_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2678_, v___y_2673_, v___y_2675_);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; 
v_unused_2689_ = lean_ctor_get(v___x_2681_, 0);
lean_dec(v_unused_2689_);
v___x_2683_ = v___x_2681_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_dec(v___x_2681_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
lean_ctor_set_tag(v___x_2683_, 1);
lean_ctor_set(v___x_2683_, 0, v_a_2680_);
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2680_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_env_2703_, lean_object* v_x_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2703_, v_x_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(lean_object* v_declName_2713_, lean_object* v_env_2714_, lean_object* v_addInfo_2715_, lean_object* v_____r_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_privateToUserName_x3f(v_declName_2713_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_dec_ref(v_addInfo_2715_);
lean_dec_ref(v_env_2714_);
v___x_2725_ = lean_box(0);
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
return v___x_2726_;
}
else
{
lean_object* v_val_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2744_; 
v_val_2727_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2729_ = v___x_2724_;
v_isShared_2730_ = v_isSharedCheck_2744_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_val_2727_);
lean_dec(v___x_2724_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2744_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
uint8_t v___x_2731_; uint8_t v___x_2732_; 
v___x_2731_ = 1;
lean_inc(v_val_2727_);
v___x_2732_ = l_Lean_Environment_contains(v_env_2714_, v_val_2727_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; lean_object* v___x_2735_; 
lean_dec(v_val_2727_);
lean_dec_ref(v_addInfo_2715_);
v___x_2733_ = lean_box(0);
if (v_isShared_2730_ == 0)
{
lean_ctor_set_tag(v___x_2729_, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2733_);
v___x_2735_ = v___x_2729_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
else
{
lean_object* v___x_2737_; 
lean_del_object(v___x_2729_);
lean_inc(v___y_2722_);
lean_inc_ref(v___y_2721_);
lean_inc(v___y_2720_);
lean_inc_ref(v___y_2719_);
lean_inc(v___y_2718_);
lean_inc_ref(v___y_2717_);
lean_inc(v_val_2727_);
v___x_2737_ = lean_apply_8(v_addInfo_2715_, v_val_2727_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, lean_box(0));
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
lean_dec_ref_known(v___x_2737_, 1);
v___x_2738_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
v___x_2739_ = l_Lean_MessageData_ofConstName(v_val_2727_, v___x_2731_);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2742_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
return v___x_2743_;
}
else
{
lean_dec(v_val_2727_);
return v___x_2737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed(lean_object* v_declName_2745_, lean_object* v_env_2746_, lean_object* v_addInfo_2747_, lean_object* v_____r_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(v_declName_2745_, v_env_2746_, v_addInfo_2747_, v_____r_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(lean_object* v_addInfo_2757_, lean_object* v_declName_2758_, uint8_t v___x_2759_, uint8_t v___x_2760_, lean_object* v___f_2761_, lean_object* v_env_2762_, lean_object* v___f_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v___x_2771_; 
lean_inc(v___y_2769_);
lean_inc_ref(v___y_2768_);
lean_inc(v___y_2767_);
lean_inc_ref(v___y_2766_);
lean_inc(v___y_2765_);
lean_inc_ref(v___y_2764_);
lean_inc(v_declName_2758_);
v___x_2771_ = lean_apply_8(v_addInfo_2757_, v_declName_2758_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, lean_box(0));
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v___x_2772_; 
lean_dec_ref_known(v___x_2771_, 1);
lean_inc(v_declName_2758_);
v___x_2772_ = l_Lean_privateToUserName_x3f(v_declName_2758_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2773_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2774_ = l_Lean_MessageData_ofConstName(v_declName_2758_, v___x_2759_);
v___x_2775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2773_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
v___x_2776_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2777_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
return v___x_2778_;
}
else
{
lean_object* v_val_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
lean_dec(v_declName_2758_);
v_val_2779_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_val_2779_);
lean_dec_ref_known(v___x_2772_, 1);
v___x_2780_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1);
v___x_2781_ = l_Lean_MessageData_ofConstName(v_val_2779_, v___x_2759_);
v___x_2782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2780_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2782_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
v___x_2785_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2784_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
return v___x_2785_;
}
}
else
{
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v_declName_2758_);
return v___x_2771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed(lean_object* v_addInfo_2786_, lean_object* v_declName_2787_, lean_object* v___x_2788_, lean_object* v___x_2789_, lean_object* v___f_2790_, lean_object* v_env_2791_, lean_object* v___f_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
uint8_t v___x_17786__boxed_2800_; uint8_t v___x_17787__boxed_2801_; lean_object* v_res_2802_; 
v___x_17786__boxed_2800_ = lean_unbox(v___x_2788_);
v___x_17787__boxed_2801_ = lean_unbox(v___x_2789_);
v_res_2802_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(v_addInfo_2786_, v_declName_2787_, v___x_17786__boxed_2800_, v___x_17787__boxed_2801_, v___f_2790_, v_env_2791_, v___f_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec_ref(v___f_2792_);
lean_dec_ref(v_env_2791_);
lean_dec_ref(v___f_2790_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(lean_object* v_declName_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2814_; lean_object* v_env_2815_; uint8_t v___x_2816_; lean_object* v_addInfo_2817_; lean_object* v_env_2818_; lean_object* v___f_2819_; lean_object* v___f_2820_; lean_object* v___x_2821_; lean_object* v___f_2822_; uint8_t v___x_2823_; uint8_t v___x_2824_; 
v___x_2814_ = lean_st_ref_get(v___y_2812_);
v_env_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc_ref(v_env_2815_);
lean_dec(v___x_2814_);
v___x_2816_ = 0;
v_addInfo_2817_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0));
v_env_2818_ = l_Lean_Environment_setExporting(v_env_2815_, v___x_2816_);
lean_inc_ref_n(v_env_2818_, 4);
lean_inc_n(v_declName_2806_, 4);
v___f_2819_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed), 11, 3);
lean_closure_set(v___f_2819_, 0, v_declName_2806_);
lean_closure_set(v___f_2819_, 1, v_env_2818_);
lean_closure_set(v___f_2819_, 2, v_addInfo_2817_);
v___f_2820_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2820_, 0, v_env_2818_);
lean_closure_set(v___f_2820_, 1, v_declName_2806_);
lean_closure_set(v___f_2820_, 2, v___f_2819_);
lean_closure_set(v___f_2820_, 3, v_addInfo_2817_);
v___x_2821_ = lean_box(v___x_2816_);
lean_inc_ref(v___f_2820_);
v___f_2822_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed), 12, 4);
lean_closure_set(v___f_2822_, 0, v_declName_2806_);
lean_closure_set(v___f_2822_, 1, v___x_2821_);
lean_closure_set(v___f_2822_, 2, v___f_2820_);
lean_closure_set(v___f_2822_, 3, v_env_2818_);
v___x_2823_ = 1;
v___x_2824_ = l_Lean_Environment_contains(v_env_2818_, v_declName_2806_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___f_2825_; lean_object* v___x_2826_; 
lean_dec_ref(v___f_2820_);
lean_dec(v_declName_2806_);
v___f_2825_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed), 8, 1);
lean_closure_set(v___f_2825_, 0, v___f_2822_);
v___x_2826_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2818_, v___f_2825_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
return v___x_2826_;
}
else
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___f_2829_; lean_object* v___x_2830_; 
v___x_2827_ = lean_box(v___x_2823_);
v___x_2828_ = lean_box(v___x_2816_);
lean_inc_ref(v_env_2818_);
v___f_2829_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed), 14, 7);
lean_closure_set(v___f_2829_, 0, v_addInfo_2817_);
lean_closure_set(v___f_2829_, 1, v_declName_2806_);
lean_closure_set(v___f_2829_, 2, v___x_2827_);
lean_closure_set(v___f_2829_, 3, v___x_2828_);
lean_closure_set(v___f_2829_, 4, v___f_2820_);
lean_closure_set(v___f_2829_, 5, v_env_2818_);
lean_closure_set(v___f_2829_, 6, v___f_2822_);
v___x_2830_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2818_, v___f_2829_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
return v___x_2830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___boxed(lean_object* v_declName_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(lean_object* v_modifiers_2840_, lean_object* v_declName_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_declName_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___x_2914_; lean_object* v_env_2915_; uint8_t v_visibility_2916_; uint8_t v___x_2917_; 
v___x_2914_ = lean_st_ref_get(v___y_2847_);
v_env_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc_ref(v_env_2915_);
lean_dec(v___x_2914_);
v_visibility_2916_ = lean_ctor_get_uint8(v_modifiers_2840_, sizeof(void*)*3);
v___x_2917_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_2915_, v_visibility_2916_);
lean_dec_ref(v_env_2915_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; lean_object* v_env_2919_; lean_object* v_declName_2920_; 
v___x_2918_ = lean_st_ref_get(v___y_2847_);
v_env_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc_ref(v_env_2919_);
lean_dec(v___x_2918_);
v_declName_2920_ = l_Lean_mkPrivateName(v_env_2919_, v_declName_2841_);
lean_dec_ref(v_env_2919_);
v_declName_2850_ = v_declName_2920_;
v___y_2851_ = v___y_2842_;
v___y_2852_ = v___y_2843_;
v___y_2853_ = v___y_2844_;
v___y_2854_ = v___y_2845_;
v___y_2855_ = v___y_2846_;
v___y_2856_ = v___y_2847_;
goto v___jp_2849_;
}
else
{
v_declName_2850_ = v_declName_2841_;
v___y_2851_ = v___y_2842_;
v___y_2852_ = v___y_2843_;
v___y_2853_ = v___y_2844_;
v___y_2854_ = v___y_2845_;
v___y_2855_ = v___y_2846_;
v___y_2856_ = v___y_2847_;
goto v___jp_2849_;
}
v___jp_2849_:
{
lean_object* v___x_2857_; 
lean_inc(v_declName_2850_);
v___x_2857_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2904_; 
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2904_ == 0)
{
lean_object* v_unused_2905_; 
v_unused_2905_ = lean_ctor_get(v___x_2857_, 0);
lean_dec(v_unused_2905_);
v___x_2859_ = v___x_2857_;
v_isShared_2860_ = v_isSharedCheck_2904_;
goto v_resetjp_2858_;
}
else
{
lean_dec(v___x_2857_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2904_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
uint8_t v_isProtected_2861_; 
v_isProtected_2861_ = lean_ctor_get_uint8(v_modifiers_2840_, sizeof(void*)*3 + 1);
if (v_isProtected_2861_ == 0)
{
lean_object* v___x_2863_; 
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v_declName_2850_);
v___x_2863_ = v___x_2859_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_declName_2850_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
else
{
lean_object* v___x_2865_; lean_object* v_env_2866_; lean_object* v_nextMacroScope_2867_; lean_object* v_ngen_2868_; lean_object* v_auxDeclNGen_2869_; lean_object* v_traceState_2870_; lean_object* v_recordedDeps_2871_; lean_object* v_messages_2872_; lean_object* v_infoState_2873_; lean_object* v_snapshotTasks_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2902_; 
v___x_2865_ = lean_st_ref_take(v___y_2856_);
v_env_2866_ = lean_ctor_get(v___x_2865_, 0);
v_nextMacroScope_2867_ = lean_ctor_get(v___x_2865_, 1);
v_ngen_2868_ = lean_ctor_get(v___x_2865_, 2);
v_auxDeclNGen_2869_ = lean_ctor_get(v___x_2865_, 3);
v_traceState_2870_ = lean_ctor_get(v___x_2865_, 4);
v_recordedDeps_2871_ = lean_ctor_get(v___x_2865_, 6);
v_messages_2872_ = lean_ctor_get(v___x_2865_, 7);
v_infoState_2873_ = lean_ctor_get(v___x_2865_, 8);
v_snapshotTasks_2874_ = lean_ctor_get(v___x_2865_, 9);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2902_ == 0)
{
lean_object* v_unused_2903_; 
v_unused_2903_ = lean_ctor_get(v___x_2865_, 5);
lean_dec(v_unused_2903_);
v___x_2876_ = v___x_2865_;
v_isShared_2877_ = v_isSharedCheck_2902_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_snapshotTasks_2874_);
lean_inc(v_infoState_2873_);
lean_inc(v_messages_2872_);
lean_inc(v_recordedDeps_2871_);
lean_inc(v_traceState_2870_);
lean_inc(v_auxDeclNGen_2869_);
lean_inc(v_ngen_2868_);
lean_inc(v_nextMacroScope_2867_);
lean_inc(v_env_2866_);
lean_dec(v___x_2865_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2902_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
lean_inc(v_declName_2850_);
v___x_2878_ = l_Lean_addProtected(v_env_2866_, v_declName_2850_);
v___x_2879_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 5, v___x_2879_);
lean_ctor_set(v___x_2876_, 0, v___x_2878_);
v___x_2881_ = v___x_2876_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2878_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_nextMacroScope_2867_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v_ngen_2868_);
lean_ctor_set(v_reuseFailAlloc_2901_, 3, v_auxDeclNGen_2869_);
lean_ctor_set(v_reuseFailAlloc_2901_, 4, v_traceState_2870_);
lean_ctor_set(v_reuseFailAlloc_2901_, 5, v___x_2879_);
lean_ctor_set(v_reuseFailAlloc_2901_, 6, v_recordedDeps_2871_);
lean_ctor_set(v_reuseFailAlloc_2901_, 7, v_messages_2872_);
lean_ctor_set(v_reuseFailAlloc_2901_, 8, v_infoState_2873_);
lean_ctor_set(v_reuseFailAlloc_2901_, 9, v_snapshotTasks_2874_);
v___x_2881_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v_mctx_2884_; lean_object* v_zetaDeltaFVarIds_2885_; lean_object* v_postponed_2886_; lean_object* v_diag_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2899_; 
v___x_2882_ = lean_st_ref_put(v___y_2856_, v___x_2881_);
v___x_2883_ = lean_st_ref_take(v___y_2854_);
v_mctx_2884_ = lean_ctor_get(v___x_2883_, 0);
v_zetaDeltaFVarIds_2885_ = lean_ctor_get(v___x_2883_, 2);
v_postponed_2886_ = lean_ctor_get(v___x_2883_, 3);
v_diag_2887_ = lean_ctor_get(v___x_2883_, 4);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2899_ == 0)
{
lean_object* v_unused_2900_; 
v_unused_2900_ = lean_ctor_get(v___x_2883_, 1);
lean_dec(v_unused_2900_);
v___x_2889_ = v___x_2883_;
v_isShared_2890_ = v_isSharedCheck_2899_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_diag_2887_);
lean_inc(v_postponed_2886_);
lean_inc(v_zetaDeltaFVarIds_2885_);
lean_inc(v_mctx_2884_);
lean_dec(v___x_2883_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2899_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; lean_object* v___x_2893_; 
v___x_2891_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__5, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__5_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__5);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 1, v___x_2891_);
v___x_2893_ = v___x_2889_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_mctx_2884_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v___x_2891_);
lean_ctor_set(v_reuseFailAlloc_2898_, 2, v_zetaDeltaFVarIds_2885_);
lean_ctor_set(v_reuseFailAlloc_2898_, 3, v_postponed_2886_);
lean_ctor_set(v_reuseFailAlloc_2898_, 4, v_diag_2887_);
v___x_2893_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2894_ = lean_st_ref_put(v___y_2854_, v___x_2893_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v_declName_2850_);
v___x_2896_ = v___x_2859_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_declName_2850_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
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
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_declName_2850_);
v_a_2906_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2857_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2857_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4___boxed(lean_object* v_modifiers_2921_, lean_object* v_declName_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2921_, v_declName_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec_ref(v_modifiers_2921_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(lean_object* v_pre_2931_, lean_object* v_declName_2932_, lean_object* v_as_2933_, size_t v_sz_2934_, size_t v_i_2935_, lean_object* v_b_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_a_2945_; uint8_t v___x_2949_; 
v___x_2949_ = lean_usize_dec_lt(v_i_2935_, v_sz_2934_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; 
lean_dec(v_declName_2932_);
lean_dec(v_pre_2931_);
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v_b_2936_);
return v___x_2950_;
}
else
{
lean_object* v___x_2951_; lean_object* v_a_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v___x_2951_ = lean_box(0);
v_a_2952_ = lean_array_uget_borrowed(v_as_2933_, v_i_2935_);
lean_inc(v_a_2952_);
lean_inc(v_pre_2931_);
v___x_2953_ = l_Lean_Name_append(v_pre_2931_, v_a_2952_);
v___x_2954_ = lean_name_eq(v___x_2953_, v_declName_2932_);
lean_dec(v___x_2953_);
if (v___x_2954_ == 0)
{
v_a_2945_ = v___x_2951_;
goto v___jp_2944_;
}
else
{
lean_object* v___x_2955_; uint8_t v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2955_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_2956_ = 0;
lean_inc(v_declName_2932_);
v___x_2957_ = l_Lean_MessageData_ofConstName(v_declName_2932_, v___x_2956_);
v___x_2958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2955_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2959_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2958_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
lean_inc(v_pre_2931_);
v___x_2961_ = l_Lean_MessageData_ofName(v_pre_2931_);
v___x_2962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2960_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_2964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2962_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
lean_inc(v_a_2952_);
v___x_2965_ = l_Lean_MessageData_ofName(v_a_2952_);
v___x_2966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2964_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
v___x_2967_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2966_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2968_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_dec_ref_known(v___x_2969_, 1);
v_a_2945_ = v___x_2951_;
goto v___jp_2944_;
}
else
{
lean_dec(v_declName_2932_);
lean_dec(v_pre_2931_);
return v___x_2969_;
}
}
}
v___jp_2944_:
{
size_t v___x_2946_; size_t v___x_2947_; 
v___x_2946_ = ((size_t)1ULL);
v___x_2947_ = lean_usize_add(v_i_2935_, v___x_2946_);
v_i_2935_ = v___x_2947_;
v_b_2936_ = v_a_2945_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6___boxed(lean_object* v_pre_2970_, lean_object* v_declName_2971_, lean_object* v_as_2972_, lean_object* v_sz_2973_, lean_object* v_i_2974_, lean_object* v_b_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
size_t v_sz_boxed_2983_; size_t v_i_boxed_2984_; lean_object* v_res_2985_; 
v_sz_boxed_2983_ = lean_unbox_usize(v_sz_2973_);
lean_dec(v_sz_2973_);
v_i_boxed_2984_ = lean_unbox_usize(v_i_2974_);
lean_dec(v_i_2974_);
v_res_2985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2970_, v_declName_2971_, v_as_2972_, v_sz_boxed_2983_, v_i_boxed_2984_, v_b_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec_ref(v_as_2972_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(lean_object* v_declName_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
if (lean_obj_tag(v_declName_2986_) == 1)
{
lean_object* v_pre_2994_; lean_object* v___x_2995_; lean_object* v_env_2996_; uint8_t v___x_2997_; 
v_pre_2994_ = lean_ctor_get(v_declName_2986_, 0);
lean_inc_n(v_pre_2994_, 2);
v___x_2995_ = lean_st_ref_get(v___y_2992_);
v_env_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc_ref(v_env_2996_);
lean_dec(v___x_2995_);
v___x_2997_ = l_Lean_isStructure(v_env_2996_, v_pre_2994_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
lean_dec_ref_known(v_declName_2986_, 2);
lean_dec(v_pre_2994_);
v___x_2998_ = lean_box(0);
v___x_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
return v___x_2999_;
}
else
{
lean_object* v___x_3000_; lean_object* v_env_3001_; lean_object* v_fieldNames_3002_; lean_object* v___x_3003_; size_t v_sz_3004_; size_t v___x_3005_; lean_object* v___x_3006_; 
v___x_3000_ = lean_st_ref_get(v___y_2992_);
v_env_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc_ref(v_env_3001_);
lean_dec(v___x_3000_);
lean_inc(v_pre_2994_);
v_fieldNames_3002_ = l_Lean_getStructureFieldsFlattened(v_env_3001_, v_pre_2994_, v___x_2997_);
v___x_3003_ = lean_box(0);
v_sz_3004_ = lean_array_size(v_fieldNames_3002_);
v___x_3005_ = ((size_t)0ULL);
v___x_3006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2994_, v_declName_2986_, v_fieldNames_3002_, v_sz_3004_, v___x_3005_, v___x_3003_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
lean_dec_ref(v_fieldNames_3002_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3013_ == 0)
{
lean_object* v_unused_3014_; 
v_unused_3014_ = lean_ctor_get(v___x_3006_, 0);
lean_dec(v_unused_3014_);
v___x_3008_ = v___x_3006_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_dec(v___x_3006_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 0, v___x_3003_);
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3003_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
else
{
return v___x_3006_;
}
}
}
else
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
lean_dec(v_declName_2986_);
v___x_3015_ = lean_box(0);
v___x_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
return v___x_3016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3___boxed(lean_object* v_declName_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v_declName_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(lean_object* v_currNamespace_3026_, lean_object* v_modifiers_3027_, lean_object* v_shortName_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3042_; lean_object* v_shortName_3043_; lean_object* v_currNamespace_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v_view_3104_; lean_object* v_name_3105_; lean_object* v_imported_3106_; lean_object* v_ctx_3107_; lean_object* v_scopes_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3166_; 
lean_inc(v_shortName_3028_);
v_view_3104_ = l_Lean_extractMacroScopes(v_shortName_3028_);
v_name_3105_ = lean_ctor_get(v_view_3104_, 0);
v_imported_3106_ = lean_ctor_get(v_view_3104_, 1);
v_ctx_3107_ = lean_ctor_get(v_view_3104_, 2);
v_scopes_3108_ = lean_ctor_get(v_view_3104_, 3);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_view_3104_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3110_ = v_view_3104_;
v_isShared_3111_ = v_isSharedCheck_3166_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_scopes_3108_);
lean_inc(v_ctx_3107_);
lean_inc(v_imported_3106_);
lean_inc(v_name_3105_);
lean_dec(v_view_3104_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3166_;
goto v_resetjp_3109_;
}
v___jp_3036_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___y_3037_);
lean_ctor_set(v___x_3039_, 1, v___y_3038_);
v___x_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
return v___x_3040_;
}
v___jp_3041_:
{
lean_object* v___x_3051_; 
lean_inc(v___y_3042_);
v___x_3051_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v___y_3042_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v___x_3052_; 
lean_dec_ref_known(v___x_3051_, 1);
v___x_3052_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_3027_, v___y_3042_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
if (lean_obj_tag(v___x_3052_) == 0)
{
uint8_t v_isProtected_3053_; 
v_isProtected_3053_ = lean_ctor_get_uint8(v_modifiers_3027_, sizeof(void*)*3 + 1);
if (v_isProtected_3053_ == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3062_; 
lean_dec(v_currNamespace_3044_);
v_a_3054_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3056_ = v___x_3052_;
v_isShared_3057_ = v_isSharedCheck_3062_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3052_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3062_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3060_; 
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v_a_3054_);
lean_ctor_set(v___x_3058_, 1, v_shortName_3043_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v___x_3058_);
v___x_3060_ = v___x_3056_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
else
{
if (lean_obj_tag(v_currNamespace_3044_) == 1)
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3075_; 
v_a_3063_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3065_ = v___x_3052_;
v_isShared_3066_ = v_isSharedCheck_3075_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3052_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3075_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v_str_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3073_; 
v_str_3067_ = lean_ctor_get(v_currNamespace_3044_, 1);
lean_inc_ref(v_str_3067_);
lean_dec_ref_known(v_currNamespace_3044_, 2);
v___x_3068_ = lean_box(0);
v___x_3069_ = l_Lean_Name_str___override(v___x_3068_, v_str_3067_);
v___x_3070_ = l_Lean_Name_append(v___x_3069_, v_shortName_3043_);
v___x_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3071_, 0, v_a_3063_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v___x_3071_);
v___x_3073_ = v___x_3065_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
else
{
lean_object* v_a_3076_; uint8_t v___x_3077_; 
lean_dec(v_currNamespace_3044_);
v_a_3076_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3076_);
lean_dec_ref_known(v___x_3052_, 1);
v___x_3077_ = l_Lean_Name_isAtomic(v_shortName_3043_);
if (v___x_3077_ == 0)
{
v___y_3037_ = v_a_3076_;
v___y_3038_ = v_shortName_3043_;
goto v___jp_3036_;
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec(v_a_3076_);
lean_dec(v_shortName_3043_);
v___x_3078_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_3079_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3078_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3079_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3079_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec(v_currNamespace_3044_);
lean_dec(v_shortName_3043_);
v_a_3088_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3052_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3052_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_currNamespace_3044_);
lean_dec(v_shortName_3043_);
lean_dec(v___y_3042_);
v_a_3096_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3051_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3051_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; uint8_t v_isRootName_3113_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; uint8_t v___x_3155_; 
v___x_3112_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_3113_ = l_Lean_Name_isPrefixOf(v___x_3112_, v_name_3105_);
v___x_3155_ = lean_name_eq(v_name_3105_, v___x_3112_);
if (v___x_3155_ == 0)
{
v___y_3142_ = v___y_3029_;
v___y_3143_ = v___y_3030_;
v___y_3144_ = v___y_3031_;
v___y_3145_ = v___y_3032_;
v___y_3146_ = v___y_3033_;
v___y_3147_ = v___y_3034_;
goto v___jp_3141_;
}
else
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_del_object(v___x_3110_);
lean_dec(v_scopes_3108_);
lean_dec(v_ctx_3107_);
lean_dec(v_imported_3106_);
lean_dec(v_name_3105_);
lean_dec(v_shortName_3028_);
lean_dec(v_currNamespace_3026_);
v___x_3156_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_3157_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3156_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3157_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
v___jp_3114_:
{
if (v_isRootName_3113_ == 0)
{
lean_dec(v_name_3105_);
v___y_3042_ = v___y_3121_;
v_shortName_3043_ = v_shortName_3028_;
v_currNamespace_3044_ = v_currNamespace_3026_;
v___y_3045_ = v___y_3119_;
v___y_3046_ = v___y_3117_;
v___y_3047_ = v___y_3116_;
v___y_3048_ = v___y_3118_;
v___y_3049_ = v___y_3115_;
v___y_3050_ = v___y_3120_;
goto v___jp_3041_;
}
else
{
lean_dec(v_shortName_3028_);
lean_dec(v_currNamespace_3026_);
if (lean_obj_tag(v_name_3105_) == 1)
{
lean_object* v_pre_3122_; lean_object* v_str_3123_; lean_object* v___x_3124_; lean_object* v_shortName_3125_; lean_object* v_currNamespace_3126_; 
v_pre_3122_ = lean_ctor_get(v_name_3105_, 0);
lean_inc(v_pre_3122_);
v_str_3123_ = lean_ctor_get(v_name_3105_, 1);
lean_inc_ref(v_str_3123_);
lean_dec_ref_known(v_name_3105_, 2);
v___x_3124_ = lean_box(0);
v_shortName_3125_ = l_Lean_Name_str___override(v___x_3124_, v_str_3123_);
v_currNamespace_3126_ = l_Lean_Name_replacePrefix(v_pre_3122_, v___x_3112_, v___x_3124_);
v___y_3042_ = v___y_3121_;
v_shortName_3043_ = v_shortName_3125_;
v_currNamespace_3044_ = v_currNamespace_3126_;
v___y_3045_ = v___y_3119_;
v___y_3046_ = v___y_3117_;
v___y_3047_ = v___y_3116_;
v___y_3048_ = v___y_3118_;
v___y_3049_ = v___y_3115_;
v___y_3050_ = v___y_3120_;
goto v___jp_3041_;
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec(v___y_3121_);
v___x_3127_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_3128_ = l_Lean_MessageData_ofName(v_name_3105_);
v___x_3129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3127_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_3131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3129_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v___x_3132_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3131_, v___y_3119_, v___y_3117_, v___y_3116_, v___y_3118_, v___y_3115_, v___y_3120_);
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3132_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3132_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
}
v___jp_3141_:
{
if (v_isRootName_3113_ == 0)
{
lean_object* v___x_3148_; 
lean_del_object(v___x_3110_);
lean_dec(v_scopes_3108_);
lean_dec(v_ctx_3107_);
lean_dec(v_imported_3106_);
lean_inc(v_shortName_3028_);
lean_inc(v_currNamespace_3026_);
v___x_3148_ = l_Lean_Name_append(v_currNamespace_3026_, v_shortName_3028_);
v___y_3115_ = v___y_3146_;
v___y_3116_ = v___y_3144_;
v___y_3117_ = v___y_3143_;
v___y_3118_ = v___y_3145_;
v___y_3119_ = v___y_3142_;
v___y_3120_ = v___y_3147_;
v___y_3121_ = v___x_3148_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3152_; 
v___x_3149_ = lean_box(0);
lean_inc(v_name_3105_);
v___x_3150_ = l_Lean_Name_replacePrefix(v_name_3105_, v___x_3112_, v___x_3149_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___x_3150_);
v___x_3152_ = v___x_3110_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3150_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_imported_3106_);
lean_ctor_set(v_reuseFailAlloc_3154_, 2, v_ctx_3107_);
lean_ctor_set(v_reuseFailAlloc_3154_, 3, v_scopes_3108_);
v___x_3152_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
lean_object* v___x_3153_; 
v___x_3153_ = l_Lean_MacroScopesView_review(v___x_3152_);
v___y_3115_ = v___y_3146_;
v___y_3116_ = v___y_3144_;
v___y_3117_ = v___y_3143_;
v___y_3118_ = v___y_3145_;
v___y_3119_ = v___y_3142_;
v___y_3120_ = v___y_3147_;
v___y_3121_ = v___x_3153_;
goto v___jp_3114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2___boxed(lean_object* v_currNamespace_3167_, lean_object* v_modifiers_3168_, lean_object* v_shortName_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3167_, v_modifiers_3168_, v_shortName_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec_ref(v_modifiers_3168_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(uint8_t v___x_3178_, lean_object* v_as_3179_, size_t v_i_3180_, size_t v_stop_3181_, lean_object* v_b_3182_){
_start:
{
lean_object* v___y_3184_; uint8_t v___x_3188_; 
v___x_3188_ = lean_usize_dec_eq(v_i_3180_, v_stop_3181_);
if (v___x_3188_ == 0)
{
lean_object* v_fst_3189_; uint8_t v___x_3190_; 
v_fst_3189_ = lean_ctor_get(v_b_3182_, 0);
v___x_3190_ = lean_unbox(v_fst_3189_);
if (v___x_3190_ == 0)
{
lean_object* v_snd_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3200_; 
v_snd_3191_ = lean_ctor_get(v_b_3182_, 1);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_b_3182_);
if (v_isSharedCheck_3200_ == 0)
{
lean_object* v_unused_3201_; 
v_unused_3201_ = lean_ctor_get(v_b_3182_, 0);
lean_dec(v_unused_3201_);
v___x_3193_ = v_b_3182_;
v_isShared_3194_ = v_isSharedCheck_3200_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_snd_3191_);
lean_dec(v_b_3182_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3200_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
uint8_t v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3198_; 
v___x_3195_ = 1;
v___x_3196_ = lean_box(v___x_3195_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3196_);
v___x_3198_ = v___x_3193_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_snd_3191_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
v___y_3184_ = v___x_3198_;
goto v___jp_3183_;
}
}
}
else
{
lean_object* v_snd_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3212_; 
v_snd_3202_ = lean_ctor_get(v_b_3182_, 1);
v_isSharedCheck_3212_ = !lean_is_exclusive(v_b_3182_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; 
v_unused_3213_ = lean_ctor_get(v_b_3182_, 0);
lean_dec(v_unused_3213_);
v___x_3204_ = v_b_3182_;
v_isShared_3205_ = v_isSharedCheck_3212_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_snd_3202_);
lean_dec(v_b_3182_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3212_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3210_; 
v___x_3206_ = lean_array_uget_borrowed(v_as_3179_, v_i_3180_);
lean_inc(v___x_3206_);
v___x_3207_ = lean_array_push(v_snd_3202_, v___x_3206_);
v___x_3208_ = lean_box(v___x_3178_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v___x_3207_);
lean_ctor_set(v___x_3204_, 0, v___x_3208_);
v___x_3210_ = v___x_3204_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3208_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v___x_3207_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
v___y_3184_ = v___x_3210_;
goto v___jp_3183_;
}
}
}
}
else
{
return v_b_3182_;
}
v___jp_3183_:
{
size_t v___x_3185_; size_t v___x_3186_; 
v___x_3185_ = ((size_t)1ULL);
v___x_3186_ = lean_usize_add(v_i_3180_, v___x_3185_);
v_i_3180_ = v___x_3186_;
v_b_3182_ = v___y_3184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4___boxed(lean_object* v___x_3214_, lean_object* v_as_3215_, lean_object* v_i_3216_, lean_object* v_stop_3217_, lean_object* v_b_3218_){
_start:
{
uint8_t v___x_18509__boxed_3219_; size_t v_i_boxed_3220_; size_t v_stop_boxed_3221_; lean_object* v_res_3222_; 
v___x_18509__boxed_3219_ = lean_unbox(v___x_3214_);
v_i_boxed_3220_ = lean_unbox_usize(v_i_3216_);
lean_dec(v_i_3216_);
v_stop_boxed_3221_ = lean_unbox_usize(v_stop_3217_);
lean_dec(v_stop_3217_);
v_res_3222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_18509__boxed_3219_, v_as_3215_, v_i_boxed_3220_, v_stop_boxed_3221_, v_b_3218_);
lean_dec_ref(v_as_3215_);
return v_res_3222_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(lean_object* v_a_3223_, lean_object* v_x_3224_){
_start:
{
if (lean_obj_tag(v_x_3224_) == 0)
{
uint8_t v___x_3225_; 
v___x_3225_ = 0;
return v___x_3225_;
}
else
{
lean_object* v_head_3226_; lean_object* v_tail_3227_; uint8_t v___x_3228_; 
v_head_3226_ = lean_ctor_get(v_x_3224_, 0);
v_tail_3227_ = lean_ctor_get(v_x_3224_, 1);
v___x_3228_ = lean_name_eq(v_a_3223_, v_head_3226_);
if (v___x_3228_ == 0)
{
v_x_3224_ = v_tail_3227_;
goto _start;
}
else
{
return v___x_3228_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_expandDeclId_spec__0___boxed(lean_object* v_a_3230_, lean_object* v_x_3231_){
_start:
{
uint8_t v_res_3232_; lean_object* v_r_3233_; 
v_res_3232_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_a_3230_, v_x_3231_);
lean_dec(v_x_3231_);
lean_dec(v_a_3230_);
v_r_3233_ = lean_box(v_res_3232_);
return v_r_3233_;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = ((lean_object*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0));
v___x_3236_ = l_Lean_stringToMessageData(v___x_3235_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(lean_object* v_u_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3245_ = lean_obj_once(&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1, &l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1);
v___x_3246_ = l_Lean_MessageData_ofName(v_u_3237_);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3249_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___boxed(lean_object* v_u_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(lean_object* v_as_3260_, size_t v_i_3261_, size_t v_stop_3262_, lean_object* v_b_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v_a_3272_; uint8_t v___x_3276_; 
v___x_3276_ = lean_usize_dec_eq(v_i_3261_, v_stop_3262_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; lean_object* v_id_3278_; uint8_t v___x_3279_; 
v___x_3277_ = lean_array_uget_borrowed(v_as_3260_, v_i_3261_);
v_id_3278_ = l_Lean_Syntax_getId(v___x_3277_);
v___x_3279_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_id_3278_, v_b_3263_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; 
v___x_3280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3280_, 0, v_id_3278_);
lean_ctor_set(v___x_3280_, 1, v_b_3263_);
v_a_3272_ = v___x_3280_;
goto v___jp_3271_;
}
else
{
lean_object* v_toCold_3281_; lean_object* v_currRecDepth_3282_; lean_object* v_ref_3283_; uint16_t v_optionFlags_3284_; uint8_t v_suppressElabErrors_3285_; uint8_t v_checkDeprecated_3286_; uint8_t v_isRecordingDeps_3287_; lean_object* v_ref_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec(v_b_3263_);
v_toCold_3281_ = lean_ctor_get(v___y_3268_, 0);
v_currRecDepth_3282_ = lean_ctor_get(v___y_3268_, 1);
v_ref_3283_ = lean_ctor_get(v___y_3268_, 2);
v_optionFlags_3284_ = lean_ctor_get_uint16(v___y_3268_, sizeof(void*)*3);
v_suppressElabErrors_3285_ = lean_ctor_get_uint8(v___y_3268_, sizeof(void*)*3 + 2);
v_checkDeprecated_3286_ = lean_ctor_get_uint8(v___y_3268_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3287_ = lean_ctor_get_uint8(v___y_3268_, sizeof(void*)*3 + 4);
v_ref_3288_ = l_Lean_replaceRef(v___x_3277_, v_ref_3283_);
lean_inc(v_currRecDepth_3282_);
lean_inc_ref(v_toCold_3281_);
v___x_3289_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3289_, 0, v_toCold_3281_);
lean_ctor_set(v___x_3289_, 1, v_currRecDepth_3282_);
lean_ctor_set(v___x_3289_, 2, v_ref_3288_);
lean_ctor_set_uint16(v___x_3289_, sizeof(void*)*3, v_optionFlags_3284_);
lean_ctor_set_uint8(v___x_3289_, sizeof(void*)*3 + 2, v_suppressElabErrors_3285_);
lean_ctor_set_uint8(v___x_3289_, sizeof(void*)*3 + 3, v_checkDeprecated_3286_);
lean_ctor_set_uint8(v___x_3289_, sizeof(void*)*3 + 4, v_isRecordingDeps_3287_);
v___x_3290_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_id_3278_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___x_3289_, v___y_3269_);
lean_dec_ref_known(v___x_3289_, 3);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; 
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_a_3291_);
lean_dec_ref_known(v___x_3290_, 1);
v_a_3272_ = v_a_3291_;
goto v___jp_3271_;
}
else
{
return v___x_3290_;
}
}
}
else
{
lean_object* v___x_3292_; 
v___x_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3292_, 0, v_b_3263_);
return v___x_3292_;
}
v___jp_3271_:
{
size_t v___x_3273_; size_t v___x_3274_; 
v___x_3273_ = ((size_t)1ULL);
v___x_3274_ = lean_usize_add(v_i_3261_, v___x_3273_);
v_i_3261_ = v___x_3274_;
v_b_3263_ = v_a_3272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3___boxed(lean_object* v_as_3293_, lean_object* v_i_3294_, lean_object* v_stop_3295_, lean_object* v_b_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
size_t v_i_boxed_3304_; size_t v_stop_boxed_3305_; lean_object* v_res_3306_; 
v_i_boxed_3304_ = lean_unbox_usize(v_i_3294_);
lean_dec(v_i_3294_);
v_stop_boxed_3305_ = lean_unbox_usize(v_stop_3295_);
lean_dec(v_stop_3295_);
v_res_3306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v_as_3293_, v_i_boxed_3304_, v_stop_boxed_3305_, v_b_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec_ref(v_as_3293_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId(lean_object* v_currNamespace_3307_, lean_object* v_currLevelNames_3308_, lean_object* v_declId_3309_, lean_object* v_modifiers_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v___x_3318_; lean_object* v_fst_3319_; lean_object* v_snd_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3395_; 
v___x_3318_ = l_Lean_Elab_expandDeclIdCore(v_declId_3309_);
v_fst_3319_ = lean_ctor_get(v___x_3318_, 0);
v_snd_3320_ = lean_ctor_get(v___x_3318_, 1);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3322_ = v___x_3318_;
v_isShared_3323_ = v_isSharedCheck_3395_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_snd_3320_);
lean_inc(v_fst_3319_);
lean_dec(v___x_3318_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3395_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v_levelNames_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3363_; uint8_t v___x_3379_; 
v___x_3379_ = l_Lean_Syntax_isNone(v_snd_3320_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v___x_3380_ = lean_unsigned_to_nat(1u);
v___x_3381_ = l_Lean_Syntax_getArg(v_snd_3320_, v___x_3380_);
lean_dec(v_snd_3320_);
v___x_3382_ = l_Lean_Syntax_getArgs(v___x_3381_);
lean_dec(v___x_3381_);
v___x_3383_ = lean_unsigned_to_nat(0u);
v___x_3384_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__0));
v___x_3385_ = lean_array_get_size(v___x_3382_);
v___x_3386_ = lean_nat_dec_lt(v___x_3383_, v___x_3385_);
if (v___x_3386_ == 0)
{
lean_dec_ref(v___x_3382_);
lean_del_object(v___x_3322_);
v___y_3363_ = v___x_3384_;
goto v___jp_3362_;
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3389_; 
v___x_3387_ = lean_box(v___x_3386_);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 1, v___x_3384_);
lean_ctor_set(v___x_3322_, 0, v___x_3387_);
v___x_3389_ = v___x_3322_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3387_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v___x_3384_);
v___x_3389_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
size_t v___x_3390_; size_t v___x_3391_; lean_object* v___x_3392_; lean_object* v_snd_3393_; 
v___x_3390_ = ((size_t)0ULL);
v___x_3391_ = lean_usize_of_nat(v___x_3385_);
v___x_3392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3379_, v___x_3382_, v___x_3390_, v___x_3391_, v___x_3389_);
lean_dec_ref(v___x_3382_);
v_snd_3393_ = lean_ctor_get(v___x_3392_, 1);
lean_inc(v_snd_3393_);
lean_dec_ref(v___x_3392_);
v___y_3363_ = v_snd_3393_;
goto v___jp_3362_;
}
}
}
else
{
lean_del_object(v___x_3322_);
lean_dec(v_snd_3320_);
v_levelNames_3325_ = v_currLevelNames_3308_;
v___y_3326_ = v_a_3311_;
v___y_3327_ = v_a_3312_;
v___y_3328_ = v_a_3313_;
v___y_3329_ = v_a_3314_;
v___y_3330_ = v_a_3315_;
v___y_3331_ = v_a_3316_;
goto v___jp_3324_;
}
v___jp_3324_:
{
lean_object* v_toCold_3332_; lean_object* v_currRecDepth_3333_; lean_object* v_ref_3334_; uint16_t v_optionFlags_3335_; uint8_t v_suppressElabErrors_3336_; uint8_t v_checkDeprecated_3337_; uint8_t v_isRecordingDeps_3338_; lean_object* v_ref_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v_toCold_3332_ = lean_ctor_get(v___y_3330_, 0);
v_currRecDepth_3333_ = lean_ctor_get(v___y_3330_, 1);
v_ref_3334_ = lean_ctor_get(v___y_3330_, 2);
v_optionFlags_3335_ = lean_ctor_get_uint16(v___y_3330_, sizeof(void*)*3);
v_suppressElabErrors_3336_ = lean_ctor_get_uint8(v___y_3330_, sizeof(void*)*3 + 2);
v_checkDeprecated_3337_ = lean_ctor_get_uint8(v___y_3330_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3338_ = lean_ctor_get_uint8(v___y_3330_, sizeof(void*)*3 + 4);
v_ref_3339_ = l_Lean_replaceRef(v_declId_3309_, v_ref_3334_);
lean_inc(v_currRecDepth_3333_);
lean_inc_ref(v_toCold_3332_);
v___x_3340_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3340_, 0, v_toCold_3332_);
lean_ctor_set(v___x_3340_, 1, v_currRecDepth_3333_);
lean_ctor_set(v___x_3340_, 2, v_ref_3339_);
lean_ctor_set_uint16(v___x_3340_, sizeof(void*)*3, v_optionFlags_3335_);
lean_ctor_set_uint8(v___x_3340_, sizeof(void*)*3 + 2, v_suppressElabErrors_3336_);
lean_ctor_set_uint8(v___x_3340_, sizeof(void*)*3 + 3, v_checkDeprecated_3337_);
lean_ctor_set_uint8(v___x_3340_, sizeof(void*)*3 + 4, v_isRecordingDeps_3338_);
v___x_3341_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3307_, v_modifiers_3310_, v_fst_3319_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___x_3340_, v___y_3331_);
lean_dec_ref_known(v___x_3340_, 3);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3353_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3344_ = v___x_3341_;
v_isShared_3345_ = v_isSharedCheck_3353_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3341_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3353_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v_fst_3346_; lean_object* v_snd_3347_; lean_object* v_docString_x3f_3348_; lean_object* v___x_3349_; lean_object* v___x_3351_; 
v_fst_3346_ = lean_ctor_get(v_a_3342_, 0);
lean_inc(v_fst_3346_);
v_snd_3347_ = lean_ctor_get(v_a_3342_, 1);
lean_inc(v_snd_3347_);
lean_dec(v_a_3342_);
v_docString_x3f_3348_ = lean_ctor_get(v_modifiers_3310_, 1);
lean_inc(v_docString_x3f_3348_);
v___x_3349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3349_, 0, v_snd_3347_);
lean_ctor_set(v___x_3349_, 1, v_fst_3346_);
lean_ctor_set(v___x_3349_, 2, v_levelNames_3325_);
lean_ctor_set(v___x_3349_, 3, v_docString_x3f_3348_);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v___x_3349_);
v___x_3351_ = v___x_3344_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec(v_levelNames_3325_);
v_a_3354_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3341_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3341_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
v___jp_3362_:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; uint8_t v___x_3366_; 
v___x_3364_ = lean_unsigned_to_nat(0u);
v___x_3365_ = lean_array_get_size(v___y_3363_);
v___x_3366_ = lean_nat_dec_lt(v___x_3364_, v___x_3365_);
if (v___x_3366_ == 0)
{
lean_dec_ref(v___y_3363_);
v_levelNames_3325_ = v_currLevelNames_3308_;
v___y_3326_ = v_a_3311_;
v___y_3327_ = v_a_3312_;
v___y_3328_ = v_a_3313_;
v___y_3329_ = v_a_3314_;
v___y_3330_ = v_a_3315_;
v___y_3331_ = v_a_3316_;
goto v___jp_3324_;
}
else
{
size_t v___x_3367_; size_t v___x_3368_; lean_object* v___x_3369_; 
v___x_3367_ = ((size_t)0ULL);
v___x_3368_ = lean_usize_of_nat(v___x_3365_);
v___x_3369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3363_, v___x_3367_, v___x_3368_, v_currLevelNames_3308_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
lean_dec_ref(v___y_3363_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_a_3370_);
lean_dec_ref_known(v___x_3369_, 1);
v_levelNames_3325_ = v_a_3370_;
v___y_3326_ = v_a_3311_;
v___y_3327_ = v_a_3312_;
v___y_3328_ = v_a_3313_;
v___y_3329_ = v_a_3314_;
v___y_3330_ = v_a_3315_;
v___y_3331_ = v_a_3316_;
goto v___jp_3324_;
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec(v_fst_3319_);
lean_dec(v_currNamespace_3307_);
v_a_3371_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3369_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3369_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___boxed(lean_object* v_currNamespace_3396_, lean_object* v_currLevelNames_3397_, lean_object* v_declId_3398_, lean_object* v_modifiers_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_Elab_expandDeclId(v_currNamespace_3396_, v_currLevelNames_3397_, v_declId_3398_, v_modifiers_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_a_3403_);
lean_dec_ref(v_a_3402_);
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3400_);
lean_dec_ref(v_modifiers_3399_);
lean_dec(v_declId_3398_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(lean_object* v_00_u03b1_3408_, lean_object* v_u_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___boxed(lean_object* v_00_u03b1_3418_, lean_object* v_u_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(v_00_u03b1_3418_, v_u_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(lean_object* v_00_u03b1_3428_, lean_object* v_msg_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v___x_3437_; 
v___x_3437_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3438_, lean_object* v_msg_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(v_00_u03b1_3438_, v_msg_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(lean_object* v_msgData_3448_, lean_object* v_macroStack_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v___x_3457_; 
v___x_3457_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_3448_, v_macroStack_3449_, v___y_3454_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_3458_, lean_object* v_macroStack_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(v_msgData_3458_, v_macroStack_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17(lean_object* v_00_u03b2_3468_){
_start:
{
lean_object* v___x_3469_; 
v___x_3469_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9___redArg(){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v___dummy_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9___redArg();
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9(lean_object* v_00_u03b2_3474_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(lean_object* v_t_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_3476_, v___y_3482_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___boxed(lean_object* v_t_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(v_t_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(lean_object* v_00_u03b1_3494_, lean_object* v_env_3495_, lean_object* v_x_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v___x_3504_; 
v___x_3504_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_3495_, v_x_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3505_, lean_object* v_env_3506_, lean_object* v_x_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(v_00_u03b1_3505_, v_env_3506_, v_x_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(lean_object* v_env_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_3516_, v___y_3520_, v___y_3522_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___boxed(lean_object* v_env_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(v_env_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17(lean_object* v_00_u03b1_3534_, lean_object* v_constName_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___redArg(v_constName_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3544_, lean_object* v_constName_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17(v_00_u03b1_3544_, v_constName_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21(lean_object* v_00_u03b1_3554_, lean_object* v_ref_3555_, lean_object* v_constName_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg(v_ref_3555_, v_constName_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___boxed(lean_object* v_00_u03b1_3565_, lean_object* v_ref_3566_, lean_object* v_constName_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21(v_00_u03b1_3565_, v_ref_3566_, v_constName_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v_ref_3566_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24(lean_object* v_00_u03b1_3576_, lean_object* v_ref_3577_, lean_object* v_msg_3578_, lean_object* v_declHint_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___redArg(v_ref_3577_, v_msg_3578_, v_declHint_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___boxed(lean_object* v_00_u03b1_3588_, lean_object* v_ref_3589_, lean_object* v_msg_3590_, lean_object* v_declHint_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24(v_00_u03b1_3588_, v_ref_3589_, v_msg_3590_, v_declHint_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v_ref_3589_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26(lean_object* v_msg_3600_, lean_object* v_declHint_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg(v_msg_3600_, v_declHint_3601_, v___y_3607_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___boxed(lean_object* v_msg_3610_, lean_object* v_declHint_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26(v_msg_3610_, v_declHint_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26(lean_object* v_00_u03b1_3620_, lean_object* v_ref_3621_, lean_object* v_msg_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___redArg(v_ref_3621_, v_msg_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___boxed(lean_object* v_00_u03b1_3631_, lean_object* v_ref_3632_, lean_object* v_msg_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26(v_00_u03b1_3631_, v_ref_3632_, v_msg_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v_ref_3632_);
return v_res_3641_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(lean_object* v_x_3645_){
_start:
{
lean_object* v_name_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v_name_3646_ = lean_ctor_get(v_x_3645_, 0);
v___x_3647_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__1));
v___x_3648_ = lean_name_eq(v_name_3646_, v___x_3647_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___boxed(lean_object* v_x_3649_){
_start:
{
uint8_t v_res_3650_; lean_object* v_r_3651_; 
v_res_3650_ = l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(v_x_3649_);
lean_dec_ref(v_x_3649_);
v_r_3651_ = lean_box(v_res_3650_);
return v_r_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__1(lean_object* v_ctx_3652_){
_start:
{
lean_object* v_toCold_3653_; lean_object* v_currRecDepth_3654_; lean_object* v_ref_3655_; uint16_t v_optionFlags_3656_; uint8_t v_suppressElabErrors_3657_; uint8_t v_isRecordingDeps_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3666_; 
v_toCold_3653_ = lean_ctor_get(v_ctx_3652_, 0);
v_currRecDepth_3654_ = lean_ctor_get(v_ctx_3652_, 1);
v_ref_3655_ = lean_ctor_get(v_ctx_3652_, 2);
v_optionFlags_3656_ = lean_ctor_get_uint16(v_ctx_3652_, sizeof(void*)*3);
v_suppressElabErrors_3657_ = lean_ctor_get_uint8(v_ctx_3652_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3658_ = lean_ctor_get_uint8(v_ctx_3652_, sizeof(void*)*3 + 4);
v_isSharedCheck_3666_ = !lean_is_exclusive(v_ctx_3652_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3660_ = v_ctx_3652_;
v_isShared_3661_ = v_isSharedCheck_3666_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_ref_3655_);
lean_inc(v_currRecDepth_3654_);
lean_inc(v_toCold_3653_);
lean_dec(v_ctx_3652_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3666_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
uint8_t v___x_3662_; lean_object* v___x_3664_; 
v___x_3662_ = 2;
if (v_isShared_3661_ == 0)
{
v___x_3664_ = v___x_3660_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_toCold_3653_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v_currRecDepth_3654_);
lean_ctor_set(v_reuseFailAlloc_3665_, 2, v_ref_3655_);
lean_ctor_set_uint16(v_reuseFailAlloc_3665_, sizeof(void*)*3, v_optionFlags_3656_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, sizeof(void*)*3 + 2, v_suppressElabErrors_3657_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, sizeof(void*)*3 + 4, v_isRecordingDeps_3658_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_ctor_set_uint8(v___x_3664_, sizeof(void*)*3 + 3, v___x_3662_);
return v___x_3664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg(lean_object* v_inst_3688_, lean_object* v_attrs_3689_, lean_object* v_a_3690_){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; uint8_t v___x_3694_; 
v___x_3691_ = lean_unsigned_to_nat(0u);
v___x_3692_ = lean_array_get_size(v_attrs_3689_);
v___x_3693_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9));
v___x_3694_ = lean_nat_dec_lt(v___x_3691_, v___x_3692_);
if (v___x_3694_ == 0)
{
lean_dec_ref(v_attrs_3689_);
lean_dec(v_inst_3688_);
return v_a_3690_;
}
else
{
if (v___x_3694_ == 0)
{
lean_dec_ref(v_attrs_3689_);
lean_dec(v_inst_3688_);
return v_a_3690_;
}
else
{
lean_object* v___f_3695_; size_t v___x_3696_; size_t v___x_3697_; lean_object* v___x_3698_; uint8_t v___x_3699_; 
v___f_3695_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10));
v___x_3696_ = ((size_t)0ULL);
v___x_3697_ = lean_usize_of_nat(v___x_3692_);
v___x_3698_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_3693_, v___f_3695_, v_attrs_3689_, v___x_3696_, v___x_3697_);
v___x_3699_ = lean_unbox(v___x_3698_);
lean_dec(v___x_3698_);
if (v___x_3699_ == 0)
{
lean_dec(v_inst_3688_);
return v_a_3690_;
}
else
{
lean_object* v___f_3700_; lean_object* v___x_3701_; 
v___f_3700_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11));
v___x_3701_ = lean_apply_3(v_inst_3688_, lean_box(0), v___f_3700_, v_a_3690_);
return v___x_3701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs(lean_object* v_m_3702_, lean_object* v_00_u03b1_3703_, lean_object* v_inst_3704_, lean_object* v_attrs_3705_, lean_object* v_a_3706_){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; 
v___x_3707_ = lean_unsigned_to_nat(0u);
v___x_3708_ = lean_array_get_size(v_attrs_3705_);
v___x_3709_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9));
v___x_3710_ = lean_nat_dec_lt(v___x_3707_, v___x_3708_);
if (v___x_3710_ == 0)
{
lean_dec_ref(v_attrs_3705_);
lean_dec(v_inst_3704_);
return v_a_3706_;
}
else
{
if (v___x_3710_ == 0)
{
lean_dec_ref(v_attrs_3705_);
lean_dec(v_inst_3704_);
return v_a_3706_;
}
else
{
lean_object* v___f_3711_; size_t v___x_3712_; size_t v___x_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___f_3711_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10));
v___x_3712_ = ((size_t)0ULL);
v___x_3713_ = lean_usize_of_nat(v___x_3708_);
v___x_3714_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_3709_, v___f_3711_, v_attrs_3705_, v___x_3712_, v___x_3713_);
v___x_3715_ = lean_unbox(v___x_3714_);
lean_dec(v___x_3714_);
if (v___x_3715_ == 0)
{
lean_dec(v_inst_3704_);
return v_a_3706_;
}
else
{
lean_object* v___f_3716_; lean_object* v___x_3717_; 
v___f_3716_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11));
v___x_3717_ = lean_apply_3(v_inst_3704_, lean_box(0), v___f_3716_, v_a_3706_);
return v___x_3717_;
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
