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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__24;
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
uint8_t v___x_688__boxed_90_; lean_object* v_res_91_; 
v___x_688__boxed_90_ = lean_unbox(v___x_86_);
v_res_91_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(v_____do__lift_85_, v___x_688__boxed_90_, v_inst_87_, v_inst_88_, v_____do__lift_89_);
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
uint8_t v___x_732__boxed_112_; lean_object* v_res_113_; 
v___x_732__boxed_112_ = lean_unbox(v___x_104_);
v_res_113_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(v___x_732__boxed_112_, v_inst_105_, v_inst_106_, v_inst_107_, v_inst_108_, v_declName_109_, v_toBind_110_, v_____do__lift_111_);
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
uint8_t v___x_758__boxed_134_; lean_object* v_res_135_; 
v___x_758__boxed_134_ = lean_unbox(v___x_127_);
v_res_135_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(v_toMonadRef_126_, v___x_758__boxed_134_, v_inst_128_, v_inst_129_, v_inst_130_, v_inst_131_, v_toBind_132_, v_declName_133_);
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
uint8_t v___x_792__boxed_158_; lean_object* v_res_159_; 
v___x_792__boxed_158_ = lean_unbox(v___x_154_);
v_res_159_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(v_val_153_, v___x_792__boxed_158_, v_inst_155_, v_inst_156_, v_____r_157_);
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
uint8_t v___x_869__boxed_207_; lean_object* v_res_208_; 
v___x_869__boxed_207_ = lean_unbox(v___x_201_);
v_res_208_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(v_declName_200_, v___x_869__boxed_207_, v_inst_202_, v_inst_203_, v_toBind_204_, v___f_205_, v_____r_206_);
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
uint8_t v___x_942__boxed_266_; lean_object* v_res_267_; 
v___x_942__boxed_266_ = lean_unbox(v___x_259_);
v_res_267_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(v___f_257_, v_declName_258_, v___x_942__boxed_266_, v_inst_260_, v_inst_261_, v_toBind_262_, v___f_263_, v_env_264_, v_____do__lift_265_);
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
uint8_t v___x_1016__boxed_308_; lean_object* v_res_309_; 
v___x_1016__boxed_308_ = lean_unbox(v___x_301_);
v_res_309_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(v_declName_300_, v___x_1016__boxed_308_, v_inst_302_, v_inst_303_, v_toBind_304_, v___f_305_, v___f_306_, v_____r_307_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx___impl(uint8_t v_x_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_box(v_x_362_);
v___x_364_ = lean_obj_tag_nat(v___x_363_);
lean_dec(v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx___impl___boxed(lean_object* v_x_365_){
_start:
{
uint8_t v_x_4__boxed_366_; lean_object* v_res_367_; 
v_x_4__boxed_366_ = lean_unbox(v_x_365_);
v_res_367_ = l_Lean_Elab_Visibility_ctorIdx___impl(v_x_4__boxed_366_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___redArg(lean_object* v_k_368_){
_start:
{
lean_inc(v_k_368_);
return v_k_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___redArg___boxed(lean_object* v_k_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Elab_Visibility_ctorElim___redArg(v_k_369_);
lean_dec(v_k_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim(lean_object* v_motive_371_, lean_object* v_ctorIdx_372_, uint8_t v_t_373_, lean_object* v_h_374_, lean_object* v_k_375_){
_start:
{
lean_inc(v_k_375_);
return v_k_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___boxed(lean_object* v_motive_376_, lean_object* v_ctorIdx_377_, lean_object* v_t_378_, lean_object* v_h_379_, lean_object* v_k_380_){
_start:
{
uint8_t v_t_boxed_381_; lean_object* v_res_382_; 
v_t_boxed_381_ = lean_unbox(v_t_378_);
v_res_382_ = l_Lean_Elab_Visibility_ctorElim(v_motive_376_, v_ctorIdx_377_, v_t_boxed_381_, v_h_379_, v_k_380_);
lean_dec(v_k_380_);
lean_dec(v_ctorIdx_377_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___redArg(lean_object* v_regular_383_){
_start:
{
lean_inc(v_regular_383_);
return v_regular_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___redArg___boxed(lean_object* v_regular_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Elab_Visibility_regular_elim___redArg(v_regular_384_);
lean_dec(v_regular_384_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim(lean_object* v_motive_386_, uint8_t v_t_387_, lean_object* v_h_388_, lean_object* v_regular_389_){
_start:
{
lean_inc(v_regular_389_);
return v_regular_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___boxed(lean_object* v_motive_390_, lean_object* v_t_391_, lean_object* v_h_392_, lean_object* v_regular_393_){
_start:
{
uint8_t v_t_boxed_394_; lean_object* v_res_395_; 
v_t_boxed_394_ = lean_unbox(v_t_391_);
v_res_395_ = l_Lean_Elab_Visibility_regular_elim(v_motive_390_, v_t_boxed_394_, v_h_392_, v_regular_393_);
lean_dec(v_regular_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___redArg(lean_object* v_private_396_){
_start:
{
lean_inc(v_private_396_);
return v_private_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___redArg___boxed(lean_object* v_private_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Elab_Visibility_private_elim___redArg(v_private_397_);
lean_dec(v_private_397_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim(lean_object* v_motive_399_, uint8_t v_t_400_, lean_object* v_h_401_, lean_object* v_private_402_){
_start:
{
lean_inc(v_private_402_);
return v_private_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___boxed(lean_object* v_motive_403_, lean_object* v_t_404_, lean_object* v_h_405_, lean_object* v_private_406_){
_start:
{
uint8_t v_t_boxed_407_; lean_object* v_res_408_; 
v_t_boxed_407_ = lean_unbox(v_t_404_);
v_res_408_ = l_Lean_Elab_Visibility_private_elim(v_motive_403_, v_t_boxed_407_, v_h_405_, v_private_406_);
lean_dec(v_private_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___redArg(lean_object* v_public_409_){
_start:
{
lean_inc(v_public_409_);
return v_public_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___redArg___boxed(lean_object* v_public_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Elab_Visibility_public_elim___redArg(v_public_410_);
lean_dec(v_public_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim(lean_object* v_motive_412_, uint8_t v_t_413_, lean_object* v_h_414_, lean_object* v_public_415_){
_start:
{
lean_inc(v_public_415_);
return v_public_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___boxed(lean_object* v_motive_416_, lean_object* v_t_417_, lean_object* v_h_418_, lean_object* v_public_419_){
_start:
{
uint8_t v_t_boxed_420_; lean_object* v_res_421_; 
v_t_boxed_420_ = lean_unbox(v_t_417_);
v_res_421_ = l_Lean_Elab_Visibility_public_elim(v_motive_416_, v_t_boxed_420_, v_h_418_, v_public_419_);
lean_dec(v_public_419_);
return v_res_421_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedVisibility_default(void){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedVisibility(void){
_start:
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0(uint8_t v_x_427_){
_start:
{
switch(v_x_427_)
{
case 0:
{
lean_object* v___x_428_; 
v___x_428_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__0));
return v___x_428_;
}
case 1:
{
lean_object* v___x_429_; 
v___x_429_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__1));
return v___x_429_;
}
default: 
{
lean_object* v___x_430_; 
v___x_430_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__2));
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0___boxed(lean_object* v_x_431_){
_start:
{
uint8_t v_x_36__boxed_432_; lean_object* v_res_433_; 
v_x_36__boxed_432_ = lean_unbox(v_x_431_);
v_res_433_ = l_Lean_Elab_instToStringVisibility___lam__0(v_x_36__boxed_432_);
return v_res_433_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPrivate(uint8_t v_x_436_){
_start:
{
if (v_x_436_ == 1)
{
uint8_t v___x_437_; 
v___x_437_ = 1;
return v___x_437_;
}
else
{
uint8_t v___x_438_; 
v___x_438_ = 0;
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPrivate___boxed(lean_object* v_x_439_){
_start:
{
uint8_t v_x_17__boxed_440_; uint8_t v_res_441_; lean_object* v_r_442_; 
v_x_17__boxed_440_ = lean_unbox(v_x_439_);
v_res_441_ = l_Lean_Elab_Visibility_isPrivate(v_x_17__boxed_440_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPublic(uint8_t v_x_443_){
_start:
{
if (v_x_443_ == 2)
{
uint8_t v___x_444_; 
v___x_444_ = 1;
return v___x_444_;
}
else
{
uint8_t v___x_445_; 
v___x_445_ = 0;
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPublic___boxed(lean_object* v_x_446_){
_start:
{
uint8_t v_x_17__boxed_447_; uint8_t v_res_448_; lean_object* v_r_449_; 
v_x_17__boxed_447_ = lean_unbox(v_x_446_);
v_res_448_ = l_Lean_Elab_Visibility_isPublic(v_x_17__boxed_447_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isInferredPublic(lean_object* v_env_450_, uint8_t v_v_451_){
_start:
{
uint8_t v___y_453_; uint8_t v_isExporting_456_; 
v_isExporting_456_ = lean_ctor_get_uint8(v_env_450_, sizeof(void*)*13);
if (v_isExporting_456_ == 0)
{
lean_object* v___x_457_; uint8_t v_isModule_458_; 
v___x_457_ = l_Lean_Environment_header(v_env_450_);
v_isModule_458_ = lean_ctor_get_uint8(v___x_457_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_457_);
if (v_isModule_458_ == 0)
{
uint8_t v___x_459_; 
v___x_459_ = 1;
v___y_453_ = v___x_459_;
goto v___jp_452_;
}
else
{
uint8_t v___x_460_; 
v___x_460_ = l_Lean_Elab_Visibility_isPublic(v_v_451_);
return v___x_460_;
}
}
else
{
v___y_453_ = v_isExporting_456_;
goto v___jp_452_;
}
v___jp_452_:
{
uint8_t v___x_454_; 
v___x_454_ = l_Lean_Elab_Visibility_isPrivate(v_v_451_);
if (v___x_454_ == 0)
{
return v___y_453_;
}
else
{
uint8_t v___x_455_; 
v___x_455_ = 0;
return v___x_455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isInferredPublic___boxed(lean_object* v_env_461_, lean_object* v_v_462_){
_start:
{
uint8_t v_v_boxed_463_; uint8_t v_res_464_; lean_object* v_r_465_; 
v_v_boxed_463_ = lean_unbox(v_v_462_);
v_res_464_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_461_, v_v_boxed_463_);
lean_dec_ref(v_env_461_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__0(lean_object* v_toPure_466_, lean_object* v_____r_467_){
_start:
{
uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = 2;
v___x_469_ = lean_box(v___x_468_);
v___x_470_ = lean_apply_2(v_toPure_466_, lean_box(0), v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__2(lean_object* v_toPure_471_, lean_object* v_____r_472_){
_start:
{
uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = 1;
v___x_474_ = lean_box(v___x_473_);
v___x_475_ = lean_apply_2(v_toPure_471_, lean_box(0), v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__0));
v___x_478_ = l_Lean_stringToMessageData(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__2));
v___x_481_ = l_Lean_stringToMessageData(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__10));
v___x_498_ = l_Lean_stringToMessageData(v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__12));
v___x_501_ = l_Lean_stringToMessageData(v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3(lean_object* v_vis_x3f_502_, lean_object* v_toPure_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_toBind_510_, lean_object* v___f_511_, lean_object* v___f_512_, uint8_t v_isExample_513_, lean_object* v___f_514_, lean_object* v___f_515_, lean_object* v_env_516_){
_start:
{
if (lean_obj_tag(v_vis_x3f_502_) == 0)
{
uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v___f_515_);
lean_dec(v___f_514_);
lean_dec(v___f_512_);
lean_dec(v___f_511_);
lean_dec(v_toBind_510_);
lean_dec_ref(v_inst_509_);
lean_dec_ref(v_inst_508_);
lean_dec(v_inst_507_);
lean_dec_ref(v_inst_506_);
lean_dec_ref(v_inst_505_);
lean_dec_ref(v_inst_504_);
v___x_520_ = 0;
v___x_521_ = lean_box(v___x_520_);
v___x_522_ = lean_apply_2(v_toPure_503_, lean_box(0), v___x_521_);
return v___x_522_;
}
else
{
lean_object* v_val_523_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; uint8_t v___y_542_; lean_object* v___x_545_; uint8_t v___x_546_; uint8_t v___y_548_; uint8_t v___y_549_; uint8_t v___y_553_; 
lean_dec(v_toPure_503_);
v_val_523_ = lean_ctor_get(v_vis_x3f_502_, 0);
lean_inc_n(v_val_523_, 2);
lean_dec_ref_known(v_vis_x3f_502_, 1);
v___x_545_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8));
v___x_546_ = l_Lean_Syntax_isOfKind(v_val_523_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_555_; uint8_t v___x_556_; 
lean_dec(v___f_515_);
lean_dec(v___f_514_);
v___x_555_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9));
lean_inc(v_val_523_);
v___x_556_ = l_Lean_Syntax_isOfKind(v_val_523_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v___f_512_);
lean_dec(v___f_511_);
lean_dec(v_toBind_510_);
lean_dec_ref(v_inst_509_);
lean_dec_ref(v_inst_508_);
lean_dec(v_inst_507_);
lean_dec_ref(v_inst_506_);
v___x_557_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11);
v___x_558_ = l_Lean_throwErrorAt___redArg(v_inst_504_, v_inst_505_, v_val_523_, v___x_557_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; 
lean_dec_ref(v_inst_505_);
v___x_559_ = l_Lean_Syntax_getHeadInfo(v_val_523_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_dec_ref_known(v___x_559_, 4);
v___y_553_ = v___x_556_;
goto v___jp_552_;
}
else
{
lean_dec(v___x_559_);
if (v___x_546_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec(v_val_523_);
lean_dec(v___f_511_);
lean_dec(v_toBind_510_);
lean_dec_ref(v_inst_509_);
lean_dec_ref(v_inst_508_);
lean_dec(v_inst_507_);
lean_dec_ref(v_inst_506_);
lean_dec_ref(v_inst_504_);
v___x_560_ = lean_box(0);
v___x_561_ = lean_apply_1(v___f_512_, v___x_560_);
return v___x_561_;
}
else
{
v___y_553_ = v___x_546_;
goto v___jp_552_;
}
}
}
}
else
{
lean_object* v___x_562_; 
lean_dec(v___f_512_);
lean_dec(v___f_511_);
lean_dec_ref(v_inst_505_);
v___x_562_ = l_Lean_Syntax_getHeadInfo(v_val_523_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v___x_563_; uint8_t v_isModule_564_; 
lean_dec_ref_known(v___x_562_, 4);
v___x_563_ = l_Lean_Environment_header(v_env_516_);
v_isModule_564_ = lean_ctor_get_uint8(v___x_563_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_563_);
if (v_isModule_564_ == 0)
{
lean_dec(v_val_523_);
lean_dec(v___f_515_);
lean_dec(v_toBind_510_);
lean_dec_ref(v_inst_509_);
lean_dec_ref(v_inst_508_);
lean_dec(v_inst_507_);
lean_dec_ref(v_inst_506_);
lean_dec_ref(v_inst_504_);
goto v___jp_517_;
}
else
{
uint8_t v_isExporting_565_; 
v_isExporting_565_ = lean_ctor_get_uint8(v_env_516_, sizeof(void*)*13);
if (v_isExporting_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec(v___f_514_);
v___x_566_ = l_Lean_linter_redundantVisibility;
v___x_567_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13);
v___x_568_ = l_Lean_Linter_logLintIf___redArg(v_inst_504_, v_inst_506_, v_inst_507_, v_inst_508_, v_inst_509_, v___x_566_, v_val_523_, v___x_567_);
v___x_569_ = lean_apply_4(v_toBind_510_, lean_box(0), lean_box(0), v___x_568_, v___f_515_);
return v___x_569_;
}
else
{
lean_dec(v_val_523_);
lean_dec(v___f_515_);
lean_dec(v_toBind_510_);
lean_dec_ref(v_inst_509_);
lean_dec_ref(v_inst_508_);
lean_dec(v_inst_507_);
lean_dec_ref(v_inst_506_);
lean_dec_ref(v_inst_504_);
goto v___jp_517_;
}
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v___x_562_);
lean_dec(v_val_523_);
lean_dec(v___f_515_);
lean_dec(v_toBind_510_);
lean_dec_ref(v_inst_509_);
lean_dec_ref(v_inst_508_);
lean_dec(v_inst_507_);
lean_dec_ref(v_inst_506_);
lean_dec_ref(v_inst_504_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_apply_1(v___f_514_, v___x_570_);
return v___x_571_;
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
v___x_532_ = l_Lean_Linter_logLintIf___redArg(v_inst_504_, v_inst_506_, v_inst_507_, v_inst_508_, v_inst_509_, v___y_525_, v_val_523_, v___x_531_);
v___x_533_ = lean_apply_4(v_toBind_510_, lean_box(0), lean_box(0), v___x_532_, v___f_511_);
return v___x_533_;
}
v___jp_534_:
{
lean_object* v___x_535_; uint8_t v_isModule_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_535_ = l_Lean_Environment_header(v_env_516_);
v_isModule_536_ = lean_ctor_get_uint8(v___x_535_, sizeof(void*)*8 + 4);
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
lean_dec(v___f_511_);
lean_dec(v_toBind_510_);
lean_dec_ref(v_inst_509_);
lean_dec_ref(v_inst_508_);
lean_dec(v_inst_507_);
lean_dec_ref(v_inst_506_);
lean_dec_ref(v_inst_504_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_apply_1(v___f_512_, v___x_543_);
return v___x_544_;
}
else
{
lean_dec(v___f_512_);
goto v___jp_534_;
}
}
v___jp_547_:
{
if (v___y_549_ == 0)
{
lean_object* v___x_550_; uint8_t v_isModule_551_; 
v___x_550_ = l_Lean_Environment_header(v_env_516_);
v_isModule_551_ = lean_ctor_get_uint8(v___x_550_, sizeof(void*)*8 + 4);
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
lean_dec(v___f_512_);
goto v___jp_534_;
}
}
v___jp_552_:
{
uint8_t v_isExporting_554_; 
v_isExporting_554_ = lean_ctor_get_uint8(v_env_516_, sizeof(void*)*13);
if (v_isExporting_554_ == 0)
{
v___y_548_ = v___y_553_;
v___y_549_ = v___x_546_;
goto v___jp_547_;
}
else
{
if (v_isExample_513_ == 0)
{
v___y_548_ = v___y_553_;
v___y_549_ = v___y_553_;
goto v___jp_547_;
}
else
{
v___y_548_ = v___y_553_;
v___y_549_ = v___x_546_;
goto v___jp_547_;
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___boxed(lean_object* v_vis_x3f_572_, lean_object* v_toPure_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_toBind_580_, lean_object* v___f_581_, lean_object* v___f_582_, lean_object* v_isExample_583_, lean_object* v___f_584_, lean_object* v___f_585_, lean_object* v_env_586_){
_start:
{
uint8_t v_isExample_boxed_587_; lean_object* v_res_588_; 
v_isExample_boxed_587_ = lean_unbox(v_isExample_583_);
v_res_588_ = l_Lean_Elab_elabVisibility___redArg___lam__3(v_vis_x3f_572_, v_toPure_573_, v_inst_574_, v_inst_575_, v_inst_576_, v_inst_577_, v_inst_578_, v_inst_579_, v_toBind_580_, v___f_581_, v___f_582_, v_isExample_boxed_587_, v___f_584_, v___f_585_, v_env_586_);
lean_dec_ref(v_env_586_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg(lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_vis_x3f_595_, uint8_t v_isExample_596_){
_start:
{
lean_object* v_toApplicative_597_; lean_object* v_toBind_598_; lean_object* v_getEnv_599_; lean_object* v_toPure_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v___f_606_; lean_object* v___x_607_; 
v_toApplicative_597_ = lean_ctor_get(v_inst_589_, 0);
v_toBind_598_ = lean_ctor_get(v_inst_589_, 1);
lean_inc_n(v_toBind_598_, 2);
v_getEnv_599_ = lean_ctor_get(v_inst_591_, 0);
lean_inc(v_getEnv_599_);
v_toPure_600_ = lean_ctor_get(v_toApplicative_597_, 1);
lean_inc_n(v_toPure_600_, 3);
v___f_601_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__0), 2, 1);
lean_closure_set(v___f_601_, 0, v_toPure_600_);
lean_inc_ref(v___f_601_);
v___f_602_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_602_, 0, v___f_601_);
v___f_603_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__2), 2, 1);
lean_closure_set(v___f_603_, 0, v_toPure_600_);
lean_inc_ref(v___f_603_);
v___f_604_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_604_, 0, v___f_603_);
v___x_605_ = lean_box(v_isExample_596_);
v___f_606_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_606_, 0, v_vis_x3f_595_);
lean_closure_set(v___f_606_, 1, v_toPure_600_);
lean_closure_set(v___f_606_, 2, v_inst_589_);
lean_closure_set(v___f_606_, 3, v_inst_590_);
lean_closure_set(v___f_606_, 4, v_inst_593_);
lean_closure_set(v___f_606_, 5, v_inst_594_);
lean_closure_set(v___f_606_, 6, v_inst_592_);
lean_closure_set(v___f_606_, 7, v_inst_591_);
lean_closure_set(v___f_606_, 8, v_toBind_598_);
lean_closure_set(v___f_606_, 9, v___f_602_);
lean_closure_set(v___f_606_, 10, v___f_601_);
lean_closure_set(v___f_606_, 11, v___x_605_);
lean_closure_set(v___f_606_, 12, v___f_603_);
lean_closure_set(v___f_606_, 13, v___f_604_);
v___x_607_ = lean_apply_4(v_toBind_598_, lean_box(0), lean_box(0), v_getEnv_599_, v___f_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___boxed(lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_vis_x3f_614_, lean_object* v_isExample_615_){
_start:
{
uint8_t v_isExample_boxed_616_; lean_object* v_res_617_; 
v_isExample_boxed_616_ = lean_unbox(v_isExample_615_);
v_res_617_ = l_Lean_Elab_elabVisibility___redArg(v_inst_608_, v_inst_609_, v_inst_610_, v_inst_611_, v_inst_612_, v_inst_613_, v_vis_x3f_614_, v_isExample_boxed_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility(lean_object* v_m_618_, lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_vis_x3f_625_, uint8_t v_isExample_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Elab_elabVisibility___redArg(v_inst_619_, v_inst_620_, v_inst_621_, v_inst_622_, v_inst_623_, v_inst_624_, v_vis_x3f_625_, v_isExample_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___boxed(lean_object* v_m_628_, lean_object* v_inst_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_vis_x3f_635_, lean_object* v_isExample_636_){
_start:
{
uint8_t v_isExample_boxed_637_; lean_object* v_res_638_; 
v_isExample_boxed_637_ = lean_unbox(v_isExample_636_);
v_res_638_ = l_Lean_Elab_elabVisibility(v_m_628_, v_inst_629_, v_inst_630_, v_inst_631_, v_inst_632_, v_inst_633_, v_inst_634_, v_vis_x3f_635_, v_isExample_boxed_637_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___impl(uint8_t v_x_639_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_box(v_x_639_);
v___x_641_ = lean_obj_tag_nat(v___x_640_);
lean_dec(v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___impl___boxed(lean_object* v_x_642_){
_start:
{
uint8_t v_x_4__boxed_643_; lean_object* v_res_644_; 
v_x_4__boxed_643_ = lean_unbox(v_x_642_);
v_res_644_ = l_Lean_Elab_RecKind_ctorIdx___impl(v_x_4__boxed_643_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg(lean_object* v_k_645_){
_start:
{
lean_inc(v_k_645_);
return v_k_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg___boxed(lean_object* v_k_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Elab_RecKind_ctorElim___redArg(v_k_646_);
lean_dec(v_k_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim(lean_object* v_motive_648_, lean_object* v_ctorIdx_649_, uint8_t v_t_650_, lean_object* v_h_651_, lean_object* v_k_652_){
_start:
{
lean_inc(v_k_652_);
return v_k_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___boxed(lean_object* v_motive_653_, lean_object* v_ctorIdx_654_, lean_object* v_t_655_, lean_object* v_h_656_, lean_object* v_k_657_){
_start:
{
uint8_t v_t_boxed_658_; lean_object* v_res_659_; 
v_t_boxed_658_ = lean_unbox(v_t_655_);
v_res_659_ = l_Lean_Elab_RecKind_ctorElim(v_motive_653_, v_ctorIdx_654_, v_t_boxed_658_, v_h_656_, v_k_657_);
lean_dec(v_k_657_);
lean_dec(v_ctorIdx_654_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg(lean_object* v_partial_660_){
_start:
{
lean_inc(v_partial_660_);
return v_partial_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg___boxed(lean_object* v_partial_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_Elab_RecKind_partial_elim___redArg(v_partial_661_);
lean_dec(v_partial_661_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim(lean_object* v_motive_663_, uint8_t v_t_664_, lean_object* v_h_665_, lean_object* v_partial_666_){
_start:
{
lean_inc(v_partial_666_);
return v_partial_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___boxed(lean_object* v_motive_667_, lean_object* v_t_668_, lean_object* v_h_669_, lean_object* v_partial_670_){
_start:
{
uint8_t v_t_boxed_671_; lean_object* v_res_672_; 
v_t_boxed_671_ = lean_unbox(v_t_668_);
v_res_672_ = l_Lean_Elab_RecKind_partial_elim(v_motive_667_, v_t_boxed_671_, v_h_669_, v_partial_670_);
lean_dec(v_partial_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg(lean_object* v_nonrec_673_){
_start:
{
lean_inc(v_nonrec_673_);
return v_nonrec_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg___boxed(lean_object* v_nonrec_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Elab_RecKind_nonrec_elim___redArg(v_nonrec_674_);
lean_dec(v_nonrec_674_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim(lean_object* v_motive_676_, uint8_t v_t_677_, lean_object* v_h_678_, lean_object* v_nonrec_679_){
_start:
{
lean_inc(v_nonrec_679_);
return v_nonrec_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___boxed(lean_object* v_motive_680_, lean_object* v_t_681_, lean_object* v_h_682_, lean_object* v_nonrec_683_){
_start:
{
uint8_t v_t_boxed_684_; lean_object* v_res_685_; 
v_t_boxed_684_ = lean_unbox(v_t_681_);
v_res_685_ = l_Lean_Elab_RecKind_nonrec_elim(v_motive_680_, v_t_boxed_684_, v_h_682_, v_nonrec_683_);
lean_dec(v_nonrec_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg(lean_object* v_default_686_){
_start:
{
lean_inc(v_default_686_);
return v_default_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg___boxed(lean_object* v_default_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Elab_RecKind_default_elim___redArg(v_default_687_);
lean_dec(v_default_687_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim(lean_object* v_motive_689_, uint8_t v_t_690_, lean_object* v_h_691_, lean_object* v_default_692_){
_start:
{
lean_inc(v_default_692_);
return v_default_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___boxed(lean_object* v_motive_693_, lean_object* v_t_694_, lean_object* v_h_695_, lean_object* v_default_696_){
_start:
{
uint8_t v_t_boxed_697_; lean_object* v_res_698_; 
v_t_boxed_697_ = lean_unbox(v_t_694_);
v_res_698_ = l_Lean_Elab_RecKind_default_elim(v_motive_693_, v_t_boxed_697_, v_h_695_, v_default_696_);
lean_dec(v_default_696_);
return v_res_698_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind_default(void){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = 0;
return v___x_699_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind(void){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = 0;
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___impl(uint8_t v_x_701_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_box(v_x_701_);
v___x_703_ = lean_obj_tag_nat(v___x_702_);
lean_dec(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___impl___boxed(lean_object* v_x_704_){
_start:
{
uint8_t v_x_4__boxed_705_; lean_object* v_res_706_; 
v_x_4__boxed_705_ = lean_unbox(v_x_704_);
v_res_706_ = l_Lean_Elab_ComputeKind_ctorIdx___impl(v_x_4__boxed_705_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg(lean_object* v_k_707_){
_start:
{
lean_inc(v_k_707_);
return v_k_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg___boxed(lean_object* v_k_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Elab_ComputeKind_ctorElim___redArg(v_k_708_);
lean_dec(v_k_708_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim(lean_object* v_motive_710_, lean_object* v_ctorIdx_711_, uint8_t v_t_712_, lean_object* v_h_713_, lean_object* v_k_714_){
_start:
{
lean_inc(v_k_714_);
return v_k_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___boxed(lean_object* v_motive_715_, lean_object* v_ctorIdx_716_, lean_object* v_t_717_, lean_object* v_h_718_, lean_object* v_k_719_){
_start:
{
uint8_t v_t_boxed_720_; lean_object* v_res_721_; 
v_t_boxed_720_ = lean_unbox(v_t_717_);
v_res_721_ = l_Lean_Elab_ComputeKind_ctorElim(v_motive_715_, v_ctorIdx_716_, v_t_boxed_720_, v_h_718_, v_k_719_);
lean_dec(v_k_719_);
lean_dec(v_ctorIdx_716_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg(lean_object* v_regular_722_){
_start:
{
lean_inc(v_regular_722_);
return v_regular_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg___boxed(lean_object* v_regular_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Elab_ComputeKind_regular_elim___redArg(v_regular_723_);
lean_dec(v_regular_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim(lean_object* v_motive_725_, uint8_t v_t_726_, lean_object* v_h_727_, lean_object* v_regular_728_){
_start:
{
lean_inc(v_regular_728_);
return v_regular_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___boxed(lean_object* v_motive_729_, lean_object* v_t_730_, lean_object* v_h_731_, lean_object* v_regular_732_){
_start:
{
uint8_t v_t_boxed_733_; lean_object* v_res_734_; 
v_t_boxed_733_ = lean_unbox(v_t_730_);
v_res_734_ = l_Lean_Elab_ComputeKind_regular_elim(v_motive_729_, v_t_boxed_733_, v_h_731_, v_regular_732_);
lean_dec(v_regular_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg(lean_object* v_meta_735_){
_start:
{
lean_inc(v_meta_735_);
return v_meta_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg___boxed(lean_object* v_meta_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Elab_ComputeKind_meta_elim___redArg(v_meta_736_);
lean_dec(v_meta_736_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim(lean_object* v_motive_738_, uint8_t v_t_739_, lean_object* v_h_740_, lean_object* v_meta_741_){
_start:
{
lean_inc(v_meta_741_);
return v_meta_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___boxed(lean_object* v_motive_742_, lean_object* v_t_743_, lean_object* v_h_744_, lean_object* v_meta_745_){
_start:
{
uint8_t v_t_boxed_746_; lean_object* v_res_747_; 
v_t_boxed_746_ = lean_unbox(v_t_743_);
v_res_747_ = l_Lean_Elab_ComputeKind_meta_elim(v_motive_742_, v_t_boxed_746_, v_h_744_, v_meta_745_);
lean_dec(v_meta_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(lean_object* v_noncomputable_748_){
_start:
{
lean_inc(v_noncomputable_748_);
return v_noncomputable_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg___boxed(lean_object* v_noncomputable_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(v_noncomputable_749_);
lean_dec(v_noncomputable_749_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim(lean_object* v_motive_751_, uint8_t v_t_752_, lean_object* v_h_753_, lean_object* v_noncomputable_754_){
_start:
{
lean_inc(v_noncomputable_754_);
return v_noncomputable_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___boxed(lean_object* v_motive_755_, lean_object* v_t_756_, lean_object* v_h_757_, lean_object* v_noncomputable_758_){
_start:
{
uint8_t v_t_boxed_759_; lean_object* v_res_760_; 
v_t_boxed_759_ = lean_unbox(v_t_756_);
v_res_760_ = l_Lean_Elab_ComputeKind_noncomputable_elim(v_motive_755_, v_t_boxed_759_, v_h_757_, v_noncomputable_758_);
lean_dec(v_noncomputable_758_);
return v_res_760_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind_default(void){
_start:
{
uint8_t v___x_761_; 
v___x_761_ = 0;
return v___x_761_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind(void){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = 0;
return v___x_762_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqComputeKind_beq(uint8_t v_x_763_, uint8_t v_y_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_765_ = lean_box(v_x_763_);
v___x_766_ = lean_obj_tag_nat(v___x_765_);
lean_dec(v___x_765_);
v___x_767_ = lean_box(v_y_764_);
v___x_768_ = lean_obj_tag_nat(v___x_767_);
lean_dec(v___x_767_);
v___x_769_ = lean_nat_dec_eq(v___x_766_, v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqComputeKind_beq___boxed(lean_object* v_x_770_, lean_object* v_y_771_){
_start:
{
uint8_t v_x_24__boxed_772_; uint8_t v_y_25__boxed_773_; uint8_t v_res_774_; lean_object* v_r_775_; 
v_x_24__boxed_772_ = lean_unbox(v_x_770_);
v_y_25__boxed_773_ = lean_unbox(v_y_771_);
v_res_774_ = l_Lean_Elab_instBEqComputeKind_beq(v_x_24__boxed_772_, v_y_25__boxed_773_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
static lean_object* _init_l_Lean_Elab_instReprComputeKind_repr___closed__6(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_unsigned_to_nat(2u);
v___x_788_ = lean_nat_to_int(v___x_787_);
return v___x_788_;
}
}
static lean_object* _init_l_Lean_Elab_instReprComputeKind_repr___closed__7(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_to_int(v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprComputeKind_repr(uint8_t v_x_791_, lean_object* v_prec_792_){
_start:
{
lean_object* v___y_794_; lean_object* v___y_801_; lean_object* v___y_808_; 
switch(v_x_791_)
{
case 0:
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = lean_unsigned_to_nat(1024u);
v___x_815_ = lean_nat_dec_le(v___x_814_, v_prec_792_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
v___x_816_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_794_ = v___x_816_;
goto v___jp_793_;
}
else
{
lean_object* v___x_817_; 
v___x_817_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_794_ = v___x_817_;
goto v___jp_793_;
}
}
case 1:
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = lean_unsigned_to_nat(1024u);
v___x_819_ = lean_nat_dec_le(v___x_818_, v_prec_792_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
v___x_820_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_801_ = v___x_820_;
goto v___jp_800_;
}
else
{
lean_object* v___x_821_; 
v___x_821_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_801_ = v___x_821_;
goto v___jp_800_;
}
}
default: 
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = lean_unsigned_to_nat(1024u);
v___x_823_ = lean_nat_dec_le(v___x_822_, v_prec_792_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; 
v___x_824_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_808_ = v___x_824_;
goto v___jp_807_;
}
else
{
lean_object* v___x_825_; 
v___x_825_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_808_ = v___x_825_;
goto v___jp_807_;
}
}
}
v___jp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_795_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__1));
lean_inc(v___y_794_);
v___x_796_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_796_, 0, v___y_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = 0;
v___x_798_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*1, v___x_797_);
v___x_799_ = l_Repr_addAppParen(v___x_798_, v_prec_792_);
return v___x_799_;
}
v___jp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_802_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__3));
lean_inc(v___y_801_);
v___x_803_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_803_, 0, v___y_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = 0;
v___x_805_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*1, v___x_804_);
v___x_806_ = l_Repr_addAppParen(v___x_805_, v_prec_792_);
return v___x_806_;
}
v___jp_807_:
{
lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_809_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__5));
lean_inc(v___y_808_);
v___x_810_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_810_, 0, v___y_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = 0;
v___x_812_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set_uint8(v___x_812_, sizeof(void*)*1, v___x_811_);
v___x_813_ = l_Repr_addAppParen(v___x_812_, v_prec_792_);
return v___x_813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprComputeKind_repr___boxed(lean_object* v_x_826_, lean_object* v_prec_827_){
_start:
{
uint8_t v_x_171__boxed_828_; lean_object* v_res_829_; 
v_x_171__boxed_828_ = lean_unbox(v_x_826_);
v_res_829_ = l_Lean_Elab_instReprComputeKind_repr(v_x_171__boxed_828_, v_prec_827_);
lean_dec(v_prec_827_);
return v_res_829_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object* v_m_844_){
_start:
{
uint8_t v_visibility_845_; uint8_t v___x_846_; 
v_visibility_845_ = lean_ctor_get_uint8(v_m_844_, sizeof(void*)*3);
v___x_846_ = l_Lean_Elab_Visibility_isPrivate(v_visibility_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPrivate___boxed(lean_object* v_m_847_){
_start:
{
uint8_t v_res_848_; lean_object* v_r_849_; 
v_res_848_ = l_Lean_Elab_Modifiers_isPrivate(v_m_847_);
lean_dec_ref(v_m_847_);
v_r_849_ = lean_box(v_res_848_);
return v_r_849_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPublic(lean_object* v_m_850_){
_start:
{
uint8_t v_visibility_851_; uint8_t v___x_852_; 
v_visibility_851_ = lean_ctor_get_uint8(v_m_850_, sizeof(void*)*3);
v___x_852_ = l_Lean_Elab_Visibility_isPublic(v_visibility_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPublic___boxed(lean_object* v_m_853_){
_start:
{
uint8_t v_res_854_; lean_object* v_r_855_; 
v_res_854_ = l_Lean_Elab_Modifiers_isPublic(v_m_853_);
lean_dec_ref(v_m_853_);
v_r_855_ = lean_box(v_res_854_);
return v_r_855_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isInferredPublic(lean_object* v_env_856_, lean_object* v_m_857_){
_start:
{
uint8_t v_visibility_858_; uint8_t v___x_859_; 
v_visibility_858_ = lean_ctor_get_uint8(v_m_857_, sizeof(void*)*3);
v___x_859_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_856_, v_visibility_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isInferredPublic___boxed(lean_object* v_env_860_, lean_object* v_m_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l_Lean_Elab_Modifiers_isInferredPublic(v_env_860_, v_m_861_);
lean_dec_ref(v_m_861_);
lean_dec_ref(v_env_860_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object* v_x_864_){
_start:
{
uint8_t v_recKind_865_; 
v_recKind_865_ = lean_ctor_get_uint8(v_x_864_, sizeof(void*)*3 + 3);
if (v_recKind_865_ == 0)
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
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPartial___boxed(lean_object* v_x_868_){
_start:
{
uint8_t v_res_869_; lean_object* v_r_870_; 
v_res_869_ = l_Lean_Elab_Modifiers_isPartial(v_x_868_);
lean_dec_ref(v_x_868_);
v_r_870_ = lean_box(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNonrec(lean_object* v_x_871_){
_start:
{
uint8_t v_recKind_872_; 
v_recKind_872_ = lean_ctor_get_uint8(v_x_871_, sizeof(void*)*3 + 3);
if (v_recKind_872_ == 1)
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
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNonrec___boxed(lean_object* v_x_875_){
_start:
{
uint8_t v_res_876_; lean_object* v_r_877_; 
v_res_876_ = l_Lean_Elab_Modifiers_isNonrec(v_x_875_);
lean_dec_ref(v_x_875_);
v_r_877_ = lean_box(v_res_876_);
return v_r_877_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isMeta(lean_object* v_m_878_){
_start:
{
uint8_t v_computeKind_879_; 
v_computeKind_879_ = lean_ctor_get_uint8(v_m_878_, sizeof(void*)*3 + 2);
if (v_computeKind_879_ == 1)
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
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isMeta___boxed(lean_object* v_m_882_){
_start:
{
uint8_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = l_Lean_Elab_Modifiers_isMeta(v_m_882_);
lean_dec_ref(v_m_882_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNoncomputable(lean_object* v_m_885_){
_start:
{
uint8_t v_computeKind_886_; 
v_computeKind_886_ = lean_ctor_get_uint8(v_m_885_, sizeof(void*)*3 + 2);
if (v_computeKind_886_ == 2)
{
uint8_t v___x_887_; 
v___x_887_ = 1;
return v___x_887_;
}
else
{
uint8_t v___x_888_; 
v___x_888_ = 0;
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNoncomputable___boxed(lean_object* v_m_889_){
_start:
{
uint8_t v_res_890_; lean_object* v_r_891_; 
v_res_890_ = l_Lean_Elab_Modifiers_isNoncomputable(v_m_889_);
lean_dec_ref(v_m_889_);
v_r_891_ = lean_box(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addAttr(lean_object* v_modifiers_892_, lean_object* v_attr_893_){
_start:
{
lean_object* v_stx_894_; lean_object* v_docString_x3f_895_; uint8_t v_visibility_896_; uint8_t v_isProtected_897_; uint8_t v_computeKind_898_; uint8_t v_recKind_899_; uint8_t v_isUnsafe_900_; lean_object* v_attrs_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_909_; 
v_stx_894_ = lean_ctor_get(v_modifiers_892_, 0);
v_docString_x3f_895_ = lean_ctor_get(v_modifiers_892_, 1);
v_visibility_896_ = lean_ctor_get_uint8(v_modifiers_892_, sizeof(void*)*3);
v_isProtected_897_ = lean_ctor_get_uint8(v_modifiers_892_, sizeof(void*)*3 + 1);
v_computeKind_898_ = lean_ctor_get_uint8(v_modifiers_892_, sizeof(void*)*3 + 2);
v_recKind_899_ = lean_ctor_get_uint8(v_modifiers_892_, sizeof(void*)*3 + 3);
v_isUnsafe_900_ = lean_ctor_get_uint8(v_modifiers_892_, sizeof(void*)*3 + 4);
v_attrs_901_ = lean_ctor_get(v_modifiers_892_, 2);
v_isSharedCheck_909_ = !lean_is_exclusive(v_modifiers_892_);
if (v_isSharedCheck_909_ == 0)
{
v___x_903_ = v_modifiers_892_;
v_isShared_904_ = v_isSharedCheck_909_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_attrs_901_);
lean_inc(v_docString_x3f_895_);
lean_inc(v_stx_894_);
lean_dec(v_modifiers_892_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_909_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = lean_array_push(v_attrs_901_, v_attr_893_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 2, v___x_905_);
v___x_907_ = v___x_903_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_stx_894_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_docString_x3f_895_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v___x_905_);
lean_ctor_set_uint8(v_reuseFailAlloc_908_, sizeof(void*)*3, v_visibility_896_);
lean_ctor_set_uint8(v_reuseFailAlloc_908_, sizeof(void*)*3 + 1, v_isProtected_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_908_, sizeof(void*)*3 + 2, v_computeKind_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_908_, sizeof(void*)*3 + 3, v_recKind_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_908_, sizeof(void*)*3 + 4, v_isUnsafe_900_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addFirstAttr(lean_object* v_modifiers_910_, lean_object* v_attr_911_){
_start:
{
lean_object* v_stx_912_; lean_object* v_docString_x3f_913_; uint8_t v_visibility_914_; uint8_t v_isProtected_915_; uint8_t v_computeKind_916_; uint8_t v_recKind_917_; uint8_t v_isUnsafe_918_; lean_object* v_attrs_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_930_; 
v_stx_912_ = lean_ctor_get(v_modifiers_910_, 0);
v_docString_x3f_913_ = lean_ctor_get(v_modifiers_910_, 1);
v_visibility_914_ = lean_ctor_get_uint8(v_modifiers_910_, sizeof(void*)*3);
v_isProtected_915_ = lean_ctor_get_uint8(v_modifiers_910_, sizeof(void*)*3 + 1);
v_computeKind_916_ = lean_ctor_get_uint8(v_modifiers_910_, sizeof(void*)*3 + 2);
v_recKind_917_ = lean_ctor_get_uint8(v_modifiers_910_, sizeof(void*)*3 + 3);
v_isUnsafe_918_ = lean_ctor_get_uint8(v_modifiers_910_, sizeof(void*)*3 + 4);
v_attrs_919_ = lean_ctor_get(v_modifiers_910_, 2);
v_isSharedCheck_930_ = !lean_is_exclusive(v_modifiers_910_);
if (v_isSharedCheck_930_ == 0)
{
v___x_921_ = v_modifiers_910_;
v_isShared_922_ = v_isSharedCheck_930_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_attrs_919_);
lean_inc(v_docString_x3f_913_);
lean_inc(v_stx_912_);
lean_dec(v_modifiers_910_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_930_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = lean_mk_empty_array_with_capacity(v___x_923_);
v___x_925_ = lean_array_push(v___x_924_, v_attr_911_);
v___x_926_ = l_Array_append___redArg(v___x_925_, v_attrs_919_);
lean_dec_ref(v_attrs_919_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 2, v___x_926_);
v___x_928_ = v___x_921_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_stx_912_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_docString_x3f_913_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v___x_926_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*3, v_visibility_914_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*3 + 1, v_isProtected_915_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*3 + 2, v_computeKind_916_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*3 + 3, v_recKind_917_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*3 + 4, v_isUnsafe_918_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(lean_object* v_p_931_, lean_object* v_as_932_, size_t v_i_933_, size_t v_stop_934_, lean_object* v_b_935_){
_start:
{
lean_object* v___y_937_; uint8_t v___x_941_; 
v___x_941_ = lean_usize_dec_eq(v_i_933_, v_stop_934_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_942_ = lean_array_uget_borrowed(v_as_932_, v_i_933_);
lean_inc_ref(v_p_931_);
lean_inc(v___x_942_);
v___x_943_ = lean_apply_1(v_p_931_, v___x_942_);
v___x_944_ = lean_unbox(v___x_943_);
if (v___x_944_ == 0)
{
v___y_937_ = v_b_935_;
goto v___jp_936_;
}
else
{
lean_object* v___x_945_; 
lean_inc(v___x_942_);
v___x_945_ = lean_array_push(v_b_935_, v___x_942_);
v___y_937_ = v___x_945_;
goto v___jp_936_;
}
}
else
{
lean_dec_ref(v_p_931_);
return v_b_935_;
}
v___jp_936_:
{
size_t v___x_938_; size_t v___x_939_; 
v___x_938_ = ((size_t)1ULL);
v___x_939_ = lean_usize_add(v_i_933_, v___x_938_);
v_i_933_ = v___x_939_;
v_b_935_ = v___y_937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0___boxed(lean_object* v_p_946_, lean_object* v_as_947_, lean_object* v_i_948_, lean_object* v_stop_949_, lean_object* v_b_950_){
_start:
{
size_t v_i_boxed_951_; size_t v_stop_boxed_952_; lean_object* v_res_953_; 
v_i_boxed_951_ = lean_unbox_usize(v_i_948_);
lean_dec(v_i_948_);
v_stop_boxed_952_ = lean_unbox_usize(v_stop_949_);
lean_dec(v_stop_949_);
v_res_953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_946_, v_as_947_, v_i_boxed_951_, v_stop_boxed_952_, v_b_950_);
lean_dec_ref(v_as_947_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object* v_modifiers_954_, lean_object* v_p_955_){
_start:
{
lean_object* v_stx_956_; lean_object* v_docString_x3f_957_; uint8_t v_visibility_958_; uint8_t v_isProtected_959_; uint8_t v_computeKind_960_; uint8_t v_recKind_961_; uint8_t v_isUnsafe_962_; lean_object* v_attrs_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_990_; 
v_stx_956_ = lean_ctor_get(v_modifiers_954_, 0);
v_docString_x3f_957_ = lean_ctor_get(v_modifiers_954_, 1);
v_visibility_958_ = lean_ctor_get_uint8(v_modifiers_954_, sizeof(void*)*3);
v_isProtected_959_ = lean_ctor_get_uint8(v_modifiers_954_, sizeof(void*)*3 + 1);
v_computeKind_960_ = lean_ctor_get_uint8(v_modifiers_954_, sizeof(void*)*3 + 2);
v_recKind_961_ = lean_ctor_get_uint8(v_modifiers_954_, sizeof(void*)*3 + 3);
v_isUnsafe_962_ = lean_ctor_get_uint8(v_modifiers_954_, sizeof(void*)*3 + 4);
v_attrs_963_ = lean_ctor_get(v_modifiers_954_, 2);
v_isSharedCheck_990_ = !lean_is_exclusive(v_modifiers_954_);
if (v_isSharedCheck_990_ == 0)
{
v___x_965_ = v_modifiers_954_;
v_isShared_966_ = v_isSharedCheck_990_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_attrs_963_);
lean_inc(v_docString_x3f_957_);
lean_inc(v_stx_956_);
lean_dec(v_modifiers_954_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_990_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_array_get_size(v_attrs_963_);
v___x_969_ = ((lean_object*)(l_Lean_Elab_instInhabitedModifiers_default___closed__0));
v___x_970_ = lean_nat_dec_lt(v___x_967_, v___x_968_);
if (v___x_970_ == 0)
{
lean_object* v___x_972_; 
lean_dec_ref(v_attrs_963_);
lean_dec_ref(v_p_955_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 2, v___x_969_);
v___x_972_ = v___x_965_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_stx_956_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_docString_x3f_957_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v___x_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3, v_visibility_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3 + 1, v_isProtected_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3 + 2, v_computeKind_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3 + 3, v_recKind_961_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3 + 4, v_isUnsafe_962_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
else
{
uint8_t v___x_974_; 
v___x_974_ = lean_nat_dec_le(v___x_968_, v___x_968_);
if (v___x_974_ == 0)
{
if (v___x_970_ == 0)
{
lean_object* v___x_976_; 
lean_dec_ref(v_attrs_963_);
lean_dec_ref(v_p_955_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 2, v___x_969_);
v___x_976_ = v___x_965_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_stx_956_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_docString_x3f_957_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v___x_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*3, v_visibility_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*3 + 1, v_isProtected_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*3 + 2, v_computeKind_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*3 + 3, v_recKind_961_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*3 + 4, v_isUnsafe_962_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
else
{
size_t v___x_978_; size_t v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_978_ = ((size_t)0ULL);
v___x_979_ = lean_usize_of_nat(v___x_968_);
v___x_980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_955_, v_attrs_963_, v___x_978_, v___x_979_, v___x_969_);
lean_dec_ref(v_attrs_963_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 2, v___x_980_);
v___x_982_ = v___x_965_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_stx_956_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_docString_x3f_957_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v___x_980_);
lean_ctor_set_uint8(v_reuseFailAlloc_983_, sizeof(void*)*3, v_visibility_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_983_, sizeof(void*)*3 + 1, v_isProtected_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_983_, sizeof(void*)*3 + 2, v_computeKind_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_983_, sizeof(void*)*3 + 3, v_recKind_961_);
lean_ctor_set_uint8(v_reuseFailAlloc_983_, sizeof(void*)*3 + 4, v_isUnsafe_962_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
else
{
size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_984_ = ((size_t)0ULL);
v___x_985_ = lean_usize_of_nat(v___x_968_);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_955_, v_attrs_963_, v___x_984_, v___x_985_, v___x_969_);
lean_dec_ref(v_attrs_963_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 2, v___x_986_);
v___x_988_ = v___x_965_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_stx_956_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_docString_x3f_957_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v___x_986_);
lean_ctor_set_uint8(v_reuseFailAlloc_989_, sizeof(void*)*3, v_visibility_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_989_, sizeof(void*)*3 + 1, v_isProtected_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_989_, sizeof(void*)*3 + 2, v_computeKind_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_989_, sizeof(void*)*3 + 3, v_recKind_961_);
lean_ctor_set_uint8(v_reuseFailAlloc_989_, sizeof(void*)*3 + 4, v_isUnsafe_962_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(lean_object* v_p_991_, lean_object* v_as_992_, size_t v_i_993_, size_t v_stop_994_){
_start:
{
uint8_t v___x_995_; 
v___x_995_ = lean_usize_dec_eq(v_i_993_, v_stop_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_996_ = lean_array_uget_borrowed(v_as_992_, v_i_993_);
lean_inc_ref(v_p_991_);
lean_inc(v___x_996_);
v___x_997_ = lean_apply_1(v_p_991_, v___x_996_);
v___x_998_ = lean_unbox(v___x_997_);
if (v___x_998_ == 0)
{
size_t v___x_999_; size_t v___x_1000_; 
v___x_999_ = ((size_t)1ULL);
v___x_1000_ = lean_usize_add(v_i_993_, v___x_999_);
v_i_993_ = v___x_1000_;
goto _start;
}
else
{
uint8_t v___x_1002_; 
lean_dec_ref(v_p_991_);
v___x_1002_ = lean_unbox(v___x_997_);
return v___x_1002_;
}
}
else
{
uint8_t v___x_1003_; 
lean_dec_ref(v_p_991_);
v___x_1003_ = 0;
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0___boxed(lean_object* v_p_1004_, lean_object* v_as_1005_, lean_object* v_i_1006_, lean_object* v_stop_1007_){
_start:
{
size_t v_i_boxed_1008_; size_t v_stop_boxed_1009_; uint8_t v_res_1010_; lean_object* v_r_1011_; 
v_i_boxed_1008_ = lean_unbox_usize(v_i_1006_);
lean_dec(v_i_1006_);
v_stop_boxed_1009_ = lean_unbox_usize(v_stop_1007_);
lean_dec(v_stop_1007_);
v_res_1010_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_1004_, v_as_1005_, v_i_boxed_1008_, v_stop_boxed_1009_);
lean_dec_ref(v_as_1005_);
v_r_1011_ = lean_box(v_res_1010_);
return v_r_1011_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_anyAttr(lean_object* v_modifiers_1012_, lean_object* v_p_1013_){
_start:
{
lean_object* v_attrs_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_attrs_1014_ = lean_ctor_get(v_modifiers_1012_, 2);
v___x_1015_ = lean_unsigned_to_nat(0u);
v___x_1016_ = lean_array_get_size(v_attrs_1014_);
v___x_1017_ = lean_nat_dec_lt(v___x_1015_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_dec_ref(v_p_1013_);
return v___x_1017_;
}
else
{
if (v___x_1017_ == 0)
{
lean_dec_ref(v_p_1013_);
return v___x_1017_;
}
else
{
size_t v___x_1018_; size_t v___x_1019_; uint8_t v___x_1020_; 
v___x_1018_ = ((size_t)0ULL);
v___x_1019_ = lean_usize_of_nat(v___x_1016_);
v___x_1020_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_1013_, v_attrs_1014_, v___x_1018_, v___x_1019_);
return v___x_1020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_anyAttr___boxed(lean_object* v_modifiers_1021_, lean_object* v_p_1022_){
_start:
{
uint8_t v_res_1023_; lean_object* v_r_1024_; 
v_res_1023_ = l_Lean_Elab_Modifiers_anyAttr(v_modifiers_1021_, v_p_1022_);
lean_dec_ref(v_modifiers_1021_);
v_r_1024_ = lean_box(v_res_1023_);
return v_r_1024_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__0));
v___x_1028_ = lean_string_length(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__2, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__2_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2);
v___x_1030_ = lean_nat_to_int(v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__0(lean_object* v_attr_1037_){
_start:
{
uint8_t v_kind_1038_; lean_object* v_name_1039_; lean_object* v_stx_1040_; lean_object* v___y_1042_; 
v_kind_1038_ = lean_ctor_get_uint8(v_attr_1037_, sizeof(void*)*2);
v_name_1039_ = lean_ctor_get(v_attr_1037_, 0);
lean_inc(v_name_1039_);
v_stx_1040_ = lean_ctor_get(v_attr_1037_, 1);
lean_inc(v_stx_1040_);
lean_dec_ref(v_attr_1037_);
switch(v_kind_1038_)
{
case 0:
{
lean_object* v___x_1064_; 
v___x_1064_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4));
v___y_1042_ = v___x_1064_;
goto v___jp_1041_;
}
case 1:
{
lean_object* v___x_1065_; 
v___x_1065_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__6));
v___y_1042_ = v___x_1065_;
goto v___jp_1041_;
}
default: 
{
lean_object* v___x_1066_; 
v___x_1066_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__7));
v___y_1042_ = v___x_1066_;
goto v___jp_1041_;
}
}
v___jp_1041_:
{
lean_object* v___x_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; 
lean_inc_ref(v___y_1042_);
v___x_1043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___y_1042_);
v___x_1044_ = 1;
v___x_1045_ = l_Lean_Name_toString(v_name_1039_, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1043_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_box(0);
v___x_1049_ = 0;
v___x_1050_ = l_Lean_Syntax_formatStx(v_stx_1040_, v___x_1048_, v___x_1049_);
v___x_1051_ = l_Std_Format_defWidth;
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = l_Std_Format_pretty(v___x_1050_, v___x_1051_, v___x_1052_, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1047_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__3, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__3_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3);
v___x_1057_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__4));
v___x_1058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v___x_1055_);
v___x_1059_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__5));
v___x_1060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1056_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = 0;
v___x_1063_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set_uint8(v___x_1063_, sizeof(void*)*1, v___x_1062_);
return v___x_1063_;
}
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__0));
v___x_1076_ = lean_string_length(v___x_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__5, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__5_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5);
v___x_1078_ = lean_nat_to_int(v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__1(lean_object* v___f_1135_, lean_object* v___f_1136_, lean_object* v_m_1137_){
_start:
{
lean_object* v_docString_x3f_1138_; uint8_t v_visibility_1139_; uint8_t v_isProtected_1140_; uint8_t v_computeKind_1141_; uint8_t v_recKind_1142_; uint8_t v_isUnsafe_1143_; lean_object* v_attrs_1144_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1190_; 
v_docString_x3f_1138_ = lean_ctor_get(v_m_1137_, 1);
lean_inc(v_docString_x3f_1138_);
v_visibility_1139_ = lean_ctor_get_uint8(v_m_1137_, sizeof(void*)*3);
v_isProtected_1140_ = lean_ctor_get_uint8(v_m_1137_, sizeof(void*)*3 + 1);
v_computeKind_1141_ = lean_ctor_get_uint8(v_m_1137_, sizeof(void*)*3 + 2);
v_recKind_1142_ = lean_ctor_get_uint8(v_m_1137_, sizeof(void*)*3 + 3);
v_isUnsafe_1143_ = lean_ctor_get_uint8(v_m_1137_, sizeof(void*)*3 + 4);
v_attrs_1144_ = lean_ctor_get(v_m_1137_, 2);
lean_inc_ref(v_attrs_1144_);
lean_dec_ref(v_m_1137_);
if (lean_obj_tag(v_docString_x3f_1138_) == 0)
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_box(0);
v___y_1190_ = v___x_1194_;
goto v___jp_1189_;
}
else
{
lean_object* v_val_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_val_1195_ = lean_ctor_get(v_docString_x3f_1138_, 0);
lean_inc(v_val_1195_);
lean_dec_ref_known(v_docString_x3f_1138_, 1);
v___x_1196_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__32));
v___x_1197_ = lean_box(0);
v___x_1198_ = 0;
v___x_1199_ = l_Lean_Syntax_formatStx(v_val_1195_, v___x_1197_, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1196_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__34));
v___x_1202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_box(0);
v___x_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1202_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___y_1190_ = v___x_1204_;
goto v___jp_1189_;
}
v___jp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v_components_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; 
lean_inc(v___y_1147_);
v___x_1148_ = l_List_appendTR___redArg(v___y_1146_, v___y_1147_);
v___x_1149_ = lean_array_to_list(v_attrs_1144_);
v___x_1150_ = lean_box(0);
v___x_1151_ = l_List_mapTR_loop___redArg(v___f_1135_, v___x_1149_, v___x_1150_);
v_components_1152_ = l_List_appendTR___redArg(v___x_1148_, v___x_1151_);
v___x_1153_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__3));
v___x_1154_ = l_Std_Format_joinSep___redArg(v___f_1136_, v_components_1152_, v___x_1153_);
v___x_1155_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__6, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__6_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6);
v___x_1156_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__7));
v___x_1157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v___x_1154_);
v___x_1158_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__8));
v___x_1159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1155_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = 0;
v___x_1162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*1, v___x_1161_);
return v___x_1162_;
}
v___jp_1163_:
{
lean_object* v___x_1166_; 
lean_inc(v___y_1165_);
v___x_1166_ = l_List_appendTR___redArg(v___y_1164_, v___y_1165_);
if (v_isUnsafe_1143_ == 0)
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_box(0);
v___y_1146_ = v___x_1166_;
v___y_1147_ = v___x_1167_;
goto v___jp_1145_;
}
else
{
lean_object* v___x_1168_; 
v___x_1168_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__11));
v___y_1146_ = v___x_1166_;
v___y_1147_ = v___x_1168_;
goto v___jp_1145_;
}
}
v___jp_1169_:
{
lean_object* v___x_1172_; 
lean_inc(v___y_1171_);
v___x_1172_ = l_List_appendTR___redArg(v___y_1170_, v___y_1171_);
switch(v_recKind_1142_)
{
case 0:
{
lean_object* v___x_1173_; 
v___x_1173_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__14));
v___y_1164_ = v___x_1172_;
v___y_1165_ = v___x_1173_;
goto v___jp_1163_;
}
case 1:
{
lean_object* v___x_1174_; 
v___x_1174_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__17));
v___y_1164_ = v___x_1172_;
v___y_1165_ = v___x_1174_;
goto v___jp_1163_;
}
default: 
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_box(0);
v___y_1164_ = v___x_1172_;
v___y_1165_ = v___x_1175_;
goto v___jp_1163_;
}
}
}
v___jp_1176_:
{
lean_object* v___x_1179_; 
lean_inc(v___y_1178_);
v___x_1179_ = l_List_appendTR___redArg(v___y_1177_, v___y_1178_);
switch(v_computeKind_1141_)
{
case 0:
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_box(0);
v___y_1170_ = v___x_1179_;
v___y_1171_ = v___x_1180_;
goto v___jp_1169_;
}
case 1:
{
lean_object* v___x_1181_; 
v___x_1181_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__20));
v___y_1170_ = v___x_1179_;
v___y_1171_ = v___x_1181_;
goto v___jp_1169_;
}
default: 
{
lean_object* v___x_1182_; 
v___x_1182_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__23));
v___y_1170_ = v___x_1179_;
v___y_1171_ = v___x_1182_;
goto v___jp_1169_;
}
}
}
v___jp_1183_:
{
lean_object* v___x_1186_; 
lean_inc(v___y_1185_);
v___x_1186_ = l_List_appendTR___redArg(v___y_1184_, v___y_1185_);
if (v_isProtected_1140_ == 0)
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_box(0);
v___y_1177_ = v___x_1186_;
v___y_1178_ = v___x_1187_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1188_; 
v___x_1188_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__26));
v___y_1177_ = v___x_1186_;
v___y_1178_ = v___x_1188_;
goto v___jp_1176_;
}
}
v___jp_1189_:
{
switch(v_visibility_1139_)
{
case 0:
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_box(0);
v___y_1184_ = v___y_1190_;
v___y_1185_ = v___x_1191_;
goto v___jp_1183_;
}
case 1:
{
lean_object* v___x_1192_; 
v___x_1192_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__28));
v___y_1184_ = v___y_1190_;
v___y_1185_ = v___x_1192_;
goto v___jp_1183_;
}
default: 
{
lean_object* v___x_1193_; 
v___x_1193_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__30));
v___y_1184_ = v___y_1190_;
v___y_1185_ = v___x_1193_;
goto v___jp_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lam__0(lean_object* v_f_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = l_Std_Format_defWidth;
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = l_Std_Format_pretty(v_f_1211_, v___x_1212_, v___x_1213_, v___x_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0));
v___x_1222_ = l_Lean_stringToMessageData(v___x_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg(lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_optDocComment_1226_){
_start:
{
lean_object* v_toApplicative_1227_; lean_object* v_toPure_1228_; lean_object* v___x_1229_; 
v_toApplicative_1227_ = lean_ctor_get(v_inst_1224_, 0);
v_toPure_1228_ = lean_ctor_get(v_toApplicative_1227_, 1);
v___x_1229_ = l_Lean_Syntax_getOptional_x3f(v_optDocComment_1226_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_inc(v_toPure_1228_);
lean_dec_ref(v_inst_1225_);
lean_dec_ref(v_inst_1224_);
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_apply_2(v_toPure_1228_, lean_box(0), v___x_1230_);
return v___x_1231_;
}
else
{
lean_object* v_val_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1274_; 
v_val_1232_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1234_ = v___x_1229_;
v_isShared_1235_ = v_isSharedCheck_1274_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_val_1232_);
lean_dec(v___x_1229_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1274_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = l_Lean_Syntax_getArg(v_val_1232_, v___x_1244_);
if (lean_obj_tag(v___x_1245_) == 1)
{
lean_object* v_kind_1246_; 
v_kind_1246_ = lean_ctor_get(v___x_1245_, 1);
lean_inc(v_kind_1246_);
if (lean_obj_tag(v_kind_1246_) == 1)
{
lean_object* v_pre_1247_; 
v_pre_1247_ = lean_ctor_get(v_kind_1246_, 0);
lean_inc(v_pre_1247_);
if (lean_obj_tag(v_pre_1247_) == 1)
{
lean_object* v_pre_1248_; 
v_pre_1248_ = lean_ctor_get(v_pre_1247_, 0);
lean_inc(v_pre_1248_);
if (lean_obj_tag(v_pre_1248_) == 1)
{
lean_object* v_pre_1249_; 
v_pre_1249_ = lean_ctor_get(v_pre_1248_, 0);
lean_inc(v_pre_1249_);
if (lean_obj_tag(v_pre_1249_) == 1)
{
lean_object* v_pre_1250_; 
v_pre_1250_ = lean_ctor_get(v_pre_1249_, 0);
if (lean_obj_tag(v_pre_1250_) == 0)
{
lean_object* v_args_1251_; lean_object* v_str_1252_; lean_object* v_str_1253_; lean_object* v_str_1254_; lean_object* v_str_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v_args_1251_ = lean_ctor_get(v___x_1245_, 2);
lean_inc_ref(v_args_1251_);
lean_dec_ref_known(v___x_1245_, 3);
v_str_1252_ = lean_ctor_get(v_kind_1246_, 1);
lean_inc_ref(v_str_1252_);
lean_dec_ref_known(v_kind_1246_, 2);
v_str_1253_ = lean_ctor_get(v_pre_1247_, 1);
lean_inc_ref(v_str_1253_);
lean_dec_ref_known(v_pre_1247_, 2);
v_str_1254_ = lean_ctor_get(v_pre_1248_, 1);
lean_inc_ref(v_str_1254_);
lean_dec_ref_known(v_pre_1248_, 2);
v_str_1255_ = lean_ctor_get(v_pre_1249_, 1);
lean_inc_ref(v_str_1255_);
lean_dec_ref_known(v_pre_1249_, 2);
v___x_1256_ = ((lean_object*)(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_));
v___x_1257_ = lean_string_dec_eq(v_str_1255_, v___x_1256_);
lean_dec_ref(v_str_1255_);
if (v___x_1257_ == 0)
{
lean_dec_ref(v_str_1254_);
lean_dec_ref(v_str_1253_);
lean_dec_ref(v_str_1252_);
lean_dec_ref(v_args_1251_);
lean_del_object(v___x_1234_);
goto v___jp_1236_;
}
else
{
lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1258_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6));
v___x_1259_ = lean_string_dec_eq(v_str_1254_, v___x_1258_);
lean_dec_ref(v_str_1254_);
if (v___x_1259_ == 0)
{
lean_dec_ref(v_str_1253_);
lean_dec_ref(v_str_1252_);
lean_dec_ref(v_args_1251_);
lean_del_object(v___x_1234_);
goto v___jp_1236_;
}
else
{
lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1260_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7));
v___x_1261_ = lean_string_dec_eq(v_str_1253_, v___x_1260_);
lean_dec_ref(v_str_1253_);
if (v___x_1261_ == 0)
{
lean_dec_ref(v_str_1252_);
lean_dec_ref(v_args_1251_);
lean_del_object(v___x_1234_);
goto v___jp_1236_;
}
else
{
lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = ((lean_object*)(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__2));
v___x_1263_ = lean_string_dec_eq(v_str_1252_, v___x_1262_);
lean_dec_ref(v_str_1252_);
if (v___x_1263_ == 0)
{
lean_dec_ref(v_args_1251_);
lean_del_object(v___x_1234_);
goto v___jp_1236_;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1264_ = lean_array_get_size(v_args_1251_);
v___x_1265_ = lean_unsigned_to_nat(2u);
v___x_1266_ = lean_nat_dec_eq(v___x_1264_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_dec_ref(v_args_1251_);
lean_del_object(v___x_1234_);
goto v___jp_1236_;
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_array_fget(v_args_1251_, v___x_1267_);
lean_dec_ref(v_args_1251_);
if (lean_obj_tag(v___x_1268_) == 2)
{
lean_object* v_val_1269_; lean_object* v___x_1271_; 
lean_inc(v_toPure_1228_);
lean_dec(v_val_1232_);
lean_dec_ref(v_inst_1225_);
lean_dec_ref(v_inst_1224_);
v_val_1269_ = lean_ctor_get(v___x_1268_, 1);
lean_inc_ref(v_val_1269_);
lean_dec_ref_known(v___x_1268_, 2);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v_val_1269_);
v___x_1271_ = v___x_1234_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_val_1269_);
v___x_1271_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_apply_2(v_toPure_1228_, lean_box(0), v___x_1271_);
return v___x_1272_;
}
}
else
{
lean_dec(v___x_1268_);
lean_del_object(v___x_1234_);
goto v___jp_1236_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1249_, 2);
lean_dec_ref_known(v_pre_1248_, 2);
lean_dec_ref_known(v_pre_1247_, 2);
lean_dec_ref_known(v_kind_1246_, 2);
lean_dec_ref_known(v___x_1245_, 3);
lean_del_object(v___x_1234_);
goto v___jp_1236_;
}
}
else
{
lean_dec_ref_known(v_pre_1248_, 2);
lean_dec(v_pre_1249_);
lean_dec_ref_known(v_pre_1247_, 2);
lean_dec_ref_known(v_kind_1246_, 2);
lean_dec_ref_known(v___x_1245_, 3);
lean_del_object(v___x_1234_);
goto v___jp_1236_;
}
}
else
{
lean_dec(v_pre_1248_);
lean_dec_ref_known(v_pre_1247_, 2);
lean_dec_ref_known(v_kind_1246_, 2);
lean_dec_ref_known(v___x_1245_, 3);
lean_del_object(v___x_1234_);
goto v___jp_1236_;
}
}
else
{
lean_dec(v_pre_1247_);
lean_dec_ref_known(v_kind_1246_, 2);
lean_dec_ref_known(v___x_1245_, 3);
lean_del_object(v___x_1234_);
goto v___jp_1236_;
}
}
else
{
lean_dec_ref_known(v___x_1245_, 3);
lean_dec(v_kind_1246_);
lean_del_object(v___x_1234_);
goto v___jp_1236_;
}
}
else
{
lean_dec(v___x_1245_);
lean_del_object(v___x_1234_);
goto v___jp_1236_;
}
v___jp_1236_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1237_ = lean_obj_once(&l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1, &l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1_once, _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1);
v___x_1238_ = lean_unsigned_to_nat(1u);
v___x_1239_ = l_Lean_Syntax_getArg(v_val_1232_, v___x_1238_);
v___x_1240_ = l_Lean_MessageData_ofSyntax(v___x_1239_);
v___x_1241_ = l_Lean_indentD(v___x_1240_);
v___x_1242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1237_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = l_Lean_throwErrorAt___redArg(v_inst_1224_, v_inst_1225_, v_val_1232_, v___x_1242_);
return v___x_1243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___boxed(lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_optDocComment_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1275_, v_inst_1276_, v_optDocComment_1277_);
lean_dec(v_optDocComment_1277_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f(lean_object* v_m_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_optDocComment_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1280_, v_inst_1281_, v_optDocComment_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___boxed(lean_object* v_m_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_optDocComment_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Elab_expandOptDocComment_x3f(v_m_1284_, v_inst_1285_, v_inst_1286_, v_optDocComment_1287_);
lean_dec(v_optDocComment_1287_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0(lean_object* v_stx_1289_, lean_object* v___y_1290_, uint8_t v_visibility_1291_, uint8_t v___y_1292_, uint8_t v___y_1293_, uint8_t v___y_1294_, lean_object* v_toPure_1295_, lean_object* v_unsafeStx_1296_, lean_object* v_attrs_1297_){
_start:
{
uint8_t v___y_1299_; uint8_t v___x_1302_; 
v___x_1302_ = l_Lean_Syntax_isNone(v_unsafeStx_1296_);
if (v___x_1302_ == 0)
{
uint8_t v___x_1303_; 
v___x_1303_ = 1;
v___y_1299_ = v___x_1303_;
goto v___jp_1298_;
}
else
{
uint8_t v___x_1304_; 
v___x_1304_ = 0;
v___y_1299_ = v___x_1304_;
goto v___jp_1298_;
}
v___jp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1300_, 0, v_stx_1289_);
lean_ctor_set(v___x_1300_, 1, v___y_1290_);
lean_ctor_set(v___x_1300_, 2, v_attrs_1297_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3, v_visibility_1291_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 1, v___y_1292_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 2, v___y_1293_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 3, v___y_1294_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 4, v___y_1299_);
v___x_1301_ = lean_apply_2(v_toPure_1295_, lean_box(0), v___x_1300_);
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0___boxed(lean_object* v_stx_1305_, lean_object* v___y_1306_, lean_object* v_visibility_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v_toPure_1311_, lean_object* v_unsafeStx_1312_, lean_object* v_attrs_1313_){
_start:
{
uint8_t v_visibility_boxed_1314_; uint8_t v___y_305__boxed_1315_; uint8_t v___y_306__boxed_1316_; uint8_t v___y_307__boxed_1317_; lean_object* v_res_1318_; 
v_visibility_boxed_1314_ = lean_unbox(v_visibility_1307_);
v___y_305__boxed_1315_ = lean_unbox(v___y_1308_);
v___y_306__boxed_1316_ = lean_unbox(v___y_1309_);
v___y_307__boxed_1317_ = lean_unbox(v___y_1310_);
v_res_1318_ = l_Lean_Elab_elabModifiers___redArg___lam__0(v_stx_1305_, v___y_1306_, v_visibility_boxed_1314_, v___y_305__boxed_1315_, v___y_306__boxed_1316_, v___y_307__boxed_1317_, v_toPure_1311_, v_unsafeStx_1312_, v_attrs_1313_);
lean_dec(v_unsafeStx_1312_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__1(lean_object* v___f_1319_, lean_object* v_attrs_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_apply_1(v___f_1319_, v_attrs_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3(lean_object* v_stx_1322_, lean_object* v___y_1323_, uint8_t v___y_1324_, uint8_t v___y_1325_, lean_object* v_toPure_1326_, lean_object* v_unsafeStx_1327_, lean_object* v_attrsStx_1328_, lean_object* v___x_1329_, lean_object* v_toBind_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_inst_1341_, lean_object* v_inst_1342_, lean_object* v_protectedStx_1343_, uint8_t v_visibility_1344_){
_start:
{
uint8_t v___y_1346_; uint8_t v___x_1361_; 
v___x_1361_ = l_Lean_Syntax_isNone(v_protectedStx_1343_);
if (v___x_1361_ == 0)
{
uint8_t v___x_1362_; 
v___x_1362_ = 1;
v___y_1346_ = v___x_1362_;
goto v___jp_1345_;
}
else
{
uint8_t v___x_1363_; 
v___x_1363_ = 0;
v___y_1346_ = v___x_1363_;
goto v___jp_1345_;
}
v___jp_1345_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___f_1351_; lean_object* v___x_1352_; 
v___x_1347_ = lean_box(v_visibility_1344_);
v___x_1348_ = lean_box(v___y_1346_);
v___x_1349_ = lean_box(v___y_1324_);
v___x_1350_ = lean_box(v___y_1325_);
lean_inc(v_toPure_1326_);
v___f_1351_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_1351_, 0, v_stx_1322_);
lean_closure_set(v___f_1351_, 1, v___y_1323_);
lean_closure_set(v___f_1351_, 2, v___x_1347_);
lean_closure_set(v___f_1351_, 3, v___x_1348_);
lean_closure_set(v___f_1351_, 4, v___x_1349_);
lean_closure_set(v___f_1351_, 5, v___x_1350_);
lean_closure_set(v___f_1351_, 6, v_toPure_1326_);
lean_closure_set(v___f_1351_, 7, v_unsafeStx_1327_);
v___x_1352_ = l_Lean_Syntax_getOptional_x3f(v_attrsStx_1328_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v___f_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v_inst_1342_);
lean_dec(v_inst_1341_);
lean_dec_ref(v_inst_1340_);
lean_dec(v_inst_1339_);
lean_dec_ref(v_inst_1338_);
lean_dec_ref(v_inst_1337_);
lean_dec_ref(v_inst_1336_);
lean_dec_ref(v_inst_1335_);
lean_dec_ref(v_inst_1334_);
lean_dec_ref(v_inst_1333_);
lean_dec_ref(v_inst_1332_);
lean_dec_ref(v_inst_1331_);
v___f_1353_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1353_, 0, v___f_1351_);
v___x_1354_ = lean_mk_empty_array_with_capacity(v___x_1329_);
v___x_1355_ = lean_apply_2(v_toPure_1326_, lean_box(0), v___x_1354_);
v___x_1356_ = lean_apply_4(v_toBind_1330_, lean_box(0), lean_box(0), v___x_1355_, v___f_1353_);
return v___x_1356_;
}
else
{
lean_object* v_val_1357_; lean_object* v___f_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec(v_toPure_1326_);
v_val_1357_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_val_1357_);
lean_dec_ref_known(v___x_1352_, 1);
v___f_1358_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1358_, 0, v___f_1351_);
v___x_1359_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_1331_, v_inst_1332_, v_inst_1333_, v_inst_1334_, v_inst_1335_, v_inst_1336_, v_inst_1337_, v_inst_1338_, v_inst_1339_, v_inst_1340_, v_inst_1341_, v_inst_1342_, v_val_1357_);
lean_dec(v_val_1357_);
v___x_1360_ = lean_apply_4(v_toBind_1330_, lean_box(0), lean_box(0), v___x_1359_, v___f_1358_);
return v___x_1360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_stx_1364_ = _args[0];
lean_object* v___y_1365_ = _args[1];
lean_object* v___y_1366_ = _args[2];
lean_object* v___y_1367_ = _args[3];
lean_object* v_toPure_1368_ = _args[4];
lean_object* v_unsafeStx_1369_ = _args[5];
lean_object* v_attrsStx_1370_ = _args[6];
lean_object* v___x_1371_ = _args[7];
lean_object* v_toBind_1372_ = _args[8];
lean_object* v_inst_1373_ = _args[9];
lean_object* v_inst_1374_ = _args[10];
lean_object* v_inst_1375_ = _args[11];
lean_object* v_inst_1376_ = _args[12];
lean_object* v_inst_1377_ = _args[13];
lean_object* v_inst_1378_ = _args[14];
lean_object* v_inst_1379_ = _args[15];
lean_object* v_inst_1380_ = _args[16];
lean_object* v_inst_1381_ = _args[17];
lean_object* v_inst_1382_ = _args[18];
lean_object* v_inst_1383_ = _args[19];
lean_object* v_inst_1384_ = _args[20];
lean_object* v_protectedStx_1385_ = _args[21];
lean_object* v_visibility_1386_ = _args[22];
_start:
{
uint8_t v___y_335__boxed_1387_; uint8_t v___y_336__boxed_1388_; uint8_t v_visibility_boxed_1389_; lean_object* v_res_1390_; 
v___y_335__boxed_1387_ = lean_unbox(v___y_1366_);
v___y_336__boxed_1388_ = lean_unbox(v___y_1367_);
v_visibility_boxed_1389_ = lean_unbox(v_visibility_1386_);
v_res_1390_ = l_Lean_Elab_elabModifiers___redArg___lam__3(v_stx_1364_, v___y_1365_, v___y_335__boxed_1387_, v___y_336__boxed_1388_, v_toPure_1368_, v_unsafeStx_1369_, v_attrsStx_1370_, v___x_1371_, v_toBind_1372_, v_inst_1373_, v_inst_1374_, v_inst_1375_, v_inst_1376_, v_inst_1377_, v_inst_1378_, v_inst_1379_, v_inst_1380_, v_inst_1381_, v_inst_1382_, v_inst_1383_, v_inst_1384_, v_protectedStx_1385_, v_visibility_boxed_1389_);
lean_dec(v_protectedStx_1385_);
lean_dec(v___x_1371_);
lean_dec(v_attrsStx_1370_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg(lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v_inst_1405_, lean_object* v_inst_1406_, lean_object* v_inst_1407_, lean_object* v_inst_1408_, lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_stx_1413_, uint8_t v_isExample_1414_){
_start:
{
lean_object* v_toApplicative_1415_; lean_object* v_toBind_1416_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v_toPure_1422_; lean_object* v___x_1423_; lean_object* v_docCommentStx_1424_; lean_object* v___x_1425_; lean_object* v_attrsStx_1426_; lean_object* v___x_1427_; lean_object* v_visibilityStx_1428_; lean_object* v___x_1429_; lean_object* v_protectedStx_1430_; uint8_t v___y_1432_; uint8_t v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; uint8_t v___y_1450_; lean_object* v___y_1451_; uint8_t v___y_1452_; uint8_t v___y_1464_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v_toApplicative_1415_ = lean_ctor_get(v_inst_1401_, 0);
v_toBind_1416_ = lean_ctor_get(v_inst_1401_, 1);
lean_inc(v_toBind_1416_);
v_toPure_1422_ = lean_ctor_get(v_toApplicative_1415_, 1);
v___x_1423_ = lean_unsigned_to_nat(0u);
v_docCommentStx_1424_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1423_);
v___x_1425_ = lean_unsigned_to_nat(1u);
v_attrsStx_1426_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1425_);
v___x_1427_ = lean_unsigned_to_nat(2u);
v_visibilityStx_1428_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1427_);
v___x_1429_ = lean_unsigned_to_nat(3u);
v_protectedStx_1430_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1429_);
v___x_1477_ = lean_unsigned_to_nat(4u);
v___x_1478_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1477_);
v___x_1479_ = l_Lean_Syntax_isNone(v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
v___x_1480_ = l_Lean_Syntax_getArg(v___x_1478_, v___x_1423_);
lean_dec(v___x_1478_);
v___x_1481_ = l_Lean_Syntax_getKind(v___x_1480_);
v___x_1482_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__1));
v___x_1483_ = lean_name_eq(v___x_1481_, v___x_1482_);
lean_dec(v___x_1481_);
if (v___x_1483_ == 0)
{
uint8_t v___x_1484_; 
v___x_1484_ = 2;
v___y_1464_ = v___x_1484_;
goto v___jp_1463_;
}
else
{
uint8_t v___x_1485_; 
v___x_1485_ = 1;
v___y_1464_ = v___x_1485_;
goto v___jp_1463_;
}
}
else
{
uint8_t v___x_1486_; 
lean_dec(v___x_1478_);
v___x_1486_ = 0;
v___y_1464_ = v___x_1486_;
goto v___jp_1463_;
}
v___jp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = l_Lean_Elab_elabVisibility___redArg(v_inst_1401_, v_inst_1404_, v_inst_1402_, v_inst_1409_, v_inst_1411_, v_inst_1410_, v___y_1419_, v_isExample_1414_);
v___x_1421_ = lean_apply_4(v_toBind_1416_, lean_box(0), lean_box(0), v___x_1420_, v___y_1418_);
return v___x_1421_;
}
v___jp_1431_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; 
v___x_1436_ = lean_box(v___y_1433_);
v___x_1437_ = lean_box(v___y_1432_);
lean_inc_ref(v_inst_1411_);
lean_inc(v_inst_1410_);
lean_inc_ref(v_inst_1409_);
lean_inc_ref(v_inst_1404_);
lean_inc_ref(v_inst_1402_);
lean_inc_ref(v_inst_1401_);
lean_inc(v_toBind_1416_);
lean_inc(v_toPure_1422_);
v___f_1438_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__3___boxed), 23, 22);
lean_closure_set(v___f_1438_, 0, v_stx_1413_);
lean_closure_set(v___f_1438_, 1, v___y_1435_);
lean_closure_set(v___f_1438_, 2, v___x_1436_);
lean_closure_set(v___f_1438_, 3, v___x_1437_);
lean_closure_set(v___f_1438_, 4, v_toPure_1422_);
lean_closure_set(v___f_1438_, 5, v___y_1434_);
lean_closure_set(v___f_1438_, 6, v_attrsStx_1426_);
lean_closure_set(v___f_1438_, 7, v___x_1423_);
lean_closure_set(v___f_1438_, 8, v_toBind_1416_);
lean_closure_set(v___f_1438_, 9, v_inst_1401_);
lean_closure_set(v___f_1438_, 10, v_inst_1402_);
lean_closure_set(v___f_1438_, 11, v_inst_1403_);
lean_closure_set(v___f_1438_, 12, v_inst_1404_);
lean_closure_set(v___f_1438_, 13, v_inst_1406_);
lean_closure_set(v___f_1438_, 14, v_inst_1407_);
lean_closure_set(v___f_1438_, 15, v_inst_1408_);
lean_closure_set(v___f_1438_, 16, v_inst_1409_);
lean_closure_set(v___f_1438_, 17, v_inst_1410_);
lean_closure_set(v___f_1438_, 18, v_inst_1411_);
lean_closure_set(v___f_1438_, 19, v_inst_1412_);
lean_closure_set(v___f_1438_, 20, v_inst_1405_);
lean_closure_set(v___f_1438_, 21, v_protectedStx_1430_);
v___x_1439_ = l_Lean_Syntax_getOptional_x3f(v_visibilityStx_1428_);
lean_dec(v_visibilityStx_1428_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_box(0);
v___y_1418_ = v___f_1438_;
v___y_1419_ = v___x_1440_;
goto v___jp_1417_;
}
else
{
lean_object* v_val_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_val_1441_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1439_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_val_1441_);
lean_dec(v___x_1439_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_val_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
v___y_1418_ = v___f_1438_;
v___y_1419_ = v___x_1446_;
goto v___jp_1417_;
}
}
}
}
v___jp_1449_:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_Syntax_getOptional_x3f(v_docCommentStx_1424_);
lean_dec(v_docCommentStx_1424_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_box(0);
v___y_1432_ = v___y_1452_;
v___y_1433_ = v___y_1450_;
v___y_1434_ = v___y_1451_;
v___y_1435_ = v___x_1454_;
goto v___jp_1431_;
}
else
{
lean_object* v_val_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
v_val_1455_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1453_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_val_1455_);
lean_dec(v___x_1453_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_val_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
v___y_1432_ = v___y_1452_;
v___y_1433_ = v___y_1450_;
v___y_1434_ = v___y_1451_;
v___y_1435_ = v___x_1460_;
goto v___jp_1431_;
}
}
}
}
v___jp_1463_:
{
lean_object* v___x_1465_; lean_object* v_unsafeStx_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1465_ = lean_unsigned_to_nat(5u);
v_unsafeStx_1466_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1465_);
v___x_1467_ = lean_unsigned_to_nat(6u);
v___x_1468_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1467_);
v___x_1469_ = l_Lean_Syntax_isNone(v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1470_ = l_Lean_Syntax_getArg(v___x_1468_, v___x_1423_);
lean_dec(v___x_1468_);
v___x_1471_ = l_Lean_Syntax_getKind(v___x_1470_);
v___x_1472_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__0));
v___x_1473_ = lean_name_eq(v___x_1471_, v___x_1472_);
lean_dec(v___x_1471_);
if (v___x_1473_ == 0)
{
uint8_t v___x_1474_; 
v___x_1474_ = 1;
v___y_1450_ = v___y_1464_;
v___y_1451_ = v_unsafeStx_1466_;
v___y_1452_ = v___x_1474_;
goto v___jp_1449_;
}
else
{
uint8_t v___x_1475_; 
v___x_1475_ = 0;
v___y_1450_ = v___y_1464_;
v___y_1451_ = v_unsafeStx_1466_;
v___y_1452_ = v___x_1475_;
goto v___jp_1449_;
}
}
else
{
uint8_t v___x_1476_; 
lean_dec(v___x_1468_);
v___x_1476_ = 2;
v___y_1450_ = v___y_1464_;
v___y_1451_ = v_unsafeStx_1466_;
v___y_1452_ = v___x_1476_;
goto v___jp_1449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___boxed(lean_object* v_inst_1487_, lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_inst_1490_, lean_object* v_inst_1491_, lean_object* v_inst_1492_, lean_object* v_inst_1493_, lean_object* v_inst_1494_, lean_object* v_inst_1495_, lean_object* v_inst_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_stx_1499_, lean_object* v_isExample_1500_){
_start:
{
uint8_t v_isExample_boxed_1501_; lean_object* v_res_1502_; 
v_isExample_boxed_1501_ = lean_unbox(v_isExample_1500_);
v_res_1502_ = l_Lean_Elab_elabModifiers___redArg(v_inst_1487_, v_inst_1488_, v_inst_1489_, v_inst_1490_, v_inst_1491_, v_inst_1492_, v_inst_1493_, v_inst_1494_, v_inst_1495_, v_inst_1496_, v_inst_1497_, v_inst_1498_, v_stx_1499_, v_isExample_boxed_1501_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object* v_m_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_inst_1513_, lean_object* v_inst_1514_, lean_object* v_inst_1515_, lean_object* v_stx_1516_, uint8_t v_isExample_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_Elab_elabModifiers___redArg(v_inst_1504_, v_inst_1505_, v_inst_1506_, v_inst_1507_, v_inst_1508_, v_inst_1509_, v_inst_1510_, v_inst_1511_, v_inst_1512_, v_inst_1513_, v_inst_1514_, v_inst_1515_, v_stx_1516_, v_isExample_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___boxed(lean_object* v_m_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_inst_1529_, lean_object* v_inst_1530_, lean_object* v_inst_1531_, lean_object* v_stx_1532_, lean_object* v_isExample_1533_){
_start:
{
uint8_t v_isExample_boxed_1534_; lean_object* v_res_1535_; 
v_isExample_boxed_1534_ = lean_unbox(v_isExample_1533_);
v_res_1535_ = l_Lean_Elab_elabModifiers(v_m_1519_, v_inst_1520_, v_inst_1521_, v_inst_1522_, v_inst_1523_, v_inst_1524_, v_inst_1525_, v_inst_1526_, v_inst_1527_, v_inst_1528_, v_inst_1529_, v_inst_1530_, v_inst_1531_, v_stx_1532_, v_isExample_boxed_1534_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__0(lean_object* v_toPure_1536_, lean_object* v_declName_1537_, lean_object* v_____r_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_apply_2(v_toPure_1536_, lean_box(0), v_declName_1537_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__1(lean_object* v_declName_1540_, lean_object* v_env_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_addProtected(v_env_1541_, v_declName_1540_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2(lean_object* v_modifiers_1543_, lean_object* v_toPure_1544_, lean_object* v_declName_1545_, lean_object* v_modifyEnv_1546_, lean_object* v___f_1547_, lean_object* v_toBind_1548_, lean_object* v___f_1549_, lean_object* v_____r_1550_){
_start:
{
uint8_t v_isProtected_1551_; 
v_isProtected_1551_ = lean_ctor_get_uint8(v_modifiers_1543_, sizeof(void*)*3 + 1);
if (v_isProtected_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_dec(v___f_1549_);
lean_dec(v_toBind_1548_);
lean_dec_ref(v___f_1547_);
lean_dec(v_modifyEnv_1546_);
v___x_1552_ = lean_apply_2(v_toPure_1544_, lean_box(0), v_declName_1545_);
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_dec(v_declName_1545_);
lean_dec(v_toPure_1544_);
v___x_1553_ = lean_apply_1(v_modifyEnv_1546_, v___f_1547_);
v___x_1554_ = lean_apply_4(v_toBind_1548_, lean_box(0), lean_box(0), v___x_1553_, v___f_1549_);
return v___x_1554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2___boxed(lean_object* v_modifiers_1555_, lean_object* v_toPure_1556_, lean_object* v_declName_1557_, lean_object* v_modifyEnv_1558_, lean_object* v___f_1559_, lean_object* v_toBind_1560_, lean_object* v___f_1561_, lean_object* v_____r_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Elab_applyVisibility___redArg___lam__2(v_modifiers_1555_, v_toPure_1556_, v_declName_1557_, v_modifyEnv_1558_, v___f_1559_, v_toBind_1560_, v___f_1561_, v_____r_1562_);
lean_dec_ref(v_modifiers_1555_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__3(lean_object* v_toPure_1564_, lean_object* v_modifiers_1565_, lean_object* v_modifyEnv_1566_, lean_object* v_toBind_1567_, lean_object* v_inst_1568_, lean_object* v_inst_1569_, lean_object* v_inst_1570_, lean_object* v_inst_1571_, lean_object* v_inst_1572_, lean_object* v_____r_1573_, lean_object* v_declName_1574_){
_start:
{
lean_object* v___f_1575_; lean_object* v___f_1576_; lean_object* v___f_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_inc_n(v_declName_1574_, 3);
lean_inc(v_toPure_1564_);
v___f_1575_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1575_, 0, v_toPure_1564_);
lean_closure_set(v___f_1575_, 1, v_declName_1574_);
v___f_1576_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1576_, 0, v_declName_1574_);
lean_inc(v_toBind_1567_);
v___f_1577_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1577_, 0, v_modifiers_1565_);
lean_closure_set(v___f_1577_, 1, v_toPure_1564_);
lean_closure_set(v___f_1577_, 2, v_declName_1574_);
lean_closure_set(v___f_1577_, 3, v_modifyEnv_1566_);
lean_closure_set(v___f_1577_, 4, v___f_1576_);
lean_closure_set(v___f_1577_, 5, v_toBind_1567_);
lean_closure_set(v___f_1577_, 6, v___f_1575_);
v___x_1578_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(v_inst_1568_, v_inst_1569_, v_inst_1570_, v_inst_1571_, v_inst_1572_, v_declName_1574_);
v___x_1579_ = lean_apply_4(v_toBind_1567_, lean_box(0), lean_box(0), v___x_1578_, v___f_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4(lean_object* v_declName_1580_, lean_object* v___f_1581_, lean_object* v_____do__lift_1582_){
_start:
{
lean_object* v_declName_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v_declName_1583_ = l_Lean_mkPrivateName(v_____do__lift_1582_, v_declName_1580_);
v___x_1584_ = lean_box(0);
v___x_1585_ = lean_apply_2(v___f_1581_, v___x_1584_, v_declName_1583_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4___boxed(lean_object* v_declName_1586_, lean_object* v___f_1587_, lean_object* v_____do__lift_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_Elab_applyVisibility___redArg___lam__4(v_declName_1586_, v___f_1587_, v_____do__lift_1588_);
lean_dec_ref(v_____do__lift_1588_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5(lean_object* v_modifiers_1590_, lean_object* v_toBind_1591_, lean_object* v_getEnv_1592_, lean_object* v___f_1593_, lean_object* v___f_1594_, lean_object* v_declName_1595_, lean_object* v_____do__lift_1596_){
_start:
{
uint8_t v_visibility_1597_; uint8_t v___x_1598_; 
v_visibility_1597_ = lean_ctor_get_uint8(v_modifiers_1590_, sizeof(void*)*3);
v___x_1598_ = l_Lean_Elab_Visibility_isInferredPublic(v_____do__lift_1596_, v_visibility_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; 
lean_dec(v_declName_1595_);
lean_dec(v___f_1594_);
v___x_1599_ = lean_apply_4(v_toBind_1591_, lean_box(0), lean_box(0), v_getEnv_1592_, v___f_1593_);
return v___x_1599_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec(v___f_1593_);
lean_dec(v_getEnv_1592_);
lean_dec(v_toBind_1591_);
v___x_1600_ = lean_box(0);
v___x_1601_ = lean_apply_2(v___f_1594_, v___x_1600_, v_declName_1595_);
return v___x_1601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5___boxed(lean_object* v_modifiers_1602_, lean_object* v_toBind_1603_, lean_object* v_getEnv_1604_, lean_object* v___f_1605_, lean_object* v___f_1606_, lean_object* v_declName_1607_, lean_object* v_____do__lift_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_Elab_applyVisibility___redArg___lam__5(v_modifiers_1602_, v_toBind_1603_, v_getEnv_1604_, v___f_1605_, v___f_1606_, v_declName_1607_, v_____do__lift_1608_);
lean_dec_ref(v_____do__lift_1608_);
lean_dec_ref(v_modifiers_1602_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg(lean_object* v_inst_1610_, lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_inst_1614_, lean_object* v_modifiers_1615_, lean_object* v_declName_1616_){
_start:
{
lean_object* v_toApplicative_1617_; lean_object* v_toBind_1618_; lean_object* v_getEnv_1619_; lean_object* v_modifyEnv_1620_; lean_object* v_toPure_1621_; lean_object* v___f_1622_; lean_object* v___f_1623_; lean_object* v___f_1624_; lean_object* v___x_1625_; 
v_toApplicative_1617_ = lean_ctor_get(v_inst_1610_, 0);
v_toBind_1618_ = lean_ctor_get(v_inst_1610_, 1);
lean_inc_n(v_toBind_1618_, 3);
v_getEnv_1619_ = lean_ctor_get(v_inst_1611_, 0);
lean_inc_n(v_getEnv_1619_, 2);
v_modifyEnv_1620_ = lean_ctor_get(v_inst_1611_, 1);
lean_inc(v_modifyEnv_1620_);
v_toPure_1621_ = lean_ctor_get(v_toApplicative_1617_, 1);
lean_inc(v_toPure_1621_);
lean_inc_ref(v_modifiers_1615_);
v___f_1622_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__3), 11, 9);
lean_closure_set(v___f_1622_, 0, v_toPure_1621_);
lean_closure_set(v___f_1622_, 1, v_modifiers_1615_);
lean_closure_set(v___f_1622_, 2, v_modifyEnv_1620_);
lean_closure_set(v___f_1622_, 3, v_toBind_1618_);
lean_closure_set(v___f_1622_, 4, v_inst_1610_);
lean_closure_set(v___f_1622_, 5, v_inst_1611_);
lean_closure_set(v___f_1622_, 6, v_inst_1612_);
lean_closure_set(v___f_1622_, 7, v_inst_1613_);
lean_closure_set(v___f_1622_, 8, v_inst_1614_);
lean_inc_ref(v___f_1622_);
lean_inc(v_declName_1616_);
v___f_1623_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_1623_, 0, v_declName_1616_);
lean_closure_set(v___f_1623_, 1, v___f_1622_);
v___f_1624_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1624_, 0, v_modifiers_1615_);
lean_closure_set(v___f_1624_, 1, v_toBind_1618_);
lean_closure_set(v___f_1624_, 2, v_getEnv_1619_);
lean_closure_set(v___f_1624_, 3, v___f_1623_);
lean_closure_set(v___f_1624_, 4, v___f_1622_);
lean_closure_set(v___f_1624_, 5, v_declName_1616_);
v___x_1625_ = lean_apply_4(v_toBind_1618_, lean_box(0), lean_box(0), v_getEnv_1619_, v___f_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility(lean_object* v_m_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v_inst_1631_, lean_object* v_modifiers_1632_, lean_object* v_declName_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1627_, v_inst_1628_, v_inst_1629_, v_inst_1630_, v_inst_1631_, v_modifiers_1632_, v_declName_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0(lean_object* v_toPure_1635_, lean_object* v_____s_1636_){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = lean_box(0);
v___x_1638_ = lean_apply_2(v_toPure_1635_, lean_box(0), v___x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1(lean_object* v___x_1639_, lean_object* v_toPure_1640_, lean_object* v_r_1641_){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1639_);
v___x_1643_ = lean_apply_2(v_toPure_1640_, lean_box(0), v___x_1642_);
return v___x_1643_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0));
v___x_1646_ = l_Lean_stringToMessageData(v___x_1645_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4));
v___x_1652_ = l_Lean_stringToMessageData(v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2(lean_object* v_pre_1653_, lean_object* v_declName_1654_, lean_object* v___x_1655_, lean_object* v_toPure_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_toBind_1659_, lean_object* v___f_1660_, lean_object* v_a_1661_, lean_object* v_x_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v___x_1664_; uint8_t v___x_1665_; 
lean_inc(v_a_1661_);
lean_inc(v_pre_1653_);
v___x_1664_ = l_Lean_Name_append(v_pre_1653_, v_a_1661_);
v___x_1665_ = lean_name_eq(v___x_1664_, v_declName_1654_);
lean_dec(v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec(v_a_1661_);
lean_dec(v___f_1660_);
lean_dec(v_toBind_1659_);
lean_dec_ref(v_inst_1658_);
lean_dec_ref(v_inst_1657_);
lean_dec(v_declName_1654_);
lean_dec(v_pre_1653_);
v___x_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1655_);
v___x_1667_ = lean_apply_2(v_toPure_1656_, lean_box(0), v___x_1666_);
return v___x_1667_;
}
else
{
lean_object* v___x_1668_; uint8_t v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_dec(v_toPure_1656_);
v___x_1668_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1669_ = 0;
v___x_1670_ = l_Lean_MessageData_ofConstName(v_declName_1654_, v___x_1669_);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1668_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_1673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = l_Lean_MessageData_ofName(v_pre_1653_);
v___x_1675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = l_Lean_MessageData_ofName(v_a_1661_);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = l_Lean_throwError___redArg(v_inst_1657_, v_inst_1658_, v___x_1681_);
v___x_1683_ = lean_apply_4(v_toBind_1659_, lean_box(0), lean_box(0), v___x_1682_, v___f_1660_);
return v___x_1683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(lean_object* v_pre_1684_, uint8_t v___x_1685_, lean_object* v_toPure_1686_, lean_object* v_declName_1687_, lean_object* v_inst_1688_, lean_object* v_inst_1689_, lean_object* v_toBind_1690_, lean_object* v___f_1691_, lean_object* v_____do__lift_1692_){
_start:
{
lean_object* v_fieldNames_1693_; lean_object* v___x_1694_; lean_object* v___f_1695_; lean_object* v___f_1696_; size_t v_sz_1697_; size_t v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_inc(v_pre_1684_);
v_fieldNames_1693_ = l_Lean_getStructureFieldsFlattened(v_____do__lift_1692_, v_pre_1684_, v___x_1685_);
v___x_1694_ = lean_box(0);
lean_inc(v_toPure_1686_);
v___f_1695_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1695_, 0, v___x_1694_);
lean_closure_set(v___f_1695_, 1, v_toPure_1686_);
lean_inc(v_toBind_1690_);
lean_inc_ref(v_inst_1688_);
v___f_1696_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2), 11, 8);
lean_closure_set(v___f_1696_, 0, v_pre_1684_);
lean_closure_set(v___f_1696_, 1, v_declName_1687_);
lean_closure_set(v___f_1696_, 2, v___x_1694_);
lean_closure_set(v___f_1696_, 3, v_toPure_1686_);
lean_closure_set(v___f_1696_, 4, v_inst_1688_);
lean_closure_set(v___f_1696_, 5, v_inst_1689_);
lean_closure_set(v___f_1696_, 6, v_toBind_1690_);
lean_closure_set(v___f_1696_, 7, v___f_1695_);
v_sz_1697_ = lean_array_size(v_fieldNames_1693_);
v___x_1698_ = ((size_t)0ULL);
v___x_1699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1688_, v_fieldNames_1693_, v___f_1696_, v_sz_1697_, v___x_1698_, v___x_1694_);
v___x_1700_ = lean_apply_4(v_toBind_1690_, lean_box(0), lean_box(0), v___x_1699_, v___f_1691_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed(lean_object* v_pre_1701_, lean_object* v___x_1702_, lean_object* v_toPure_1703_, lean_object* v_declName_1704_, lean_object* v_inst_1705_, lean_object* v_inst_1706_, lean_object* v_toBind_1707_, lean_object* v___f_1708_, lean_object* v_____do__lift_1709_){
_start:
{
uint8_t v___x_469__boxed_1710_; lean_object* v_res_1711_; 
v___x_469__boxed_1710_ = lean_unbox(v___x_1702_);
v_res_1711_ = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(v_pre_1701_, v___x_469__boxed_1710_, v_toPure_1703_, v_declName_1704_, v_inst_1705_, v_inst_1706_, v_toBind_1707_, v___f_1708_, v_____do__lift_1709_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4(lean_object* v_pre_1712_, lean_object* v_toPure_1713_, lean_object* v_declName_1714_, lean_object* v_inst_1715_, lean_object* v_inst_1716_, lean_object* v_toBind_1717_, lean_object* v___f_1718_, lean_object* v_getEnv_1719_, lean_object* v_____do__lift_1720_){
_start:
{
uint8_t v___x_1721_; 
lean_inc(v_pre_1712_);
v___x_1721_ = l_Lean_isStructure(v_____do__lift_1720_, v_pre_1712_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_dec(v_getEnv_1719_);
lean_dec(v___f_1718_);
lean_dec(v_toBind_1717_);
lean_dec_ref(v_inst_1716_);
lean_dec_ref(v_inst_1715_);
lean_dec(v_declName_1714_);
lean_dec(v_pre_1712_);
v___x_1722_ = lean_box(0);
v___x_1723_ = lean_apply_2(v_toPure_1713_, lean_box(0), v___x_1722_);
return v___x_1723_;
}
else
{
lean_object* v___x_1724_; lean_object* v___f_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_box(v___x_1721_);
lean_inc(v_toBind_1717_);
v___f_1725_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1725_, 0, v_pre_1712_);
lean_closure_set(v___f_1725_, 1, v___x_1724_);
lean_closure_set(v___f_1725_, 2, v_toPure_1713_);
lean_closure_set(v___f_1725_, 3, v_declName_1714_);
lean_closure_set(v___f_1725_, 4, v_inst_1715_);
lean_closure_set(v___f_1725_, 5, v_inst_1716_);
lean_closure_set(v___f_1725_, 6, v_toBind_1717_);
lean_closure_set(v___f_1725_, 7, v___f_1718_);
v___x_1726_ = lean_apply_4(v_toBind_1717_, lean_box(0), lean_box(0), v_getEnv_1719_, v___f_1725_);
return v___x_1726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg(lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_inst_1729_, lean_object* v_declName_1730_){
_start:
{
if (lean_obj_tag(v_declName_1730_) == 1)
{
lean_object* v_toApplicative_1731_; lean_object* v_toBind_1732_; lean_object* v_toPure_1733_; lean_object* v_pre_1734_; lean_object* v_getEnv_1735_; lean_object* v___f_1736_; lean_object* v___f_1737_; lean_object* v___x_1738_; 
v_toApplicative_1731_ = lean_ctor_get(v_inst_1727_, 0);
v_toBind_1732_ = lean_ctor_get(v_inst_1727_, 1);
lean_inc_n(v_toBind_1732_, 2);
v_toPure_1733_ = lean_ctor_get(v_toApplicative_1731_, 1);
lean_inc_n(v_toPure_1733_, 2);
v_pre_1734_ = lean_ctor_get(v_declName_1730_, 0);
lean_inc(v_pre_1734_);
v_getEnv_1735_ = lean_ctor_get(v_inst_1728_, 0);
lean_inc_n(v_getEnv_1735_, 2);
lean_dec_ref(v_inst_1728_);
v___f_1736_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1736_, 0, v_toPure_1733_);
v___f_1737_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1737_, 0, v_pre_1734_);
lean_closure_set(v___f_1737_, 1, v_toPure_1733_);
lean_closure_set(v___f_1737_, 2, v_declName_1730_);
lean_closure_set(v___f_1737_, 3, v_inst_1727_);
lean_closure_set(v___f_1737_, 4, v_inst_1729_);
lean_closure_set(v___f_1737_, 5, v_toBind_1732_);
lean_closure_set(v___f_1737_, 6, v___f_1736_);
lean_closure_set(v___f_1737_, 7, v_getEnv_1735_);
v___x_1738_ = lean_apply_4(v_toBind_1732_, lean_box(0), lean_box(0), v_getEnv_1735_, v___f_1737_);
return v___x_1738_;
}
else
{
lean_object* v_toApplicative_1739_; lean_object* v_toPure_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v_toApplicative_1739_ = lean_ctor_get(v_inst_1727_, 0);
lean_inc_ref(v_toApplicative_1739_);
lean_dec(v_declName_1730_);
lean_dec_ref(v_inst_1729_);
lean_dec_ref(v_inst_1728_);
lean_dec_ref(v_inst_1727_);
v_toPure_1740_ = lean_ctor_get(v_toApplicative_1739_, 1);
lean_inc(v_toPure_1740_);
lean_dec_ref(v_toApplicative_1739_);
v___x_1741_ = lean_box(0);
v___x_1742_ = lean_apply_2(v_toPure_1740_, lean_box(0), v___x_1741_);
return v___x_1742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField(lean_object* v_m_1743_, lean_object* v_inst_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_declName_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1744_, v_inst_1745_, v_inst_1746_, v_declName_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__0(lean_object* v_declName_1749_, lean_object* v_shortName_1750_, lean_object* v_toPure_1751_, lean_object* v_____r_1752_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v_declName_1749_);
lean_ctor_set(v___x_1753_, 1, v_shortName_1750_);
v___x_1754_ = lean_apply_2(v_toPure_1751_, lean_box(0), v___x_1753_);
return v___x_1754_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0));
v___x_1757_ = l_Lean_stringToMessageData(v___x_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2(lean_object* v_modifiers_1758_, lean_object* v_shortName_1759_, lean_object* v_toPure_1760_, lean_object* v_currNamespace_1761_, lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_toBind_1764_, lean_object* v_declName_1765_){
_start:
{
uint8_t v_isProtected_1766_; 
v_isProtected_1766_ = lean_ctor_get_uint8(v_modifiers_1758_, sizeof(void*)*3 + 1);
if (v_isProtected_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec(v_toBind_1764_);
lean_dec_ref(v_inst_1763_);
lean_dec_ref(v_inst_1762_);
lean_dec(v_currNamespace_1761_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_declName_1765_);
lean_ctor_set(v___x_1767_, 1, v_shortName_1759_);
v___x_1768_ = lean_apply_2(v_toPure_1760_, lean_box(0), v___x_1767_);
return v___x_1768_;
}
else
{
if (lean_obj_tag(v_currNamespace_1761_) == 1)
{
lean_object* v_str_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
lean_dec(v_toBind_1764_);
lean_dec_ref(v_inst_1763_);
lean_dec_ref(v_inst_1762_);
v_str_1769_ = lean_ctor_get(v_currNamespace_1761_, 1);
lean_inc_ref(v_str_1769_);
lean_dec_ref_known(v_currNamespace_1761_, 2);
v___x_1770_ = lean_box(0);
v___x_1771_ = l_Lean_Name_str___override(v___x_1770_, v_str_1769_);
v___x_1772_ = l_Lean_Name_append(v___x_1771_, v_shortName_1759_);
v___x_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1773_, 0, v_declName_1765_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = lean_apply_2(v_toPure_1760_, lean_box(0), v___x_1773_);
return v___x_1774_;
}
else
{
lean_object* v___f_1775_; uint8_t v___x_1776_; 
lean_dec(v_currNamespace_1761_);
lean_inc(v_toPure_1760_);
lean_inc(v_shortName_1759_);
lean_inc(v_declName_1765_);
v___f_1775_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1775_, 0, v_declName_1765_);
lean_closure_set(v___f_1775_, 1, v_shortName_1759_);
lean_closure_set(v___f_1775_, 2, v_toPure_1760_);
v___x_1776_ = l_Lean_Name_isAtomic(v_shortName_1759_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_dec_ref(v___f_1775_);
lean_dec(v_toBind_1764_);
lean_dec_ref(v_inst_1763_);
lean_dec_ref(v_inst_1762_);
v___x_1777_ = lean_box(0);
v___x_1778_ = l_Lean_Elab_mkDeclName___redArg___lam__0(v_declName_1765_, v_shortName_1759_, v_toPure_1760_, v___x_1777_);
return v___x_1778_;
}
else
{
lean_object* v___f_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec(v_declName_1765_);
lean_dec(v_toPure_1760_);
lean_dec(v_shortName_1759_);
v___f_1779_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1779_, 0, v___f_1775_);
v___x_1780_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_1781_ = l_Lean_throwError___redArg(v_inst_1762_, v_inst_1763_, v___x_1780_);
v___x_1782_ = lean_apply_4(v_toBind_1764_, lean_box(0), lean_box(0), v___x_1781_, v___f_1779_);
return v___x_1782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2___boxed(lean_object* v_modifiers_1783_, lean_object* v_shortName_1784_, lean_object* v_toPure_1785_, lean_object* v_currNamespace_1786_, lean_object* v_inst_1787_, lean_object* v_inst_1788_, lean_object* v_toBind_1789_, lean_object* v_declName_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_Elab_mkDeclName___redArg___lam__2(v_modifiers_1783_, v_shortName_1784_, v_toPure_1785_, v_currNamespace_1786_, v_inst_1787_, v_inst_1788_, v_toBind_1789_, v_declName_1790_);
lean_dec_ref(v_modifiers_1783_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__1(lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_modifiers_1797_, lean_object* v___y_1798_, lean_object* v_toBind_1799_, lean_object* v___f_1800_, lean_object* v_____r_1801_){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1792_, v_inst_1793_, v_inst_1794_, v_inst_1795_, v_inst_1796_, v_modifiers_1797_, v___y_1798_);
v___x_1803_ = lean_apply_4(v_toBind_1799_, lean_box(0), lean_box(0), v___x_1802_, v___f_1800_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3(lean_object* v_modifiers_1804_, lean_object* v_toPure_1805_, lean_object* v_inst_1806_, lean_object* v_inst_1807_, lean_object* v_toBind_1808_, lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v___y_1812_, lean_object* v_____r_1813_, lean_object* v_shortName_1814_, lean_object* v_currNamespace_1815_){
_start:
{
lean_object* v___f_1816_; lean_object* v___f_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_inc_n(v_toBind_1808_, 2);
lean_inc_ref_n(v_inst_1807_, 2);
lean_inc_ref_n(v_inst_1806_, 2);
lean_inc_ref(v_modifiers_1804_);
v___f_1816_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1816_, 0, v_modifiers_1804_);
lean_closure_set(v___f_1816_, 1, v_shortName_1814_);
lean_closure_set(v___f_1816_, 2, v_toPure_1805_);
lean_closure_set(v___f_1816_, 3, v_currNamespace_1815_);
lean_closure_set(v___f_1816_, 4, v_inst_1806_);
lean_closure_set(v___f_1816_, 5, v_inst_1807_);
lean_closure_set(v___f_1816_, 6, v_toBind_1808_);
lean_inc(v___y_1812_);
lean_inc_ref(v_inst_1809_);
v___f_1817_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1817_, 0, v_inst_1806_);
lean_closure_set(v___f_1817_, 1, v_inst_1809_);
lean_closure_set(v___f_1817_, 2, v_inst_1807_);
lean_closure_set(v___f_1817_, 3, v_inst_1810_);
lean_closure_set(v___f_1817_, 4, v_inst_1811_);
lean_closure_set(v___f_1817_, 5, v_modifiers_1804_);
lean_closure_set(v___f_1817_, 6, v___y_1812_);
lean_closure_set(v___f_1817_, 7, v_toBind_1808_);
lean_closure_set(v___f_1817_, 8, v___f_1816_);
v___x_1818_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1806_, v_inst_1809_, v_inst_1807_, v___y_1812_);
v___x_1819_ = lean_apply_4(v_toBind_1808_, lean_box(0), lean_box(0), v___x_1818_, v___f_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__4(lean_object* v___f_1820_, lean_object* v_shortName_1821_, lean_object* v_currNamespace_1822_, lean_object* v_____r_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_apply_3(v___f_1820_, v_____r_1823_, v_shortName_1821_, v_currNamespace_1822_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5(lean_object* v_modifiers_1825_, lean_object* v_toPure_1826_, lean_object* v_inst_1827_, lean_object* v_inst_1828_, lean_object* v_toBind_1829_, lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, uint8_t v_isRootName_1833_, lean_object* v_shortName_1834_, lean_object* v_currNamespace_1835_, lean_object* v_name_1836_, lean_object* v___x_1837_, lean_object* v_imported_1838_, lean_object* v_ctx_1839_, lean_object* v_scopes_1840_, lean_object* v_____r_1841_){
_start:
{
lean_object* v___y_1843_; 
if (v_isRootName_1833_ == 0)
{
lean_object* v___x_1862_; 
lean_dec(v_scopes_1840_);
lean_dec(v_ctx_1839_);
lean_dec(v_imported_1838_);
lean_inc(v_shortName_1834_);
lean_inc(v_currNamespace_1835_);
v___x_1862_ = l_Lean_Name_append(v_currNamespace_1835_, v_shortName_1834_);
v___y_1843_ = v___x_1862_;
goto v___jp_1842_;
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1863_ = lean_box(0);
lean_inc(v_name_1836_);
v___x_1864_ = l_Lean_Name_replacePrefix(v_name_1836_, v___x_1837_, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
lean_ctor_set(v___x_1865_, 1, v_imported_1838_);
lean_ctor_set(v___x_1865_, 2, v_ctx_1839_);
lean_ctor_set(v___x_1865_, 3, v_scopes_1840_);
v___x_1866_ = l_Lean_MacroScopesView_review(v___x_1865_);
v___y_1843_ = v___x_1866_;
goto v___jp_1842_;
}
v___jp_1842_:
{
lean_object* v___f_1844_; 
lean_inc(v___y_1843_);
lean_inc_ref(v_inst_1832_);
lean_inc(v_inst_1831_);
lean_inc_ref(v_inst_1830_);
lean_inc(v_toBind_1829_);
lean_inc_ref(v_inst_1828_);
lean_inc_ref(v_inst_1827_);
lean_inc(v_toPure_1826_);
lean_inc_ref(v_modifiers_1825_);
v___f_1844_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__3), 12, 9);
lean_closure_set(v___f_1844_, 0, v_modifiers_1825_);
lean_closure_set(v___f_1844_, 1, v_toPure_1826_);
lean_closure_set(v___f_1844_, 2, v_inst_1827_);
lean_closure_set(v___f_1844_, 3, v_inst_1828_);
lean_closure_set(v___f_1844_, 4, v_toBind_1829_);
lean_closure_set(v___f_1844_, 5, v_inst_1830_);
lean_closure_set(v___f_1844_, 6, v_inst_1831_);
lean_closure_set(v___f_1844_, 7, v_inst_1832_);
lean_closure_set(v___f_1844_, 8, v___y_1843_);
if (v_isRootName_1833_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec_ref(v___f_1844_);
lean_dec(v_name_1836_);
v___x_1845_ = lean_box(0);
v___x_1846_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1825_, v_toPure_1826_, v_inst_1827_, v_inst_1828_, v_toBind_1829_, v_inst_1830_, v_inst_1831_, v_inst_1832_, v___y_1843_, v___x_1845_, v_shortName_1834_, v_currNamespace_1835_);
return v___x_1846_;
}
else
{
if (lean_obj_tag(v_name_1836_) == 1)
{
lean_object* v_pre_1847_; lean_object* v_str_1848_; lean_object* v___x_1849_; lean_object* v_shortName_1850_; lean_object* v_currNamespace_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec_ref(v___f_1844_);
lean_dec(v_currNamespace_1835_);
lean_dec(v_shortName_1834_);
v_pre_1847_ = lean_ctor_get(v_name_1836_, 0);
lean_inc(v_pre_1847_);
v_str_1848_ = lean_ctor_get(v_name_1836_, 1);
lean_inc_ref(v_str_1848_);
lean_dec_ref_known(v_name_1836_, 2);
v___x_1849_ = lean_box(0);
v_shortName_1850_ = l_Lean_Name_str___override(v___x_1849_, v_str_1848_);
v_currNamespace_1851_ = l_Lean_Name_replacePrefix(v_pre_1847_, v___x_1837_, v___x_1849_);
v___x_1852_ = lean_box(0);
v___x_1853_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1825_, v_toPure_1826_, v_inst_1827_, v_inst_1828_, v_toBind_1829_, v_inst_1830_, v_inst_1831_, v_inst_1832_, v___y_1843_, v___x_1852_, v_shortName_1850_, v_currNamespace_1851_);
return v___x_1853_;
}
else
{
lean_object* v___f_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_dec(v___y_1843_);
lean_dec_ref(v_inst_1832_);
lean_dec(v_inst_1831_);
lean_dec_ref(v_inst_1830_);
lean_dec(v_toPure_1826_);
lean_dec_ref(v_modifiers_1825_);
v___f_1854_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__4), 4, 3);
lean_closure_set(v___f_1854_, 0, v___f_1844_);
lean_closure_set(v___f_1854_, 1, v_shortName_1834_);
lean_closure_set(v___f_1854_, 2, v_currNamespace_1835_);
v___x_1855_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1856_ = l_Lean_MessageData_ofName(v_name_1836_);
v___x_1857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = l_Lean_throwError___redArg(v_inst_1827_, v_inst_1828_, v___x_1859_);
v___x_1861_ = lean_apply_4(v_toBind_1829_, lean_box(0), lean_box(0), v___x_1860_, v___f_1854_);
return v___x_1861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_modifiers_1867_ = _args[0];
lean_object* v_toPure_1868_ = _args[1];
lean_object* v_inst_1869_ = _args[2];
lean_object* v_inst_1870_ = _args[3];
lean_object* v_toBind_1871_ = _args[4];
lean_object* v_inst_1872_ = _args[5];
lean_object* v_inst_1873_ = _args[6];
lean_object* v_inst_1874_ = _args[7];
lean_object* v_isRootName_1875_ = _args[8];
lean_object* v_shortName_1876_ = _args[9];
lean_object* v_currNamespace_1877_ = _args[10];
lean_object* v_name_1878_ = _args[11];
lean_object* v___x_1879_ = _args[12];
lean_object* v_imported_1880_ = _args[13];
lean_object* v_ctx_1881_ = _args[14];
lean_object* v_scopes_1882_ = _args[15];
lean_object* v_____r_1883_ = _args[16];
_start:
{
uint8_t v_isRootName_boxed_1884_; lean_object* v_res_1885_; 
v_isRootName_boxed_1884_ = lean_unbox(v_isRootName_1875_);
v_res_1885_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1867_, v_toPure_1868_, v_inst_1869_, v_inst_1870_, v_toBind_1871_, v_inst_1872_, v_inst_1873_, v_inst_1874_, v_isRootName_boxed_1884_, v_shortName_1876_, v_currNamespace_1877_, v_name_1878_, v___x_1879_, v_imported_1880_, v_ctx_1881_, v_scopes_1882_, v_____r_1883_);
lean_dec(v___x_1879_);
return v_res_1885_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___closed__3(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__2));
v___x_1891_ = l_Lean_stringToMessageData(v___x_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg(lean_object* v_inst_1892_, lean_object* v_inst_1893_, lean_object* v_inst_1894_, lean_object* v_inst_1895_, lean_object* v_inst_1896_, lean_object* v_currNamespace_1897_, lean_object* v_modifiers_1898_, lean_object* v_shortName_1899_){
_start:
{
lean_object* v_view_1900_; lean_object* v_toApplicative_1901_; lean_object* v_name_1902_; lean_object* v_imported_1903_; lean_object* v_ctx_1904_; lean_object* v_scopes_1905_; lean_object* v_toBind_1906_; lean_object* v_toPure_1907_; lean_object* v___x_1908_; uint8_t v_isRootName_1909_; lean_object* v___x_1910_; lean_object* v___f_1911_; uint8_t v___x_1912_; 
lean_inc_n(v_shortName_1899_, 2);
v_view_1900_ = l_Lean_extractMacroScopes(v_shortName_1899_);
v_toApplicative_1901_ = lean_ctor_get(v_inst_1892_, 0);
v_name_1902_ = lean_ctor_get(v_view_1900_, 0);
lean_inc_n(v_name_1902_, 2);
v_imported_1903_ = lean_ctor_get(v_view_1900_, 1);
lean_inc_n(v_imported_1903_, 2);
v_ctx_1904_ = lean_ctor_get(v_view_1900_, 2);
lean_inc_n(v_ctx_1904_, 2);
v_scopes_1905_ = lean_ctor_get(v_view_1900_, 3);
lean_inc_n(v_scopes_1905_, 2);
lean_dec_ref(v_view_1900_);
v_toBind_1906_ = lean_ctor_get(v_inst_1892_, 1);
lean_inc_n(v_toBind_1906_, 2);
v_toPure_1907_ = lean_ctor_get(v_toApplicative_1901_, 1);
v___x_1908_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_1909_ = l_Lean_Name_isPrefixOf(v___x_1908_, v_name_1902_);
v___x_1910_ = lean_box(v_isRootName_1909_);
lean_inc(v_currNamespace_1897_);
lean_inc_ref(v_inst_1896_);
lean_inc(v_inst_1895_);
lean_inc_ref(v_inst_1893_);
lean_inc_ref(v_inst_1894_);
lean_inc_ref(v_inst_1892_);
lean_inc(v_toPure_1907_);
lean_inc_ref(v_modifiers_1898_);
v___f_1911_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1911_, 0, v_modifiers_1898_);
lean_closure_set(v___f_1911_, 1, v_toPure_1907_);
lean_closure_set(v___f_1911_, 2, v_inst_1892_);
lean_closure_set(v___f_1911_, 3, v_inst_1894_);
lean_closure_set(v___f_1911_, 4, v_toBind_1906_);
lean_closure_set(v___f_1911_, 5, v_inst_1893_);
lean_closure_set(v___f_1911_, 6, v_inst_1895_);
lean_closure_set(v___f_1911_, 7, v_inst_1896_);
lean_closure_set(v___f_1911_, 8, v___x_1910_);
lean_closure_set(v___f_1911_, 9, v_shortName_1899_);
lean_closure_set(v___f_1911_, 10, v_currNamespace_1897_);
lean_closure_set(v___f_1911_, 11, v_name_1902_);
lean_closure_set(v___f_1911_, 12, v___x_1908_);
lean_closure_set(v___f_1911_, 13, v_imported_1903_);
lean_closure_set(v___f_1911_, 14, v_ctx_1904_);
lean_closure_set(v___f_1911_, 15, v_scopes_1905_);
v___x_1912_ = lean_name_eq(v_name_1902_, v___x_1908_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_inc(v_toPure_1907_);
lean_dec_ref(v___f_1911_);
v___x_1913_ = lean_box(0);
v___x_1914_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1898_, v_toPure_1907_, v_inst_1892_, v_inst_1894_, v_toBind_1906_, v_inst_1893_, v_inst_1895_, v_inst_1896_, v_isRootName_1909_, v_shortName_1899_, v_currNamespace_1897_, v_name_1902_, v___x_1908_, v_imported_1903_, v_ctx_1904_, v_scopes_1905_, v___x_1913_);
return v___x_1914_;
}
else
{
lean_object* v___f_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_dec(v_scopes_1905_);
lean_dec(v_ctx_1904_);
lean_dec(v_imported_1903_);
lean_dec(v_name_1902_);
lean_dec(v_shortName_1899_);
lean_dec_ref(v_modifiers_1898_);
lean_dec(v_currNamespace_1897_);
lean_dec_ref(v_inst_1896_);
lean_dec(v_inst_1895_);
lean_dec_ref(v_inst_1893_);
v___f_1915_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1915_, 0, v___f_1911_);
v___x_1916_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_1917_ = l_Lean_throwError___redArg(v_inst_1892_, v_inst_1894_, v___x_1916_);
v___x_1918_ = lean_apply_4(v_toBind_1906_, lean_box(0), lean_box(0), v___x_1917_, v___f_1915_);
return v___x_1918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName(lean_object* v_m_1919_, lean_object* v_inst_1920_, lean_object* v_inst_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_currNamespace_1925_, lean_object* v_modifiers_1926_, lean_object* v_shortName_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Lean_Elab_mkDeclName___redArg(v_inst_1920_, v_inst_1921_, v_inst_1922_, v_inst_1923_, v_inst_1924_, v_currNamespace_1925_, v_modifiers_1926_, v_shortName_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore(lean_object* v_declId_1938_){
_start:
{
uint8_t v___x_1939_; 
v___x_1939_ = l_Lean_Syntax_isIdent(v_declId_1938_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v_id_1942_; lean_object* v___x_1943_; lean_object* v_optUnivDeclStx_1944_; lean_object* v___x_1945_; 
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1941_ = l_Lean_Syntax_getArg(v_declId_1938_, v___x_1940_);
v_id_1942_ = l_Lean_Syntax_getId(v___x_1941_);
lean_dec(v___x_1941_);
v___x_1943_ = lean_unsigned_to_nat(1u);
v_optUnivDeclStx_1944_ = l_Lean_Syntax_getArg(v_declId_1938_, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v_id_1942_);
lean_ctor_set(v___x_1945_, 1, v_optUnivDeclStx_1944_);
return v___x_1945_;
}
else
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = l_Lean_Syntax_getId(v_declId_1938_);
v___x_1947_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__3));
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1946_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
return v___x_1948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore___boxed(lean_object* v_declId_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_Elab_expandDeclIdCore(v_declId_1949_);
lean_dec(v_declId_1949_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(lean_object* v_msgData_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1957_; lean_object* v_env_1958_; uint8_t v___x_1959_; lean_object* v_env_1960_; lean_object* v___x_1961_; lean_object* v_toCold_1962_; lean_object* v_mctx_1963_; lean_object* v_lctx_1964_; lean_object* v_options_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1957_ = lean_st_ref_get(v___y_1955_);
v_env_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc_ref(v_env_1958_);
lean_dec(v___x_1957_);
v___x_1959_ = 0;
v_env_1960_ = l_Lean_Environment_setRecordingDeps(v_env_1958_, v___x_1959_);
v___x_1961_ = lean_st_ref_get(v___y_1953_);
v_toCold_1962_ = lean_ctor_get(v___y_1954_, 0);
v_mctx_1963_ = lean_ctor_get(v___x_1961_, 0);
lean_inc_ref(v_mctx_1963_);
lean_dec(v___x_1961_);
v_lctx_1964_ = lean_ctor_get(v___y_1952_, 2);
v_options_1965_ = lean_ctor_get(v_toCold_1962_, 2);
lean_inc_ref(v_options_1965_);
lean_inc_ref(v_lctx_1964_);
v___x_1966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1966_, 0, v_env_1960_);
lean_ctor_set(v___x_1966_, 1, v_mctx_1963_);
lean_ctor_set(v___x_1966_, 2, v_lctx_1964_);
lean_ctor_set(v___x_1966_, 3, v_options_1965_);
v___x_1967_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
lean_ctor_set(v___x_1967_, 1, v_msgData_1951_);
v___x_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msgData_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
return v_res_1975_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(lean_object* v_opts_1976_, lean_object* v_opt_1977_){
_start:
{
lean_object* v_name_1978_; lean_object* v_defValue_1979_; lean_object* v_map_1980_; lean_object* v___x_1981_; 
v_name_1978_ = lean_ctor_get(v_opt_1977_, 0);
v_defValue_1979_ = lean_ctor_get(v_opt_1977_, 1);
v_map_1980_ = lean_ctor_get(v_opts_1976_, 0);
v___x_1981_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1980_, v_name_1978_);
if (lean_obj_tag(v___x_1981_) == 0)
{
uint8_t v___x_1982_; 
v___x_1982_ = lean_unbox(v_defValue_1979_);
return v___x_1982_;
}
else
{
lean_object* v_val_1983_; 
v_val_1983_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_val_1983_);
lean_dec_ref_known(v___x_1981_, 1);
if (lean_obj_tag(v_val_1983_) == 1)
{
uint8_t v_v_1984_; 
v_v_1984_ = lean_ctor_get_uint8(v_val_1983_, 0);
lean_dec_ref_known(v_val_1983_, 0);
return v_v_1984_;
}
else
{
uint8_t v___x_1985_; 
lean_dec(v_val_1983_);
v___x_1985_ = lean_unbox(v_defValue_1979_);
return v___x_1985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_opts_1986_, lean_object* v_opt_1987_){
_start:
{
uint8_t v_res_1988_; lean_object* v_r_1989_; 
v_res_1988_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_opts_1986_, v_opt_1987_);
lean_dec_ref(v_opt_1987_);
lean_dec_ref(v_opts_1986_);
v_r_1989_ = lean_box(v_res_1988_);
return v_r_1989_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = lean_box(1);
v___x_1991_ = l_Lean_MessageData_ofFormat(v___x_1990_);
return v___x_1991_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2));
v___x_1996_ = l_Lean_MessageData_ofFormat(v___x_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(lean_object* v_x_1997_, lean_object* v_x_1998_){
_start:
{
if (lean_obj_tag(v_x_1998_) == 0)
{
return v_x_1997_;
}
else
{
lean_object* v_head_1999_; lean_object* v_tail_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2022_; 
v_head_1999_ = lean_ctor_get(v_x_1998_, 0);
v_tail_2000_ = lean_ctor_get(v_x_1998_, 1);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_x_1998_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2002_ = v_x_1998_;
v_isShared_2003_ = v_isSharedCheck_2022_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_tail_2000_);
lean_inc(v_head_1999_);
lean_dec(v_x_1998_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2022_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v_before_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2020_; 
v_before_2004_ = lean_ctor_get(v_head_1999_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_head_1999_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v_head_1999_, 1);
lean_dec(v_unused_2021_);
v___x_2006_ = v_head_1999_;
v_isShared_2007_ = v_isSharedCheck_2020_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_before_2004_);
lean_dec(v_head_1999_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2020_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_2007_ == 0)
{
lean_ctor_set_tag(v___x_2006_, 7);
lean_ctor_set(v___x_2006_, 1, v___x_2008_);
lean_ctor_set(v___x_2006_, 0, v_x_1997_);
v___x_2010_ = v___x_2006_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_x_1997_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2011_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3);
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 7);
lean_ctor_set(v___x_2002_, 1, v___x_2011_);
lean_ctor_set(v___x_2002_, 0, v___x_2010_);
v___x_2013_ = v___x_2002_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2014_ = l_Lean_MessageData_ofSyntax(v_before_2004_);
v___x_2015_ = l_Lean_indentD(v___x_2014_);
v___x_2016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2013_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v_x_1997_ = v___x_2016_;
v_x_1998_ = v_tail_2000_;
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
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1));
v___x_2027_ = l_Lean_MessageData_ofFormat(v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_2028_, lean_object* v_macroStack_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2032_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2030_);
v___x_2033_ = l_Lean_Elab_pp_macroStack;
v___x_2034_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v___x_2032_, v___x_2033_);
lean_dec_ref(v___x_2032_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; 
lean_dec(v_macroStack_2029_);
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_msgData_2028_);
return v___x_2035_;
}
else
{
if (lean_obj_tag(v_macroStack_2029_) == 0)
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_msgData_2028_);
return v___x_2036_;
}
else
{
lean_object* v_head_2037_; lean_object* v_after_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2053_; 
v_head_2037_ = lean_ctor_get(v_macroStack_2029_, 0);
lean_inc(v_head_2037_);
v_after_2038_ = lean_ctor_get(v_head_2037_, 1);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_head_2037_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; 
v_unused_2054_ = lean_ctor_get(v_head_2037_, 0);
lean_dec(v_unused_2054_);
v___x_2040_ = v_head_2037_;
v_isShared_2041_ = v_isSharedCheck_2053_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_after_2038_);
lean_dec(v_head_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2053_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 7);
lean_ctor_set(v___x_2040_, 1, v___x_2042_);
lean_ctor_set(v___x_2040_, 0, v_msgData_2028_);
v___x_2044_ = v___x_2040_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_msgData_2028_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v_msgData_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2045_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = l_Lean_MessageData_ofSyntax(v_after_2038_);
v___x_2048_ = l_Lean_indentD(v___x_2047_);
v_msgData_2049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2049_, 0, v___x_2046_);
lean_ctor_set(v_msgData_2049_, 1, v___x_2048_);
v___x_2050_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(v_msgData_2049_, v_macroStack_2029_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_2055_, lean_object* v_macroStack_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_2055_, v_macroStack_2056_, v___y_2057_);
lean_dec_ref(v___y_2057_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(lean_object* v_msg_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_ref_2068_; lean_object* v_macroStack_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v_a_2072_; lean_object* v___x_2073_; lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2082_; 
v_ref_2068_ = lean_ctor_get(v___y_2065_, 2);
v_macroStack_2069_ = lean_ctor_get(v___y_2061_, 1);
v___x_2070_ = l_Lean_Elab_getBetterRef(v_ref_2068_, v_macroStack_2069_);
v___x_2071_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msg_2060_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2071_);
lean_inc(v_macroStack_2069_);
v___x_2073_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_a_2072_, v_macroStack_2069_, v___y_2065_);
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2070_);
lean_ctor_set(v___x_2078_, 1, v_a_2074_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set_tag(v___x_2076_, 1);
lean_ctor_set(v___x_2076_, 0, v___x_2078_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg___boxed(lean_object* v_msg_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(lean_object* v_env_2092_, lean_object* v_declName_2093_, lean_object* v___f_2094_, lean_object* v_addInfo_2095_, lean_object* v_____r_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v___x_2104_; uint8_t v___x_2105_; uint8_t v___x_2106_; 
lean_inc(v_declName_2093_);
v___x_2104_ = l_Lean_mkPrivateName(v_env_2092_, v_declName_2093_);
v___x_2105_ = 1;
lean_inc(v___x_2104_);
v___x_2106_ = l_Lean_Environment_contains(v_env_2092_, v___x_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_dec(v___x_2104_);
lean_dec_ref(v_addInfo_2095_);
lean_dec(v_declName_2093_);
v___x_2107_ = lean_box(0);
lean_inc(v___y_2102_);
lean_inc_ref(v___y_2101_);
lean_inc(v___y_2100_);
lean_inc_ref(v___y_2099_);
lean_inc(v___y_2098_);
lean_inc_ref(v___y_2097_);
v___x_2108_ = lean_apply_8(v___f_2094_, v___x_2107_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, lean_box(0));
return v___x_2108_;
}
else
{
lean_object* v___x_2109_; 
lean_dec_ref(v___f_2094_);
lean_inc(v___y_2102_);
lean_inc_ref(v___y_2101_);
lean_inc(v___y_2100_);
lean_inc_ref(v___y_2099_);
lean_inc(v___y_2098_);
lean_inc_ref(v___y_2097_);
v___x_2109_ = lean_apply_8(v_addInfo_2095_, v___x_2104_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, lean_box(0));
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec_ref_known(v___x_2109_, 1);
v___x_2110_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1);
v___x_2111_ = l_Lean_MessageData_ofConstName(v_declName_2093_, v___x_2105_);
v___x_2112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2112_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2114_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
return v___x_2115_;
}
else
{
lean_dec(v_declName_2093_);
return v___x_2109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed(lean_object* v_env_2116_, lean_object* v_declName_2117_, lean_object* v___f_2118_, lean_object* v_addInfo_2119_, lean_object* v_____r_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(v_env_2116_, v_declName_2117_, v___f_2118_, v_addInfo_2119_, v_____r_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(lean_object* v___f_2129_, lean_object* v_declName_2130_, uint8_t v___x_2131_, lean_object* v_env_2132_, lean_object* v_____do__lift_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
uint8_t v___y_2142_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
lean_inc(v_declName_2130_);
v___x_2151_ = l_Lean_privateToUserName(v_declName_2130_);
lean_inc_ref(v_env_2132_);
v___x_2152_ = lean_is_reserved_name(v_env_2132_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; uint8_t v___x_2154_; 
lean_inc(v_declName_2130_);
v___x_2153_ = l_Lean_mkPrivateName(v_____do__lift_2133_, v_declName_2130_);
v___x_2154_ = lean_is_reserved_name(v_env_2132_, v___x_2153_);
v___y_2142_ = v___x_2154_;
goto v___jp_2141_;
}
else
{
lean_dec_ref(v_env_2132_);
v___y_2142_ = v___x_2152_;
goto v___jp_2141_;
}
v___jp_2141_:
{
if (v___y_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
lean_dec(v_declName_2130_);
v___x_2143_ = lean_box(0);
lean_inc(v___y_2139_);
lean_inc_ref(v___y_2138_);
lean_inc(v___y_2137_);
lean_inc_ref(v___y_2136_);
lean_inc(v___y_2135_);
lean_inc_ref(v___y_2134_);
v___x_2144_ = lean_apply_8(v___f_2129_, v___x_2143_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, lean_box(0));
return v___x_2144_;
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_dec_ref(v___f_2129_);
v___x_2145_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2146_ = l_Lean_MessageData_ofConstName(v_declName_2130_, v___x_2131_);
v___x_2147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3);
v___x_2149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2147_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2149_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
return v___x_2150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed(lean_object* v___f_2155_, lean_object* v_declName_2156_, lean_object* v___x_2157_, lean_object* v_env_2158_, lean_object* v_____do__lift_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
uint8_t v___x_16614__boxed_2167_; lean_object* v_res_2168_; 
v___x_16614__boxed_2167_ = lean_unbox(v___x_2157_);
v_res_2168_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(v___f_2155_, v_declName_2156_, v___x_16614__boxed_2167_, v_env_2158_, v_____do__lift_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec_ref(v_____do__lift_2159_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(lean_object* v_t_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v___x_2172_; lean_object* v_infoState_2173_; uint8_t v_enabled_2174_; 
v___x_2172_ = lean_st_ref_get(v___y_2170_);
v_infoState_2173_ = lean_ctor_get(v___x_2172_, 8);
lean_inc_ref(v_infoState_2173_);
lean_dec(v___x_2172_);
v_enabled_2174_ = lean_ctor_get_uint8(v_infoState_2173_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2173_);
if (v_enabled_2174_ == 0)
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec_ref(v_t_2169_);
v___x_2175_ = lean_box(0);
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
return v___x_2176_;
}
else
{
lean_object* v___x_2177_; lean_object* v_infoState_2178_; lean_object* v_env_2179_; lean_object* v_nextMacroScope_2180_; lean_object* v_ngen_2181_; lean_object* v_auxDeclNGen_2182_; lean_object* v_traceState_2183_; lean_object* v_cache_2184_; lean_object* v_recordedDeps_2185_; lean_object* v_messages_2186_; lean_object* v_snapshotTasks_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2209_; 
v___x_2177_ = lean_st_ref_take(v___y_2170_);
v_infoState_2178_ = lean_ctor_get(v___x_2177_, 8);
v_env_2179_ = lean_ctor_get(v___x_2177_, 0);
v_nextMacroScope_2180_ = lean_ctor_get(v___x_2177_, 1);
v_ngen_2181_ = lean_ctor_get(v___x_2177_, 2);
v_auxDeclNGen_2182_ = lean_ctor_get(v___x_2177_, 3);
v_traceState_2183_ = lean_ctor_get(v___x_2177_, 4);
v_cache_2184_ = lean_ctor_get(v___x_2177_, 5);
v_recordedDeps_2185_ = lean_ctor_get(v___x_2177_, 6);
v_messages_2186_ = lean_ctor_get(v___x_2177_, 7);
v_snapshotTasks_2187_ = lean_ctor_get(v___x_2177_, 9);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2189_ = v___x_2177_;
v_isShared_2190_ = v_isSharedCheck_2209_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_snapshotTasks_2187_);
lean_inc(v_infoState_2178_);
lean_inc(v_messages_2186_);
lean_inc(v_recordedDeps_2185_);
lean_inc(v_cache_2184_);
lean_inc(v_traceState_2183_);
lean_inc(v_auxDeclNGen_2182_);
lean_inc(v_ngen_2181_);
lean_inc(v_nextMacroScope_2180_);
lean_inc(v_env_2179_);
lean_dec(v___x_2177_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2209_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
uint8_t v_enabled_2191_; lean_object* v_assignment_2192_; lean_object* v_lazyAssignment_2193_; lean_object* v_trees_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2208_; 
v_enabled_2191_ = lean_ctor_get_uint8(v_infoState_2178_, sizeof(void*)*3);
v_assignment_2192_ = lean_ctor_get(v_infoState_2178_, 0);
v_lazyAssignment_2193_ = lean_ctor_get(v_infoState_2178_, 1);
v_trees_2194_ = lean_ctor_get(v_infoState_2178_, 2);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_infoState_2178_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2196_ = v_infoState_2178_;
v_isShared_2197_ = v_isSharedCheck_2208_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_trees_2194_);
lean_inc(v_lazyAssignment_2193_);
lean_inc(v_assignment_2192_);
lean_dec(v_infoState_2178_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2208_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2198_ = lean_box(0);
v___x_2199_ = l_Lean_PersistentArray_push___redArg(v_trees_2194_, v_t_2169_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 2, v___x_2199_);
v___x_2201_ = v___x_2196_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_assignment_2192_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_lazyAssignment_2193_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v___x_2199_);
lean_ctor_set_uint8(v_reuseFailAlloc_2207_, sizeof(void*)*3, v_enabled_2191_);
v___x_2201_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2203_; 
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 8, v___x_2201_);
v___x_2203_ = v___x_2189_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_env_2179_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_nextMacroScope_2180_);
lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_ngen_2181_);
lean_ctor_set(v_reuseFailAlloc_2206_, 3, v_auxDeclNGen_2182_);
lean_ctor_set(v_reuseFailAlloc_2206_, 4, v_traceState_2183_);
lean_ctor_set(v_reuseFailAlloc_2206_, 5, v_cache_2184_);
lean_ctor_set(v_reuseFailAlloc_2206_, 6, v_recordedDeps_2185_);
lean_ctor_set(v_reuseFailAlloc_2206_, 7, v_messages_2186_);
lean_ctor_set(v_reuseFailAlloc_2206_, 8, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2206_, 9, v_snapshotTasks_2187_);
v___x_2203_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = lean_st_ref_put(v___y_2170_, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2198_);
return v___x_2205_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg___boxed(lean_object* v_t_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_2210_, v___y_2211_);
lean_dec(v___y_2211_);
return v_res_2213_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = lean_unsigned_to_nat(32u);
v___x_2215_ = lean_mk_empty_array_with_capacity(v___x_2214_);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1(void){
_start:
{
size_t v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2217_ = ((size_t)5ULL);
v___x_2218_ = lean_unsigned_to_nat(0u);
v___x_2219_ = lean_unsigned_to_nat(32u);
v___x_2220_ = lean_mk_empty_array_with_capacity(v___x_2219_);
v___x_2221_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0);
v___x_2222_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v___x_2220_);
lean_ctor_set(v___x_2222_, 2, v___x_2218_);
lean_ctor_set(v___x_2222_, 3, v___x_2218_);
lean_ctor_set_usize(v___x_2222_, 4, v___x_2217_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(lean_object* v_t_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2231_; lean_object* v_infoState_2232_; uint8_t v_enabled_2233_; 
v___x_2231_ = lean_st_ref_get(v___y_2229_);
v_infoState_2232_ = lean_ctor_get(v___x_2231_, 8);
lean_inc_ref(v_infoState_2232_);
lean_dec(v___x_2231_);
v_enabled_2233_ = lean_ctor_get_uint8(v_infoState_2232_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2232_);
if (v_enabled_2233_ == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
lean_dec_ref(v_t_2223_);
v___x_2234_ = lean_box(0);
v___x_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
return v___x_2235_;
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1);
v___x_2237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2237_, 0, v_t_2223_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v___x_2237_, v___y_2229_);
return v___x_2238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___boxed(lean_object* v_t_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v_t_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
if (lean_obj_tag(v_a_2248_) == 0)
{
lean_object* v___x_2250_; 
v___x_2250_ = l_List_reverse___redArg(v_a_2249_);
return v___x_2250_;
}
else
{
lean_object* v_head_2251_; lean_object* v_tail_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2261_; 
v_head_2251_ = lean_ctor_get(v_a_2248_, 0);
v_tail_2252_ = lean_ctor_get(v_a_2248_, 1);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_a_2248_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2254_ = v_a_2248_;
v_isShared_2255_ = v_isSharedCheck_2261_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_tail_2252_);
lean_inc(v_head_2251_);
lean_dec(v_a_2248_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2261_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2256_ = l_Lean_mkLevelParam(v_head_2251_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 1, v_a_2249_);
lean_ctor_set(v___x_2254_, 0, v___x_2256_);
v___x_2258_ = v___x_2254_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_a_2249_);
v___x_2258_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
v_a_2248_ = v_tail_2252_;
v_a_2249_ = v___x_2258_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0);
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
return v___x_2263_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2264_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2265_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0);
v___x_2266_ = lean_unsigned_to_nat(0u);
v___x_2267_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
lean_ctor_set(v___x_2267_, 2, v___x_2266_);
lean_ctor_set(v___x_2267_, 3, v___x_2266_);
lean_ctor_set(v___x_2267_, 4, v___x_2265_);
lean_ctor_set(v___x_2267_, 5, v___x_2265_);
lean_ctor_set(v___x_2267_, 6, v___x_2265_);
lean_ctor_set(v___x_2267_, 7, v___x_2265_);
lean_ctor_set(v___x_2267_, 8, v___x_2265_);
lean_ctor_set(v___x_2267_, 9, v___x_2265_);
lean_ctor_set(v___x_2267_, 10, v___x_2265_);
lean_ctor_set(v___x_2267_, 11, v___x_2264_);
return v___x_2267_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2268_ = lean_box(1);
v___x_2269_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3);
v___x_2270_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0);
v___x_2271_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
lean_ctor_set(v___x_2271_, 1, v___x_2269_);
lean_ctor_set(v___x_2271_, 2, v___x_2268_);
return v___x_2271_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3));
v___x_2274_ = l_Lean_stringToMessageData(v___x_2273_);
return v___x_2274_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5));
v___x_2277_ = l_Lean_stringToMessageData(v___x_2276_);
return v___x_2277_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7));
v___x_2280_ = l_Lean_stringToMessageData(v___x_2279_);
return v___x_2280_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9));
v___x_2283_ = l_Lean_stringToMessageData(v___x_2282_);
return v___x_2283_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11));
v___x_2286_ = l_Lean_stringToMessageData(v___x_2285_);
return v___x_2286_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13));
v___x_2289_ = l_Lean_stringToMessageData(v___x_2288_);
return v___x_2289_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15));
v___x_2292_ = l_Lean_stringToMessageData(v___x_2291_);
return v___x_2292_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__18(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17));
v___x_2295_ = l_Lean_stringToMessageData(v___x_2294_);
return v___x_2295_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__20(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__19));
v___x_2298_ = l_Lean_stringToMessageData(v___x_2297_);
return v___x_2298_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__22(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__21));
v___x_2301_ = l_Lean_stringToMessageData(v___x_2300_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__24(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__23));
v___x_2304_ = l_Lean_stringToMessageData(v___x_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(lean_object* v_msg_2305_, lean_object* v_declHint_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v_env_2311_; uint8_t v___x_2312_; 
v___x_2309_ = lean_box(0);
v___x_2310_ = lean_st_ref_get(v___y_2307_);
v_env_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc_ref(v_env_2311_);
lean_dec(v___x_2310_);
v___x_2312_ = l_Lean_Name_isAnonymous(v_declHint_2306_);
if (v___x_2312_ == 0)
{
uint8_t v_isExporting_2313_; 
v_isExporting_2313_ = lean_ctor_get_uint8(v_env_2311_, sizeof(void*)*13);
if (v_isExporting_2313_ == 0)
{
lean_object* v___x_2314_; 
lean_dec_ref(v_env_2311_);
lean_dec(v_declHint_2306_);
v___x_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2314_, 0, v_msg_2305_);
return v___x_2314_;
}
else
{
lean_object* v___x_2315_; uint8_t v___x_2316_; 
lean_inc_ref(v_env_2311_);
v___x_2315_ = l_Lean_Environment_setExporting(v_env_2311_, v___x_2312_);
lean_inc(v_declHint_2306_);
lean_inc_ref(v___x_2315_);
v___x_2316_ = l_Lean_Environment_contains(v___x_2315_, v_declHint_2306_, v_isExporting_2313_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; 
lean_dec_ref(v___x_2315_);
lean_dec_ref(v_env_2311_);
lean_dec(v_declHint_2306_);
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v_msg_2305_);
return v___x_2317_;
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v_c_2323_; lean_object* v___x_2324_; 
v___x_2318_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
v___x_2319_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2);
v___x_2320_ = l_Lean_Options_empty;
v___x_2321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2315_);
lean_ctor_set(v___x_2321_, 1, v___x_2318_);
lean_ctor_set(v___x_2321_, 2, v___x_2319_);
lean_ctor_set(v___x_2321_, 3, v___x_2320_);
lean_inc(v_declHint_2306_);
v___x_2322_ = l_Lean_MessageData_ofConstName(v_declHint_2306_, v___x_2312_);
v_c_2323_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2323_, 0, v___x_2321_);
lean_ctor_set(v_c_2323_, 1, v___x_2322_);
v___x_2324_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2311_, v_declHint_2306_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_dec_ref(v_env_2311_);
lean_dec(v_declHint_2306_);
v___x_2325_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4);
v___x_2326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
lean_ctor_set(v___x_2326_, 1, v_c_2323_);
v___x_2327_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6);
v___x_2328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2326_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = l_Lean_MessageData_note(v___x_2328_);
v___x_2330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2330_, 0, v_msg_2305_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
v___x_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
return v___x_2331_;
}
else
{
lean_object* v_val_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2388_; 
v_val_2332_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2334_ = v___x_2324_;
v_isShared_2335_ = v_isSharedCheck_2388_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_val_2332_);
lean_dec(v___x_2324_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2388_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v_modules_2337_; lean_object* v_moduleNames_2338_; lean_object* v_mod_2339_; uint8_t v___y_2341_; uint8_t v___x_2371_; 
v___x_2336_ = l_Lean_Environment_header(v_env_2311_);
lean_dec_ref(v_env_2311_);
v_modules_2337_ = lean_ctor_get(v___x_2336_, 3);
lean_inc_ref(v_modules_2337_);
v_moduleNames_2338_ = lean_ctor_get(v___x_2336_, 4);
lean_inc_ref(v_moduleNames_2338_);
lean_dec_ref(v___x_2336_);
v_mod_2339_ = lean_array_get(v___x_2309_, v_moduleNames_2338_, v_val_2332_);
lean_dec_ref(v_moduleNames_2338_);
v___x_2371_ = l_Lean_isPrivateName(v_declHint_2306_);
lean_dec(v_declHint_2306_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2372_; uint8_t v___x_2373_; 
v___x_2372_ = lean_array_get_size(v_modules_2337_);
v___x_2373_ = lean_nat_dec_lt(v_val_2332_, v___x_2372_);
if (v___x_2373_ == 0)
{
lean_dec_ref(v_modules_2337_);
lean_dec(v_val_2332_);
v___y_2341_ = v___x_2371_;
goto v___jp_2340_;
}
else
{
lean_object* v___x_2374_; lean_object* v_toImport_2375_; uint8_t v_isExported_2376_; 
v___x_2374_ = lean_array_fget(v_modules_2337_, v_val_2332_);
lean_dec(v_val_2332_);
lean_dec_ref(v_modules_2337_);
v_toImport_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc_ref(v_toImport_2375_);
lean_dec(v___x_2374_);
v_isExported_2376_ = lean_ctor_get_uint8(v_toImport_2375_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2375_);
v___y_2341_ = v_isExported_2376_;
goto v___jp_2340_;
}
}
else
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
lean_dec_ref(v_modules_2337_);
lean_del_object(v___x_2334_);
lean_dec(v_val_2332_);
v___x_2377_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4);
v___x_2378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
lean_ctor_set(v___x_2378_, 1, v_c_2323_);
v___x_2379_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__22);
v___x_2380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2378_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = l_Lean_MessageData_ofName(v_mod_2339_);
v___x_2382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2380_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__24);
v___x_2384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2382_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = l_Lean_MessageData_note(v___x_2384_);
v___x_2386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2386_, 0, v_msg_2305_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
return v___x_2387_;
}
v___jp_2340_:
{
if (v___y_2341_ == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2342_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8);
v___x_2343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v_c_2323_);
v___x_2344_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10);
v___x_2345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2343_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
v___x_2346_ = l_Lean_MessageData_ofName(v_mod_2339_);
v___x_2347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12);
v___x_2349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2347_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = l_Lean_MessageData_note(v___x_2349_);
v___x_2351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2351_, 0, v_msg_2305_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set_tag(v___x_2334_, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2351_);
v___x_2353_ = v___x_2334_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
else
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2355_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14);
v___x_2356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
lean_ctor_set(v___x_2356_, 1, v_c_2323_);
v___x_2357_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16);
v___x_2358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = l_Lean_MessageData_ofName(v_mod_2339_);
lean_inc_ref(v___x_2359_);
v___x_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2358_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__18);
v___x_2362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2360_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
v___x_2363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
lean_ctor_set(v___x_2363_, 1, v___x_2359_);
v___x_2364_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__20);
v___x_2365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = l_Lean_MessageData_note(v___x_2365_);
v___x_2367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2367_, 0, v_msg_2305_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set_tag(v___x_2334_, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2367_);
v___x_2369_ = v___x_2334_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
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
lean_object* v___x_2389_; 
lean_dec_ref(v_env_2311_);
lean_dec(v_declHint_2306_);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v_msg_2305_);
return v___x_2389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___boxed(lean_object* v_msg_2390_, lean_object* v_declHint_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2390_, v_declHint_2391_, v___y_2392_);
lean_dec(v___y_2392_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(lean_object* v_msg_2395_, lean_object* v_declHint_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2414_; 
v___x_2404_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2395_, v_declHint_2396_, v___y_2402_);
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2407_ = v___x_2404_;
v_isShared_2408_ = v_isSharedCheck_2414_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2404_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2414_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2409_ = l_Lean_unknownIdentifierMessageTag;
v___x_2410_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
lean_ctor_set(v___x_2410_, 1, v_a_2405_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 0, v___x_2410_);
v___x_2412_ = v___x_2407_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23___boxed(lean_object* v_msg_2415_, lean_object* v_declHint_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2415_, v_declHint_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(lean_object* v_ref_2425_, lean_object* v_msg_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_toCold_2434_; lean_object* v_currRecDepth_2435_; lean_object* v_ref_2436_; uint16_t v_optionFlags_2437_; uint8_t v_suppressElabErrors_2438_; uint8_t v_isRecordingDeps_2439_; lean_object* v_ref_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_toCold_2434_ = lean_ctor_get(v___y_2431_, 0);
v_currRecDepth_2435_ = lean_ctor_get(v___y_2431_, 1);
v_ref_2436_ = lean_ctor_get(v___y_2431_, 2);
v_optionFlags_2437_ = lean_ctor_get_uint16(v___y_2431_, sizeof(void*)*3);
v_suppressElabErrors_2438_ = lean_ctor_get_uint8(v___y_2431_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2439_ = lean_ctor_get_uint8(v___y_2431_, sizeof(void*)*3 + 3);
v_ref_2440_ = l_Lean_replaceRef(v_ref_2425_, v_ref_2436_);
lean_inc(v_currRecDepth_2435_);
lean_inc_ref(v_toCold_2434_);
v___x_2441_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2441_, 0, v_toCold_2434_);
lean_ctor_set(v___x_2441_, 1, v_currRecDepth_2435_);
lean_ctor_set(v___x_2441_, 2, v_ref_2440_);
lean_ctor_set_uint16(v___x_2441_, sizeof(void*)*3, v_optionFlags_2437_);
lean_ctor_set_uint8(v___x_2441_, sizeof(void*)*3 + 2, v_suppressElabErrors_2438_);
lean_ctor_set_uint8(v___x_2441_, sizeof(void*)*3 + 3, v_isRecordingDeps_2439_);
v___x_2442_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___x_2441_, v___y_2432_);
lean_dec_ref_known(v___x_2441_, 3);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg___boxed(lean_object* v_ref_2443_, lean_object* v_msg_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2443_, v_msg_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v_ref_2443_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(lean_object* v_ref_2453_, lean_object* v_msg_2454_, lean_object* v_declHint_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___x_2463_; lean_object* v_a_2464_; lean_object* v___x_2465_; 
v___x_2463_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2454_, v_declHint_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref(v___x_2463_);
v___x_2465_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2453_, v_a_2464_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg___boxed(lean_object* v_ref_2466_, lean_object* v_msg_2467_, lean_object* v_declHint_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2466_, v_msg_2467_, v_declHint_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v_ref_2466_);
return v_res_2476_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0));
v___x_2479_ = l_Lean_stringToMessageData(v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(lean_object* v_ref_2480_, lean_object* v_constName_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v___x_2489_; uint8_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2489_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1);
v___x_2490_ = 0;
lean_inc(v_constName_2481_);
v___x_2491_ = l_Lean_MessageData_ofConstName(v_constName_2481_, v___x_2490_);
v___x_2492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2489_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___x_2493_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2492_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
v___x_2495_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2480_, v___x_2494_, v_constName_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___boxed(lean_object* v_ref_2496_, lean_object* v_constName_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2496_, v_constName_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v_ref_2496_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(lean_object* v_constName_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_ref_2514_; lean_object* v___x_2515_; 
v_ref_2514_ = lean_ctor_get(v___y_2511_, 2);
v___x_2515_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2514_, v_constName_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_constName_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(lean_object* v_constName_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___x_2533_; lean_object* v_env_2534_; uint8_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2533_ = lean_st_ref_get(v___y_2531_);
v_env_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc_ref(v_env_2534_);
lean_dec(v___x_2533_);
v___x_2535_ = 0;
lean_inc(v_constName_2525_);
v___x_2536_ = l_Lean_Environment_findConstVal_x3f(v_env_2534_, v_constName_2525_, v___x_2535_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
return v___x_2537_;
}
else
{
lean_object* v_val_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_constName_2525_);
v_val_2538_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2536_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_val_2538_);
lean_dec(v___x_2536_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
lean_ctor_set_tag(v___x_2540_, 0);
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_val_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14___boxed(lean_object* v_constName_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(lean_object* v_constName_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v___x_2563_; 
lean_inc(v_constName_2555_);
v___x_2563_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2575_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2575_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2575_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v_levelParams_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2573_; 
v_levelParams_2568_ = lean_ctor_get(v_a_2564_, 1);
lean_inc(v_levelParams_2568_);
lean_dec(v_a_2564_);
v___x_2569_ = lean_box(0);
v___x_2570_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(v_levelParams_2568_, v___x_2569_);
v___x_2571_ = l_Lean_mkConst(v_constName_2555_, v___x_2570_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2571_);
v___x_2573_ = v___x_2566_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_dec(v_constName_2555_);
v_a_2576_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2563_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2563_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_constName_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_constName_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(uint8_t v___x_2593_, lean_object* v_declName_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_ref_2602_; lean_object* v___x_2603_; 
v_ref_2602_ = lean_ctor_get(v___y_2599_, 2);
v___x_2603_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_declName_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v___x_2605_ = lean_box(0);
lean_inc(v_ref_2602_);
v___x_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
lean_ctor_set(v___x_2606_, 1, v_ref_2602_);
v___x_2607_ = lean_unsigned_to_nat(32u);
v___x_2608_ = lean_mk_empty_array_with_capacity(v___x_2607_);
lean_dec_ref(v___x_2608_);
v___x_2609_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4);
v___x_2610_ = lean_box(0);
v___x_2611_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2611_, 0, v___x_2606_);
lean_ctor_set(v___x_2611_, 1, v___x_2609_);
lean_ctor_set(v___x_2611_, 2, v___x_2610_);
lean_ctor_set(v___x_2611_, 3, v_a_2604_);
lean_ctor_set_uint8(v___x_2611_, sizeof(void*)*4, v___x_2593_);
lean_ctor_set_uint8(v___x_2611_, sizeof(void*)*4 + 1, v___x_2593_);
v___x_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
v___x_2613_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v___x_2612_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
return v___x_2613_;
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
v_a_2614_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2603_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2603_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v___x_2622_, lean_object* v_declName_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
uint8_t v___x_17418__boxed_2631_; lean_object* v_res_2632_; 
v___x_17418__boxed_2631_ = lean_unbox(v___x_2622_);
v_res_2632_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(v___x_17418__boxed_2631_, v_declName_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(lean_object* v___f_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; lean_object* v_env_2642_; lean_object* v___x_2643_; 
v___x_2641_ = lean_st_ref_get(v___y_2639_);
v_env_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc_ref(v_env_2642_);
lean_dec(v___x_2641_);
v___x_2643_ = lean_apply_8(v___f_2633_, v_env_2642_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, lean_box(0));
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed(lean_object* v___f_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(v___f_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v_res_2652_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
return v___x_2654_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
return v___x_2656_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2658_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
lean_ctor_set(v___x_2658_, 2, v___x_2657_);
lean_ctor_set(v___x_2658_, 3, v___x_2657_);
lean_ctor_set(v___x_2658_, 4, v___x_2657_);
lean_ctor_set(v___x_2658_, 5, v___x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(lean_object* v_env_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; lean_object* v_nextMacroScope_2664_; lean_object* v_ngen_2665_; lean_object* v_auxDeclNGen_2666_; lean_object* v_traceState_2667_; lean_object* v_recordedDeps_2668_; lean_object* v_messages_2669_; lean_object* v_infoState_2670_; lean_object* v_snapshotTasks_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2697_; 
v___x_2663_ = lean_st_ref_take(v___y_2661_);
v_nextMacroScope_2664_ = lean_ctor_get(v___x_2663_, 1);
v_ngen_2665_ = lean_ctor_get(v___x_2663_, 2);
v_auxDeclNGen_2666_ = lean_ctor_get(v___x_2663_, 3);
v_traceState_2667_ = lean_ctor_get(v___x_2663_, 4);
v_recordedDeps_2668_ = lean_ctor_get(v___x_2663_, 6);
v_messages_2669_ = lean_ctor_get(v___x_2663_, 7);
v_infoState_2670_ = lean_ctor_get(v___x_2663_, 8);
v_snapshotTasks_2671_ = lean_ctor_get(v___x_2663_, 9);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2697_ == 0)
{
lean_object* v_unused_2698_; lean_object* v_unused_2699_; 
v_unused_2698_ = lean_ctor_get(v___x_2663_, 5);
lean_dec(v_unused_2698_);
v_unused_2699_ = lean_ctor_get(v___x_2663_, 0);
lean_dec(v_unused_2699_);
v___x_2673_ = v___x_2663_;
v_isShared_2674_ = v_isSharedCheck_2697_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_snapshotTasks_2671_);
lean_inc(v_infoState_2670_);
lean_inc(v_messages_2669_);
lean_inc(v_recordedDeps_2668_);
lean_inc(v_traceState_2667_);
lean_inc(v_auxDeclNGen_2666_);
lean_inc(v_ngen_2665_);
lean_inc(v_nextMacroScope_2664_);
lean_dec(v___x_2663_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2697_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2675_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 5, v___x_2675_);
lean_ctor_set(v___x_2673_, 0, v_env_2659_);
v___x_2677_ = v___x_2673_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_env_2659_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_nextMacroScope_2664_);
lean_ctor_set(v_reuseFailAlloc_2696_, 2, v_ngen_2665_);
lean_ctor_set(v_reuseFailAlloc_2696_, 3, v_auxDeclNGen_2666_);
lean_ctor_set(v_reuseFailAlloc_2696_, 4, v_traceState_2667_);
lean_ctor_set(v_reuseFailAlloc_2696_, 5, v___x_2675_);
lean_ctor_set(v_reuseFailAlloc_2696_, 6, v_recordedDeps_2668_);
lean_ctor_set(v_reuseFailAlloc_2696_, 7, v_messages_2669_);
lean_ctor_set(v_reuseFailAlloc_2696_, 8, v_infoState_2670_);
lean_ctor_set(v_reuseFailAlloc_2696_, 9, v_snapshotTasks_2671_);
v___x_2677_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v_mctx_2680_; lean_object* v_zetaDeltaFVarIds_2681_; lean_object* v_postponed_2682_; lean_object* v_diag_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2694_; 
v___x_2678_ = lean_st_ref_put(v___y_2661_, v___x_2677_);
v___x_2679_ = lean_st_ref_take(v___y_2660_);
v_mctx_2680_ = lean_ctor_get(v___x_2679_, 0);
v_zetaDeltaFVarIds_2681_ = lean_ctor_get(v___x_2679_, 2);
v_postponed_2682_ = lean_ctor_get(v___x_2679_, 3);
v_diag_2683_ = lean_ctor_get(v___x_2679_, 4);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; 
v_unused_2695_ = lean_ctor_get(v___x_2679_, 1);
lean_dec(v_unused_2695_);
v___x_2685_ = v___x_2679_;
v_isShared_2686_ = v_isSharedCheck_2694_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_diag_2683_);
lean_inc(v_postponed_2682_);
lean_inc(v_zetaDeltaFVarIds_2681_);
lean_inc(v_mctx_2680_);
lean_dec(v___x_2679_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2694_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2687_ = lean_box(0);
v___x_2688_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 1, v___x_2688_);
v___x_2690_ = v___x_2685_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_mctx_2680_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2693_, 2, v_zetaDeltaFVarIds_2681_);
lean_ctor_set(v_reuseFailAlloc_2693_, 3, v_postponed_2682_);
lean_ctor_set(v_reuseFailAlloc_2693_, 4, v_diag_2683_);
v___x_2690_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2691_ = lean_st_ref_put(v___y_2660_, v___x_2690_);
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2687_);
return v___x_2692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___boxed(lean_object* v_env_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2700_, v___y_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec(v___y_2701_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(lean_object* v_env_2705_, lean_object* v_x_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v___x_2714_; lean_object* v_env_2715_; lean_object* v_a_2717_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2714_ = lean_st_ref_get(v___y_2712_);
v_env_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc_ref(v_env_2715_);
lean_dec(v___x_2714_);
v___x_2727_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2705_, v___y_2710_, v___y_2712_);
lean_dec_ref(v___x_2727_);
lean_inc(v___y_2712_);
lean_inc_ref(v___y_2711_);
lean_inc(v___y_2710_);
lean_inc_ref(v___y_2709_);
lean_inc(v___y_2708_);
lean_inc_ref(v___y_2707_);
v___x_2728_ = lean_apply_7(v_x_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, lean_box(0));
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2728_, 1);
v___x_2730_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2715_, v___y_2710_, v___y_2712_);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2737_ == 0)
{
lean_object* v_unused_2738_; 
v_unused_2738_ = lean_ctor_get(v___x_2730_, 0);
lean_dec(v_unused_2738_);
v___x_2732_ = v___x_2730_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_dec(v___x_2730_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v_a_2729_);
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2729_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
else
{
lean_object* v_a_2739_; 
v_a_2739_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2739_);
lean_dec_ref_known(v___x_2728_, 1);
v_a_2717_ = v_a_2739_;
goto v___jp_2716_;
}
v___jp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
v___x_2718_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2715_, v___y_2710_, v___y_2712_);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v___x_2718_, 0);
lean_dec(v_unused_2726_);
v___x_2720_ = v___x_2718_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_dec(v___x_2718_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
lean_ctor_set_tag(v___x_2720_, 1);
lean_ctor_set(v___x_2720_, 0, v_a_2717_);
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2717_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_env_2740_, lean_object* v_x_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2740_, v_x_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(lean_object* v_declName_2750_, lean_object* v_env_2751_, lean_object* v_addInfo_2752_, lean_object* v_____r_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_privateToUserName_x3f(v_declName_2750_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_dec_ref(v_addInfo_2752_);
lean_dec_ref(v_env_2751_);
v___x_2762_ = lean_box(0);
v___x_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
return v___x_2763_;
}
else
{
lean_object* v_val_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2781_; 
v_val_2764_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2766_ = v___x_2761_;
v_isShared_2767_ = v_isSharedCheck_2781_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_val_2764_);
lean_dec(v___x_2761_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2781_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
uint8_t v___x_2768_; uint8_t v___x_2769_; 
v___x_2768_ = 1;
lean_inc(v_val_2764_);
v___x_2769_ = l_Lean_Environment_contains(v_env_2751_, v_val_2764_, v___x_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_dec(v_val_2764_);
lean_dec_ref(v_addInfo_2752_);
v___x_2770_ = lean_box(0);
if (v_isShared_2767_ == 0)
{
lean_ctor_set_tag(v___x_2766_, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2770_);
v___x_2772_ = v___x_2766_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
else
{
lean_object* v___x_2774_; 
lean_del_object(v___x_2766_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc_ref(v___y_2754_);
lean_inc(v_val_2764_);
v___x_2774_ = lean_apply_8(v_addInfo_2752_, v_val_2764_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, lean_box(0));
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_dec_ref_known(v___x_2774_, 1);
v___x_2775_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
v___x_2776_ = l_Lean_MessageData_ofConstName(v_val_2764_, v___x_2768_);
v___x_2777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2779_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
return v___x_2780_;
}
else
{
lean_dec(v_val_2764_);
return v___x_2774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed(lean_object* v_declName_2782_, lean_object* v_env_2783_, lean_object* v_addInfo_2784_, lean_object* v_____r_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(v_declName_2782_, v_env_2783_, v_addInfo_2784_, v_____r_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(lean_object* v_addInfo_2794_, lean_object* v_declName_2795_, uint8_t v___x_2796_, lean_object* v___f_2797_, uint8_t v___x_2798_, lean_object* v_env_2799_, lean_object* v___f_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; 
lean_inc(v___y_2806_);
lean_inc_ref(v___y_2805_);
lean_inc(v___y_2804_);
lean_inc_ref(v___y_2803_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v_declName_2795_);
v___x_2808_ = lean_apply_8(v_addInfo_2794_, v_declName_2795_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, lean_box(0));
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v___x_2809_; 
lean_dec_ref_known(v___x_2808_, 1);
lean_inc(v_declName_2795_);
v___x_2809_ = l_Lean_privateToUserName_x3f(v_declName_2795_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2810_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2811_ = l_Lean_MessageData_ofConstName(v_declName_2795_, v___x_2796_);
v___x_2812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2812_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v___x_2815_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2814_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
return v___x_2815_;
}
else
{
lean_object* v_val_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
lean_dec(v_declName_2795_);
v_val_2816_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_val_2816_);
lean_dec_ref_known(v___x_2809_, 1);
v___x_2817_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1);
v___x_2818_ = l_Lean_MessageData_ofConstName(v_val_2816_, v___x_2796_);
v___x_2819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2817_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2819_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2821_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
return v___x_2822_;
}
}
else
{
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v_declName_2795_);
return v___x_2808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed(lean_object* v_addInfo_2823_, lean_object* v_declName_2824_, lean_object* v___x_2825_, lean_object* v___f_2826_, lean_object* v___x_2827_, lean_object* v_env_2828_, lean_object* v___f_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
uint8_t v___x_17770__boxed_2837_; uint8_t v___x_17772__boxed_2838_; lean_object* v_res_2839_; 
v___x_17770__boxed_2837_ = lean_unbox(v___x_2825_);
v___x_17772__boxed_2838_ = lean_unbox(v___x_2827_);
v_res_2839_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(v_addInfo_2823_, v_declName_2824_, v___x_17770__boxed_2837_, v___f_2826_, v___x_17772__boxed_2838_, v_env_2828_, v___f_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec_ref(v___f_2829_);
lean_dec_ref(v_env_2828_);
lean_dec_ref(v___f_2826_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(lean_object* v_declName_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v___x_2851_; lean_object* v_env_2852_; uint8_t v___x_2853_; lean_object* v_addInfo_2854_; lean_object* v_env_2855_; lean_object* v___f_2856_; lean_object* v___f_2857_; lean_object* v___x_2858_; lean_object* v___f_2859_; uint8_t v___x_2860_; uint8_t v___x_2861_; 
v___x_2851_ = lean_st_ref_get(v___y_2849_);
v_env_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc_ref(v_env_2852_);
lean_dec(v___x_2851_);
v___x_2853_ = 0;
v_addInfo_2854_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0));
v_env_2855_ = l_Lean_Environment_setExporting(v_env_2852_, v___x_2853_);
lean_inc_ref_n(v_env_2855_, 4);
lean_inc_n(v_declName_2843_, 4);
v___f_2856_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed), 11, 3);
lean_closure_set(v___f_2856_, 0, v_declName_2843_);
lean_closure_set(v___f_2856_, 1, v_env_2855_);
lean_closure_set(v___f_2856_, 2, v_addInfo_2854_);
v___f_2857_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2857_, 0, v_env_2855_);
lean_closure_set(v___f_2857_, 1, v_declName_2843_);
lean_closure_set(v___f_2857_, 2, v___f_2856_);
lean_closure_set(v___f_2857_, 3, v_addInfo_2854_);
v___x_2858_ = lean_box(v___x_2853_);
lean_inc_ref(v___f_2857_);
v___f_2859_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed), 12, 4);
lean_closure_set(v___f_2859_, 0, v___f_2857_);
lean_closure_set(v___f_2859_, 1, v_declName_2843_);
lean_closure_set(v___f_2859_, 2, v___x_2858_);
lean_closure_set(v___f_2859_, 3, v_env_2855_);
v___x_2860_ = 1;
v___x_2861_ = l_Lean_Environment_contains(v_env_2855_, v_declName_2843_, v___x_2860_);
if (v___x_2861_ == 0)
{
lean_object* v___f_2862_; lean_object* v___x_2863_; 
lean_dec_ref(v___f_2857_);
lean_dec(v_declName_2843_);
v___f_2862_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed), 8, 1);
lean_closure_set(v___f_2862_, 0, v___f_2859_);
v___x_2863_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2855_, v___f_2862_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
return v___x_2863_;
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___f_2866_; lean_object* v___x_2867_; 
v___x_2864_ = lean_box(v___x_2860_);
v___x_2865_ = lean_box(v___x_2853_);
lean_inc_ref(v_env_2855_);
v___f_2866_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed), 14, 7);
lean_closure_set(v___f_2866_, 0, v_addInfo_2854_);
lean_closure_set(v___f_2866_, 1, v_declName_2843_);
lean_closure_set(v___f_2866_, 2, v___x_2864_);
lean_closure_set(v___f_2866_, 3, v___f_2857_);
lean_closure_set(v___f_2866_, 4, v___x_2865_);
lean_closure_set(v___f_2866_, 5, v_env_2855_);
lean_closure_set(v___f_2866_, 6, v___f_2859_);
v___x_2867_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2855_, v___f_2866_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
return v___x_2867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___boxed(lean_object* v_declName_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(lean_object* v_modifiers_2877_, lean_object* v_declName_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_declName_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___x_2951_; lean_object* v_env_2952_; uint8_t v_visibility_2953_; uint8_t v___x_2954_; 
v___x_2951_ = lean_st_ref_get(v___y_2884_);
v_env_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc_ref(v_env_2952_);
lean_dec(v___x_2951_);
v_visibility_2953_ = lean_ctor_get_uint8(v_modifiers_2877_, sizeof(void*)*3);
v___x_2954_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_2952_, v_visibility_2953_);
lean_dec_ref(v_env_2952_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; lean_object* v_env_2956_; lean_object* v_declName_2957_; 
v___x_2955_ = lean_st_ref_get(v___y_2884_);
v_env_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc_ref(v_env_2956_);
lean_dec(v___x_2955_);
v_declName_2957_ = l_Lean_mkPrivateName(v_env_2956_, v_declName_2878_);
lean_dec_ref(v_env_2956_);
v_declName_2887_ = v_declName_2957_;
v___y_2888_ = v___y_2879_;
v___y_2889_ = v___y_2880_;
v___y_2890_ = v___y_2881_;
v___y_2891_ = v___y_2882_;
v___y_2892_ = v___y_2883_;
v___y_2893_ = v___y_2884_;
goto v___jp_2886_;
}
else
{
v_declName_2887_ = v_declName_2878_;
v___y_2888_ = v___y_2879_;
v___y_2889_ = v___y_2880_;
v___y_2890_ = v___y_2881_;
v___y_2891_ = v___y_2882_;
v___y_2892_ = v___y_2883_;
v___y_2893_ = v___y_2884_;
goto v___jp_2886_;
}
v___jp_2886_:
{
lean_object* v___x_2894_; 
lean_inc(v_declName_2887_);
v___x_2894_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2941_; 
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2941_ == 0)
{
lean_object* v_unused_2942_; 
v_unused_2942_ = lean_ctor_get(v___x_2894_, 0);
lean_dec(v_unused_2942_);
v___x_2896_ = v___x_2894_;
v_isShared_2897_ = v_isSharedCheck_2941_;
goto v_resetjp_2895_;
}
else
{
lean_dec(v___x_2894_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2941_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
uint8_t v_isProtected_2898_; 
v_isProtected_2898_ = lean_ctor_get_uint8(v_modifiers_2877_, sizeof(void*)*3 + 1);
if (v_isProtected_2898_ == 0)
{
lean_object* v___x_2900_; 
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v_declName_2887_);
v___x_2900_ = v___x_2896_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_declName_2887_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
else
{
lean_object* v___x_2902_; lean_object* v_env_2903_; lean_object* v_nextMacroScope_2904_; lean_object* v_ngen_2905_; lean_object* v_auxDeclNGen_2906_; lean_object* v_traceState_2907_; lean_object* v_recordedDeps_2908_; lean_object* v_messages_2909_; lean_object* v_infoState_2910_; lean_object* v_snapshotTasks_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2939_; 
v___x_2902_ = lean_st_ref_take(v___y_2893_);
v_env_2903_ = lean_ctor_get(v___x_2902_, 0);
v_nextMacroScope_2904_ = lean_ctor_get(v___x_2902_, 1);
v_ngen_2905_ = lean_ctor_get(v___x_2902_, 2);
v_auxDeclNGen_2906_ = lean_ctor_get(v___x_2902_, 3);
v_traceState_2907_ = lean_ctor_get(v___x_2902_, 4);
v_recordedDeps_2908_ = lean_ctor_get(v___x_2902_, 6);
v_messages_2909_ = lean_ctor_get(v___x_2902_, 7);
v_infoState_2910_ = lean_ctor_get(v___x_2902_, 8);
v_snapshotTasks_2911_ = lean_ctor_get(v___x_2902_, 9);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2939_ == 0)
{
lean_object* v_unused_2940_; 
v_unused_2940_ = lean_ctor_get(v___x_2902_, 5);
lean_dec(v_unused_2940_);
v___x_2913_ = v___x_2902_;
v_isShared_2914_ = v_isSharedCheck_2939_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_snapshotTasks_2911_);
lean_inc(v_infoState_2910_);
lean_inc(v_messages_2909_);
lean_inc(v_recordedDeps_2908_);
lean_inc(v_traceState_2907_);
lean_inc(v_auxDeclNGen_2906_);
lean_inc(v_ngen_2905_);
lean_inc(v_nextMacroScope_2904_);
lean_inc(v_env_2903_);
lean_dec(v___x_2902_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2939_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2918_; 
lean_inc(v_declName_2887_);
v___x_2915_ = l_Lean_addProtected(v_env_2903_, v_declName_2887_);
v___x_2916_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 5, v___x_2916_);
lean_ctor_set(v___x_2913_, 0, v___x_2915_);
v___x_2918_ = v___x_2913_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_nextMacroScope_2904_);
lean_ctor_set(v_reuseFailAlloc_2938_, 2, v_ngen_2905_);
lean_ctor_set(v_reuseFailAlloc_2938_, 3, v_auxDeclNGen_2906_);
lean_ctor_set(v_reuseFailAlloc_2938_, 4, v_traceState_2907_);
lean_ctor_set(v_reuseFailAlloc_2938_, 5, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2938_, 6, v_recordedDeps_2908_);
lean_ctor_set(v_reuseFailAlloc_2938_, 7, v_messages_2909_);
lean_ctor_set(v_reuseFailAlloc_2938_, 8, v_infoState_2910_);
lean_ctor_set(v_reuseFailAlloc_2938_, 9, v_snapshotTasks_2911_);
v___x_2918_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v_mctx_2921_; lean_object* v_zetaDeltaFVarIds_2922_; lean_object* v_postponed_2923_; lean_object* v_diag_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2936_; 
v___x_2919_ = lean_st_ref_put(v___y_2893_, v___x_2918_);
v___x_2920_ = lean_st_ref_take(v___y_2891_);
v_mctx_2921_ = lean_ctor_get(v___x_2920_, 0);
v_zetaDeltaFVarIds_2922_ = lean_ctor_get(v___x_2920_, 2);
v_postponed_2923_ = lean_ctor_get(v___x_2920_, 3);
v_diag_2924_ = lean_ctor_get(v___x_2920_, 4);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2936_ == 0)
{
lean_object* v_unused_2937_; 
v_unused_2937_ = lean_ctor_get(v___x_2920_, 1);
lean_dec(v_unused_2937_);
v___x_2926_ = v___x_2920_;
v_isShared_2927_ = v_isSharedCheck_2936_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_diag_2924_);
lean_inc(v_postponed_2923_);
lean_inc(v_zetaDeltaFVarIds_2922_);
lean_inc(v_mctx_2921_);
lean_dec(v___x_2920_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2936_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2928_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 1, v___x_2928_);
v___x_2930_ = v___x_2926_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_mctx_2921_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v___x_2928_);
lean_ctor_set(v_reuseFailAlloc_2935_, 2, v_zetaDeltaFVarIds_2922_);
lean_ctor_set(v_reuseFailAlloc_2935_, 3, v_postponed_2923_);
lean_ctor_set(v_reuseFailAlloc_2935_, 4, v_diag_2924_);
v___x_2930_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2931_; lean_object* v___x_2933_; 
v___x_2931_ = lean_st_ref_put(v___y_2891_, v___x_2930_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v_declName_2887_);
v___x_2933_ = v___x_2896_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_declName_2887_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
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
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec(v_declName_2887_);
v_a_2943_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2894_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2894_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4___boxed(lean_object* v_modifiers_2958_, lean_object* v_declName_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2958_, v_declName_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec_ref(v_modifiers_2958_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(lean_object* v_pre_2968_, lean_object* v_declName_2969_, lean_object* v_as_2970_, size_t v_sz_2971_, size_t v_i_2972_, lean_object* v_b_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v_a_2982_; uint8_t v___x_2986_; 
v___x_2986_ = lean_usize_dec_lt(v_i_2972_, v_sz_2971_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; 
lean_dec(v_declName_2969_);
lean_dec(v_pre_2968_);
v___x_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2987_, 0, v_b_2973_);
return v___x_2987_;
}
else
{
lean_object* v___x_2988_; lean_object* v_a_2989_; lean_object* v___x_2990_; uint8_t v___x_2991_; 
v___x_2988_ = lean_box(0);
v_a_2989_ = lean_array_uget_borrowed(v_as_2970_, v_i_2972_);
lean_inc(v_a_2989_);
lean_inc(v_pre_2968_);
v___x_2990_ = l_Lean_Name_append(v_pre_2968_, v_a_2989_);
v___x_2991_ = lean_name_eq(v___x_2990_, v_declName_2969_);
lean_dec(v___x_2990_);
if (v___x_2991_ == 0)
{
v_a_2982_ = v___x_2988_;
goto v___jp_2981_;
}
else
{
lean_object* v___x_2992_; uint8_t v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_2992_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_2993_ = 0;
lean_inc(v_declName_2969_);
v___x_2994_ = l_Lean_MessageData_ofConstName(v_declName_2969_, v___x_2993_);
v___x_2995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2992_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
v___x_2996_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_2997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2995_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
lean_inc(v_pre_2968_);
v___x_2998_ = l_Lean_MessageData_ofName(v_pre_2968_);
v___x_2999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2997_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
v___x_3000_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_3001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_2999_);
lean_ctor_set(v___x_3001_, 1, v___x_3000_);
lean_inc(v_a_2989_);
v___x_3002_ = l_Lean_MessageData_ofName(v_a_2989_);
v___x_3003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3001_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_3005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3003_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
v___x_3006_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3005_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_dec_ref_known(v___x_3006_, 1);
v_a_2982_ = v___x_2988_;
goto v___jp_2981_;
}
else
{
lean_dec(v_declName_2969_);
lean_dec(v_pre_2968_);
return v___x_3006_;
}
}
}
v___jp_2981_:
{
size_t v___x_2983_; size_t v___x_2984_; 
v___x_2983_ = ((size_t)1ULL);
v___x_2984_ = lean_usize_add(v_i_2972_, v___x_2983_);
v_i_2972_ = v___x_2984_;
v_b_2973_ = v_a_2982_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6___boxed(lean_object* v_pre_3007_, lean_object* v_declName_3008_, lean_object* v_as_3009_, lean_object* v_sz_3010_, lean_object* v_i_3011_, lean_object* v_b_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
size_t v_sz_boxed_3020_; size_t v_i_boxed_3021_; lean_object* v_res_3022_; 
v_sz_boxed_3020_ = lean_unbox_usize(v_sz_3010_);
lean_dec(v_sz_3010_);
v_i_boxed_3021_ = lean_unbox_usize(v_i_3011_);
lean_dec(v_i_3011_);
v_res_3022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_3007_, v_declName_3008_, v_as_3009_, v_sz_boxed_3020_, v_i_boxed_3021_, v_b_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec_ref(v_as_3009_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(lean_object* v_declName_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
if (lean_obj_tag(v_declName_3023_) == 1)
{
lean_object* v_pre_3031_; lean_object* v___x_3032_; lean_object* v_env_3033_; uint8_t v___x_3034_; 
v_pre_3031_ = lean_ctor_get(v_declName_3023_, 0);
lean_inc_n(v_pre_3031_, 2);
v___x_3032_ = lean_st_ref_get(v___y_3029_);
v_env_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc_ref(v_env_3033_);
lean_dec(v___x_3032_);
v___x_3034_ = l_Lean_isStructure(v_env_3033_, v_pre_3031_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
lean_dec_ref_known(v_declName_3023_, 2);
lean_dec(v_pre_3031_);
v___x_3035_ = lean_box(0);
v___x_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
return v___x_3036_;
}
else
{
lean_object* v___x_3037_; lean_object* v_env_3038_; lean_object* v_fieldNames_3039_; lean_object* v___x_3040_; size_t v_sz_3041_; size_t v___x_3042_; lean_object* v___x_3043_; 
v___x_3037_ = lean_st_ref_get(v___y_3029_);
v_env_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc_ref(v_env_3038_);
lean_dec(v___x_3037_);
lean_inc(v_pre_3031_);
v_fieldNames_3039_ = l_Lean_getStructureFieldsFlattened(v_env_3038_, v_pre_3031_, v___x_3034_);
v___x_3040_ = lean_box(0);
v_sz_3041_ = lean_array_size(v_fieldNames_3039_);
v___x_3042_ = ((size_t)0ULL);
v___x_3043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_3031_, v_declName_3023_, v_fieldNames_3039_, v_sz_3041_, v___x_3042_, v___x_3040_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
lean_dec_ref(v_fieldNames_3039_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3050_ == 0)
{
lean_object* v_unused_3051_; 
v_unused_3051_ = lean_ctor_get(v___x_3043_, 0);
lean_dec(v_unused_3051_);
v___x_3045_ = v___x_3043_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_dec(v___x_3043_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3040_);
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3040_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
else
{
return v___x_3043_;
}
}
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
lean_dec(v_declName_3023_);
v___x_3052_ = lean_box(0);
v___x_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
return v___x_3053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3___boxed(lean_object* v_declName_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v_declName_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(lean_object* v_currNamespace_3063_, lean_object* v_modifiers_3064_, lean_object* v_shortName_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3079_; lean_object* v_shortName_3080_; lean_object* v_currNamespace_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v_view_3141_; lean_object* v_name_3142_; lean_object* v_imported_3143_; lean_object* v_ctx_3144_; lean_object* v_scopes_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3203_; 
lean_inc(v_shortName_3065_);
v_view_3141_ = l_Lean_extractMacroScopes(v_shortName_3065_);
v_name_3142_ = lean_ctor_get(v_view_3141_, 0);
v_imported_3143_ = lean_ctor_get(v_view_3141_, 1);
v_ctx_3144_ = lean_ctor_get(v_view_3141_, 2);
v_scopes_3145_ = lean_ctor_get(v_view_3141_, 3);
v_isSharedCheck_3203_ = !lean_is_exclusive(v_view_3141_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3147_ = v_view_3141_;
v_isShared_3148_ = v_isSharedCheck_3203_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_scopes_3145_);
lean_inc(v_ctx_3144_);
lean_inc(v_imported_3143_);
lean_inc(v_name_3142_);
lean_dec(v_view_3141_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3203_;
goto v_resetjp_3146_;
}
v___jp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___y_3075_);
lean_ctor_set(v___x_3076_, 1, v___y_3074_);
v___x_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3076_);
return v___x_3077_;
}
v___jp_3078_:
{
lean_object* v___x_3088_; 
lean_inc(v___y_3079_);
v___x_3088_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v___y_3079_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v___x_3089_; 
lean_dec_ref_known(v___x_3088_, 1);
v___x_3089_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_3064_, v___y_3079_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3089_) == 0)
{
uint8_t v_isProtected_3090_; 
v_isProtected_3090_ = lean_ctor_get_uint8(v_modifiers_3064_, sizeof(void*)*3 + 1);
if (v_isProtected_3090_ == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_currNamespace_3081_);
v_a_3091_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3093_ = v___x_3089_;
v_isShared_3094_ = v_isSharedCheck_3099_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3089_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3099_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3095_, 0, v_a_3091_);
lean_ctor_set(v___x_3095_, 1, v_shortName_3080_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3095_);
v___x_3097_ = v___x_3093_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
else
{
if (lean_obj_tag(v_currNamespace_3081_) == 1)
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3112_; 
v_a_3100_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3102_ = v___x_3089_;
v_isShared_3103_ = v_isSharedCheck_3112_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3089_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3112_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v_str_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; 
v_str_3104_ = lean_ctor_get(v_currNamespace_3081_, 1);
lean_inc_ref(v_str_3104_);
lean_dec_ref_known(v_currNamespace_3081_, 2);
v___x_3105_ = lean_box(0);
v___x_3106_ = l_Lean_Name_str___override(v___x_3105_, v_str_3104_);
v___x_3107_ = l_Lean_Name_append(v___x_3106_, v_shortName_3080_);
v___x_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3108_, 0, v_a_3100_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3108_);
v___x_3110_ = v___x_3102_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
else
{
lean_object* v_a_3113_; uint8_t v___x_3114_; 
lean_dec(v_currNamespace_3081_);
v_a_3113_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3089_, 1);
v___x_3114_ = l_Lean_Name_isAtomic(v_shortName_3080_);
if (v___x_3114_ == 0)
{
v___y_3074_ = v_shortName_3080_;
v___y_3075_ = v_a_3113_;
goto v___jp_3073_;
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec(v_a_3113_);
lean_dec(v_shortName_3080_);
v___x_3115_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_3116_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3115_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3116_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3116_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_dec(v_currNamespace_3081_);
lean_dec(v_shortName_3080_);
v_a_3125_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3089_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3089_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec(v_currNamespace_3081_);
lean_dec(v_shortName_3080_);
lean_dec(v___y_3079_);
v_a_3133_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3088_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3088_);
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
v_resetjp_3146_:
{
lean_object* v___x_3149_; uint8_t v_isRootName_3150_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; uint8_t v___x_3192_; 
v___x_3149_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_3150_ = l_Lean_Name_isPrefixOf(v___x_3149_, v_name_3142_);
v___x_3192_ = lean_name_eq(v_name_3142_, v___x_3149_);
if (v___x_3192_ == 0)
{
v___y_3179_ = v___y_3066_;
v___y_3180_ = v___y_3067_;
v___y_3181_ = v___y_3068_;
v___y_3182_ = v___y_3069_;
v___y_3183_ = v___y_3070_;
v___y_3184_ = v___y_3071_;
goto v___jp_3178_;
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_del_object(v___x_3147_);
lean_dec(v_scopes_3145_);
lean_dec(v_ctx_3144_);
lean_dec(v_imported_3143_);
lean_dec(v_name_3142_);
lean_dec(v_shortName_3065_);
lean_dec(v_currNamespace_3063_);
v___x_3193_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_3194_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3193_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
v___jp_3151_:
{
if (v_isRootName_3150_ == 0)
{
lean_dec(v_name_3142_);
v___y_3079_ = v___y_3158_;
v_shortName_3080_ = v_shortName_3065_;
v_currNamespace_3081_ = v_currNamespace_3063_;
v___y_3082_ = v___y_3153_;
v___y_3083_ = v___y_3154_;
v___y_3084_ = v___y_3155_;
v___y_3085_ = v___y_3152_;
v___y_3086_ = v___y_3156_;
v___y_3087_ = v___y_3157_;
goto v___jp_3078_;
}
else
{
lean_dec(v_shortName_3065_);
lean_dec(v_currNamespace_3063_);
if (lean_obj_tag(v_name_3142_) == 1)
{
lean_object* v_pre_3159_; lean_object* v_str_3160_; lean_object* v___x_3161_; lean_object* v_shortName_3162_; lean_object* v_currNamespace_3163_; 
v_pre_3159_ = lean_ctor_get(v_name_3142_, 0);
lean_inc(v_pre_3159_);
v_str_3160_ = lean_ctor_get(v_name_3142_, 1);
lean_inc_ref(v_str_3160_);
lean_dec_ref_known(v_name_3142_, 2);
v___x_3161_ = lean_box(0);
v_shortName_3162_ = l_Lean_Name_str___override(v___x_3161_, v_str_3160_);
v_currNamespace_3163_ = l_Lean_Name_replacePrefix(v_pre_3159_, v___x_3149_, v___x_3161_);
v___y_3079_ = v___y_3158_;
v_shortName_3080_ = v_shortName_3162_;
v_currNamespace_3081_ = v_currNamespace_3163_;
v___y_3082_ = v___y_3153_;
v___y_3083_ = v___y_3154_;
v___y_3084_ = v___y_3155_;
v___y_3085_ = v___y_3152_;
v___y_3086_ = v___y_3156_;
v___y_3087_ = v___y_3157_;
goto v___jp_3078_;
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec(v___y_3158_);
v___x_3164_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_3165_ = l_Lean_MessageData_ofName(v_name_3142_);
v___x_3166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3164_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_3168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3166_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3168_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3152_, v___y_3156_, v___y_3157_);
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
}
v___jp_3178_:
{
if (v_isRootName_3150_ == 0)
{
lean_object* v___x_3185_; 
lean_del_object(v___x_3147_);
lean_dec(v_scopes_3145_);
lean_dec(v_ctx_3144_);
lean_dec(v_imported_3143_);
lean_inc(v_shortName_3065_);
lean_inc(v_currNamespace_3063_);
v___x_3185_ = l_Lean_Name_append(v_currNamespace_3063_, v_shortName_3065_);
v___y_3152_ = v___y_3182_;
v___y_3153_ = v___y_3179_;
v___y_3154_ = v___y_3180_;
v___y_3155_ = v___y_3181_;
v___y_3156_ = v___y_3183_;
v___y_3157_ = v___y_3184_;
v___y_3158_ = v___x_3185_;
goto v___jp_3151_;
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3186_ = lean_box(0);
lean_inc(v_name_3142_);
v___x_3187_ = l_Lean_Name_replacePrefix(v_name_3142_, v___x_3149_, v___x_3186_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v___x_3187_);
v___x_3189_ = v___x_3147_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_imported_3143_);
lean_ctor_set(v_reuseFailAlloc_3191_, 2, v_ctx_3144_);
lean_ctor_set(v_reuseFailAlloc_3191_, 3, v_scopes_3145_);
v___x_3189_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_Lean_MacroScopesView_review(v___x_3189_);
v___y_3152_ = v___y_3182_;
v___y_3153_ = v___y_3179_;
v___y_3154_ = v___y_3180_;
v___y_3155_ = v___y_3181_;
v___y_3156_ = v___y_3183_;
v___y_3157_ = v___y_3184_;
v___y_3158_ = v___x_3190_;
goto v___jp_3151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2___boxed(lean_object* v_currNamespace_3204_, lean_object* v_modifiers_3205_, lean_object* v_shortName_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3204_, v_modifiers_3205_, v_shortName_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec_ref(v_modifiers_3205_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(uint8_t v___x_3215_, lean_object* v_as_3216_, size_t v_i_3217_, size_t v_stop_3218_, lean_object* v_b_3219_){
_start:
{
lean_object* v___y_3221_; uint8_t v___x_3225_; 
v___x_3225_ = lean_usize_dec_eq(v_i_3217_, v_stop_3218_);
if (v___x_3225_ == 0)
{
lean_object* v_fst_3226_; uint8_t v___x_3227_; 
v_fst_3226_ = lean_ctor_get(v_b_3219_, 0);
v___x_3227_ = lean_unbox(v_fst_3226_);
if (v___x_3227_ == 0)
{
lean_object* v_snd_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3237_; 
v_snd_3228_ = lean_ctor_get(v_b_3219_, 1);
v_isSharedCheck_3237_ = !lean_is_exclusive(v_b_3219_);
if (v_isSharedCheck_3237_ == 0)
{
lean_object* v_unused_3238_; 
v_unused_3238_ = lean_ctor_get(v_b_3219_, 0);
lean_dec(v_unused_3238_);
v___x_3230_ = v_b_3219_;
v_isShared_3231_ = v_isSharedCheck_3237_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_snd_3228_);
lean_dec(v_b_3219_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3237_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
uint8_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3235_; 
v___x_3232_ = 1;
v___x_3233_ = lean_box(v___x_3232_);
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 0, v___x_3233_);
v___x_3235_ = v___x_3230_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v_snd_3228_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
v___y_3221_ = v___x_3235_;
goto v___jp_3220_;
}
}
}
else
{
lean_object* v_snd_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3249_; 
v_snd_3239_ = lean_ctor_get(v_b_3219_, 1);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_b_3219_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; 
v_unused_3250_ = lean_ctor_get(v_b_3219_, 0);
lean_dec(v_unused_3250_);
v___x_3241_ = v_b_3219_;
v_isShared_3242_ = v_isSharedCheck_3249_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_snd_3239_);
lean_dec(v_b_3219_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3249_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3247_; 
v___x_3243_ = lean_array_uget_borrowed(v_as_3216_, v_i_3217_);
lean_inc(v___x_3243_);
v___x_3244_ = lean_array_push(v_snd_3239_, v___x_3243_);
v___x_3245_ = lean_box(v___x_3215_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 1, v___x_3244_);
lean_ctor_set(v___x_3241_, 0, v___x_3245_);
v___x_3247_ = v___x_3241_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v___x_3244_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
v___y_3221_ = v___x_3247_;
goto v___jp_3220_;
}
}
}
}
else
{
return v_b_3219_;
}
v___jp_3220_:
{
size_t v___x_3222_; size_t v___x_3223_; 
v___x_3222_ = ((size_t)1ULL);
v___x_3223_ = lean_usize_add(v_i_3217_, v___x_3222_);
v_i_3217_ = v___x_3223_;
v_b_3219_ = v___y_3221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4___boxed(lean_object* v___x_3251_, lean_object* v_as_3252_, lean_object* v_i_3253_, lean_object* v_stop_3254_, lean_object* v_b_3255_){
_start:
{
uint8_t v___x_18479__boxed_3256_; size_t v_i_boxed_3257_; size_t v_stop_boxed_3258_; lean_object* v_res_3259_; 
v___x_18479__boxed_3256_ = lean_unbox(v___x_3251_);
v_i_boxed_3257_ = lean_unbox_usize(v_i_3253_);
lean_dec(v_i_3253_);
v_stop_boxed_3258_ = lean_unbox_usize(v_stop_3254_);
lean_dec(v_stop_3254_);
v_res_3259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_18479__boxed_3256_, v_as_3252_, v_i_boxed_3257_, v_stop_boxed_3258_, v_b_3255_);
lean_dec_ref(v_as_3252_);
return v_res_3259_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(lean_object* v_a_3260_, lean_object* v_x_3261_){
_start:
{
if (lean_obj_tag(v_x_3261_) == 0)
{
uint8_t v___x_3262_; 
v___x_3262_ = 0;
return v___x_3262_;
}
else
{
lean_object* v_head_3263_; lean_object* v_tail_3264_; uint8_t v___x_3265_; 
v_head_3263_ = lean_ctor_get(v_x_3261_, 0);
v_tail_3264_ = lean_ctor_get(v_x_3261_, 1);
v___x_3265_ = lean_name_eq(v_a_3260_, v_head_3263_);
if (v___x_3265_ == 0)
{
v_x_3261_ = v_tail_3264_;
goto _start;
}
else
{
return v___x_3265_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_expandDeclId_spec__0___boxed(lean_object* v_a_3267_, lean_object* v_x_3268_){
_start:
{
uint8_t v_res_3269_; lean_object* v_r_3270_; 
v_res_3269_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_a_3267_, v_x_3268_);
lean_dec(v_x_3268_);
lean_dec(v_a_3267_);
v_r_3270_ = lean_box(v_res_3269_);
return v_r_3270_;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = ((lean_object*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0));
v___x_3273_ = l_Lean_stringToMessageData(v___x_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(lean_object* v_u_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3282_ = lean_obj_once(&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1, &l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1);
v___x_3283_ = l_Lean_MessageData_ofName(v_u_3274_);
v___x_3284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3282_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3286_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___boxed(lean_object* v_u_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(lean_object* v_as_3297_, size_t v_i_3298_, size_t v_stop_3299_, lean_object* v_b_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v_a_3309_; uint8_t v___x_3313_; 
v___x_3313_ = lean_usize_dec_eq(v_i_3298_, v_stop_3299_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; lean_object* v_id_3315_; uint8_t v___x_3316_; 
v___x_3314_ = lean_array_uget_borrowed(v_as_3297_, v_i_3298_);
v_id_3315_ = l_Lean_Syntax_getId(v___x_3314_);
v___x_3316_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_id_3315_, v_b_3300_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; 
v___x_3317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3317_, 0, v_id_3315_);
lean_ctor_set(v___x_3317_, 1, v_b_3300_);
v_a_3309_ = v___x_3317_;
goto v___jp_3308_;
}
else
{
lean_object* v_toCold_3318_; lean_object* v_currRecDepth_3319_; lean_object* v_ref_3320_; uint16_t v_optionFlags_3321_; uint8_t v_suppressElabErrors_3322_; uint8_t v_isRecordingDeps_3323_; lean_object* v_ref_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
lean_dec(v_b_3300_);
v_toCold_3318_ = lean_ctor_get(v___y_3305_, 0);
v_currRecDepth_3319_ = lean_ctor_get(v___y_3305_, 1);
v_ref_3320_ = lean_ctor_get(v___y_3305_, 2);
v_optionFlags_3321_ = lean_ctor_get_uint16(v___y_3305_, sizeof(void*)*3);
v_suppressElabErrors_3322_ = lean_ctor_get_uint8(v___y_3305_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3323_ = lean_ctor_get_uint8(v___y_3305_, sizeof(void*)*3 + 3);
v_ref_3324_ = l_Lean_replaceRef(v___x_3314_, v_ref_3320_);
lean_inc(v_currRecDepth_3319_);
lean_inc_ref(v_toCold_3318_);
v___x_3325_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3325_, 0, v_toCold_3318_);
lean_ctor_set(v___x_3325_, 1, v_currRecDepth_3319_);
lean_ctor_set(v___x_3325_, 2, v_ref_3324_);
lean_ctor_set_uint16(v___x_3325_, sizeof(void*)*3, v_optionFlags_3321_);
lean_ctor_set_uint8(v___x_3325_, sizeof(void*)*3 + 2, v_suppressElabErrors_3322_);
lean_ctor_set_uint8(v___x_3325_, sizeof(void*)*3 + 3, v_isRecordingDeps_3323_);
v___x_3326_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_id_3315_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___x_3325_, v___y_3306_);
lean_dec_ref_known(v___x_3325_, 3);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
v_a_3309_ = v_a_3327_;
goto v___jp_3308_;
}
else
{
return v___x_3326_;
}
}
}
else
{
lean_object* v___x_3328_; 
v___x_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3328_, 0, v_b_3300_);
return v___x_3328_;
}
v___jp_3308_:
{
size_t v___x_3310_; size_t v___x_3311_; 
v___x_3310_ = ((size_t)1ULL);
v___x_3311_ = lean_usize_add(v_i_3298_, v___x_3310_);
v_i_3298_ = v___x_3311_;
v_b_3300_ = v_a_3309_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3___boxed(lean_object* v_as_3329_, lean_object* v_i_3330_, lean_object* v_stop_3331_, lean_object* v_b_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
size_t v_i_boxed_3340_; size_t v_stop_boxed_3341_; lean_object* v_res_3342_; 
v_i_boxed_3340_ = lean_unbox_usize(v_i_3330_);
lean_dec(v_i_3330_);
v_stop_boxed_3341_ = lean_unbox_usize(v_stop_3331_);
lean_dec(v_stop_3331_);
v_res_3342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v_as_3329_, v_i_boxed_3340_, v_stop_boxed_3341_, v_b_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec_ref(v_as_3329_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId(lean_object* v_currNamespace_3343_, lean_object* v_currLevelNames_3344_, lean_object* v_declId_3345_, lean_object* v_modifiers_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v___x_3354_; lean_object* v_fst_3355_; lean_object* v_snd_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3436_; 
v___x_3354_ = l_Lean_Elab_expandDeclIdCore(v_declId_3345_);
v_fst_3355_ = lean_ctor_get(v___x_3354_, 0);
v_snd_3356_ = lean_ctor_get(v___x_3354_, 1);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3358_ = v___x_3354_;
v_isShared_3359_ = v_isSharedCheck_3436_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_snd_3356_);
lean_inc(v_fst_3355_);
lean_dec(v___x_3354_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3436_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v_levelNames_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3398_; lean_object* v___y_3409_; uint8_t v___x_3420_; 
v___x_3420_ = l_Lean_Syntax_isNone(v_snd_3356_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
v___x_3421_ = lean_unsigned_to_nat(1u);
v___x_3422_ = l_Lean_Syntax_getArg(v_snd_3356_, v___x_3421_);
lean_dec(v_snd_3356_);
v___x_3423_ = l_Lean_Syntax_getArgs(v___x_3422_);
lean_dec(v___x_3422_);
v___x_3424_ = lean_unsigned_to_nat(0u);
v___x_3425_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__0));
v___x_3426_ = lean_array_get_size(v___x_3423_);
v___x_3427_ = lean_nat_dec_lt(v___x_3424_, v___x_3426_);
if (v___x_3427_ == 0)
{
lean_dec_ref(v___x_3423_);
lean_del_object(v___x_3358_);
v___y_3409_ = v___x_3425_;
goto v___jp_3408_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3430_; 
v___x_3428_ = lean_box(v___x_3427_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 1, v___x_3425_);
lean_ctor_set(v___x_3358_, 0, v___x_3428_);
v___x_3430_ = v___x_3358_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3428_);
lean_ctor_set(v_reuseFailAlloc_3435_, 1, v___x_3425_);
v___x_3430_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
size_t v___x_3431_; size_t v___x_3432_; lean_object* v___x_3433_; lean_object* v_snd_3434_; 
v___x_3431_ = ((size_t)0ULL);
v___x_3432_ = lean_usize_of_nat(v___x_3426_);
v___x_3433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3420_, v___x_3423_, v___x_3431_, v___x_3432_, v___x_3430_);
lean_dec_ref(v___x_3423_);
v_snd_3434_ = lean_ctor_get(v___x_3433_, 1);
lean_inc(v_snd_3434_);
lean_dec_ref(v___x_3433_);
v___y_3409_ = v_snd_3434_;
goto v___jp_3408_;
}
}
}
else
{
lean_del_object(v___x_3358_);
lean_dec(v_snd_3356_);
v_levelNames_3361_ = v_currLevelNames_3344_;
v___y_3362_ = v_a_3347_;
v___y_3363_ = v_a_3348_;
v___y_3364_ = v_a_3349_;
v___y_3365_ = v_a_3350_;
v___y_3366_ = v_a_3351_;
v___y_3367_ = v_a_3352_;
goto v___jp_3360_;
}
v___jp_3360_:
{
lean_object* v_toCold_3368_; lean_object* v_currRecDepth_3369_; lean_object* v_ref_3370_; uint16_t v_optionFlags_3371_; uint8_t v_suppressElabErrors_3372_; uint8_t v_isRecordingDeps_3373_; lean_object* v_ref_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v_toCold_3368_ = lean_ctor_get(v___y_3366_, 0);
v_currRecDepth_3369_ = lean_ctor_get(v___y_3366_, 1);
v_ref_3370_ = lean_ctor_get(v___y_3366_, 2);
v_optionFlags_3371_ = lean_ctor_get_uint16(v___y_3366_, sizeof(void*)*3);
v_suppressElabErrors_3372_ = lean_ctor_get_uint8(v___y_3366_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3373_ = lean_ctor_get_uint8(v___y_3366_, sizeof(void*)*3 + 3);
v_ref_3374_ = l_Lean_replaceRef(v_declId_3345_, v_ref_3370_);
lean_inc(v_currRecDepth_3369_);
lean_inc_ref(v_toCold_3368_);
v___x_3375_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3375_, 0, v_toCold_3368_);
lean_ctor_set(v___x_3375_, 1, v_currRecDepth_3369_);
lean_ctor_set(v___x_3375_, 2, v_ref_3374_);
lean_ctor_set_uint16(v___x_3375_, sizeof(void*)*3, v_optionFlags_3371_);
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*3 + 2, v_suppressElabErrors_3372_);
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*3 + 3, v_isRecordingDeps_3373_);
v___x_3376_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3343_, v_modifiers_3346_, v_fst_3355_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___x_3375_, v___y_3367_);
lean_dec_ref_known(v___x_3375_, 3);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3388_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3379_ = v___x_3376_;
v_isShared_3380_ = v_isSharedCheck_3388_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3376_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3388_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v_fst_3381_; lean_object* v_snd_3382_; lean_object* v_docString_x3f_3383_; lean_object* v___x_3384_; lean_object* v___x_3386_; 
v_fst_3381_ = lean_ctor_get(v_a_3377_, 0);
lean_inc(v_fst_3381_);
v_snd_3382_ = lean_ctor_get(v_a_3377_, 1);
lean_inc(v_snd_3382_);
lean_dec(v_a_3377_);
v_docString_x3f_3383_ = lean_ctor_get(v_modifiers_3346_, 1);
lean_inc(v_docString_x3f_3383_);
v___x_3384_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3384_, 0, v_snd_3382_);
lean_ctor_set(v___x_3384_, 1, v_fst_3381_);
lean_ctor_set(v___x_3384_, 2, v_levelNames_3361_);
lean_ctor_set(v___x_3384_, 3, v_docString_x3f_3383_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3384_);
v___x_3386_ = v___x_3379_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3384_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec(v_levelNames_3361_);
v_a_3389_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3376_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3376_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
v___jp_3397_:
{
if (lean_obj_tag(v___y_3398_) == 0)
{
lean_object* v_a_3399_; 
v_a_3399_ = lean_ctor_get(v___y_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___y_3398_, 1);
v_levelNames_3361_ = v_a_3399_;
v___y_3362_ = v_a_3347_;
v___y_3363_ = v_a_3348_;
v___y_3364_ = v_a_3349_;
v___y_3365_ = v_a_3350_;
v___y_3366_ = v_a_3351_;
v___y_3367_ = v_a_3352_;
goto v___jp_3360_;
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v_fst_3355_);
lean_dec(v_currNamespace_3343_);
v_a_3400_ = lean_ctor_get(v___y_3398_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___y_3398_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___y_3398_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___y_3398_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
v___jp_3408_:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v___x_3410_ = lean_unsigned_to_nat(0u);
v___x_3411_ = lean_array_get_size(v___y_3409_);
v___x_3412_ = lean_nat_dec_lt(v___x_3410_, v___x_3411_);
if (v___x_3412_ == 0)
{
lean_dec_ref(v___y_3409_);
v_levelNames_3361_ = v_currLevelNames_3344_;
v___y_3362_ = v_a_3347_;
v___y_3363_ = v_a_3348_;
v___y_3364_ = v_a_3349_;
v___y_3365_ = v_a_3350_;
v___y_3366_ = v_a_3351_;
v___y_3367_ = v_a_3352_;
goto v___jp_3360_;
}
else
{
uint8_t v___x_3413_; 
v___x_3413_ = lean_nat_dec_le(v___x_3411_, v___x_3411_);
if (v___x_3413_ == 0)
{
if (v___x_3412_ == 0)
{
lean_dec_ref(v___y_3409_);
v_levelNames_3361_ = v_currLevelNames_3344_;
v___y_3362_ = v_a_3347_;
v___y_3363_ = v_a_3348_;
v___y_3364_ = v_a_3349_;
v___y_3365_ = v_a_3350_;
v___y_3366_ = v_a_3351_;
v___y_3367_ = v_a_3352_;
goto v___jp_3360_;
}
else
{
size_t v___x_3414_; size_t v___x_3415_; lean_object* v___x_3416_; 
v___x_3414_ = ((size_t)0ULL);
v___x_3415_ = lean_usize_of_nat(v___x_3411_);
v___x_3416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3409_, v___x_3414_, v___x_3415_, v_currLevelNames_3344_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
lean_dec_ref(v___y_3409_);
v___y_3398_ = v___x_3416_;
goto v___jp_3397_;
}
}
else
{
size_t v___x_3417_; size_t v___x_3418_; lean_object* v___x_3419_; 
v___x_3417_ = ((size_t)0ULL);
v___x_3418_ = lean_usize_of_nat(v___x_3411_);
v___x_3419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3409_, v___x_3417_, v___x_3418_, v_currLevelNames_3344_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
lean_dec_ref(v___y_3409_);
v___y_3398_ = v___x_3419_;
goto v___jp_3397_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___boxed(lean_object* v_currNamespace_3437_, lean_object* v_currLevelNames_3438_, lean_object* v_declId_3439_, lean_object* v_modifiers_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Lean_Elab_expandDeclId(v_currNamespace_3437_, v_currLevelNames_3438_, v_declId_3439_, v_modifiers_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_);
lean_dec(v_a_3446_);
lean_dec_ref(v_a_3445_);
lean_dec(v_a_3444_);
lean_dec_ref(v_a_3443_);
lean_dec(v_a_3442_);
lean_dec_ref(v_a_3441_);
lean_dec_ref(v_modifiers_3440_);
lean_dec(v_declId_3439_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(lean_object* v_00_u03b1_3449_, lean_object* v_u_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___boxed(lean_object* v_00_u03b1_3459_, lean_object* v_u_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(v_00_u03b1_3459_, v_u_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(lean_object* v_00_u03b1_3469_, lean_object* v_msg_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3479_, lean_object* v_msg_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(v_00_u03b1_3479_, v_msg_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(lean_object* v_msgData_3489_, lean_object* v_macroStack_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_3489_, v_macroStack_3490_, v___y_3495_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_3499_, lean_object* v_macroStack_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(v_msgData_3499_, v_macroStack_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(lean_object* v_t_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___x_3517_; 
v___x_3517_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_3509_, v___y_3515_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___boxed(lean_object* v_t_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(v_t_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(lean_object* v_env_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_3527_, v___y_3531_, v___y_3533_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___boxed(lean_object* v_env_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(v_env_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(lean_object* v_00_u03b1_3545_, lean_object* v_env_3546_, lean_object* v_x_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_3546_, v_x_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3556_, lean_object* v_env_3557_, lean_object* v_x_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(v_00_u03b1_3556_, v_env_3557_, v_x_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(lean_object* v_00_u03b1_3567_, lean_object* v_constName_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___boxed(lean_object* v_00_u03b1_3577_, lean_object* v_constName_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(v_00_u03b1_3577_, v_constName_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(lean_object* v_00_u03b1_3587_, lean_object* v_ref_3588_, lean_object* v_constName_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_3588_, v_constName_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___boxed(lean_object* v_00_u03b1_3598_, lean_object* v_ref_3599_, lean_object* v_constName_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(v_00_u03b1_3598_, v_ref_3599_, v_constName_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v_ref_3599_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(lean_object* v_00_u03b1_3609_, lean_object* v_ref_3610_, lean_object* v_msg_3611_, lean_object* v_declHint_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_3610_, v_msg_3611_, v_declHint_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___boxed(lean_object* v_00_u03b1_3621_, lean_object* v_ref_3622_, lean_object* v_msg_3623_, lean_object* v_declHint_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(v_00_u03b1_3621_, v_ref_3622_, v_msg_3623_, v_declHint_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v_ref_3622_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(lean_object* v_msg_3633_, lean_object* v_declHint_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_3633_, v_declHint_3634_, v___y_3640_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___boxed(lean_object* v_msg_3643_, lean_object* v_declHint_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(v_msg_3643_, v_declHint_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(lean_object* v_00_u03b1_3653_, lean_object* v_ref_3654_, lean_object* v_msg_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_3654_, v_msg_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___boxed(lean_object* v_00_u03b1_3664_, lean_object* v_ref_3665_, lean_object* v_msg_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(v_00_u03b1_3664_, v_ref_3665_, v_msg_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v_ref_3665_);
return v_res_3674_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(lean_object* v_x_3678_){
_start:
{
lean_object* v_name_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; 
v_name_3679_ = lean_ctor_get(v_x_3678_, 0);
v___x_3680_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__1));
v___x_3681_ = lean_name_eq(v_name_3679_, v___x_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___boxed(lean_object* v_x_3682_){
_start:
{
uint8_t v_res_3683_; lean_object* v_r_3684_; 
v_res_3683_ = l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(v_x_3682_);
lean_dec_ref(v_x_3682_);
v_r_3684_ = lean_box(v_res_3683_);
return v_r_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__1(lean_object* v_ctx_3685_){
_start:
{
lean_object* v_declName_x3f_3686_; lean_object* v_macroStack_3687_; uint8_t v_mayPostpone_3688_; uint8_t v_errToSorry_3689_; lean_object* v_autoBoundImplicitContext_3690_; lean_object* v_autoBoundImplicitForbidden_3691_; lean_object* v_sectionVars_3692_; lean_object* v_sectionFVars_3693_; uint8_t v_implicitLambda_3694_; uint8_t v_heedElabAsElim_3695_; uint8_t v_isNoncomputableSection_3696_; uint8_t v_isMetaSection_3697_; uint8_t v_ignoreTCFailures_3698_; uint8_t v_inPattern_3699_; lean_object* v_tacSnap_x3f_3700_; uint8_t v_saveRecAppSyntax_3701_; uint8_t v_holesAsSyntheticOpaque_3702_; lean_object* v_fixedTermElabs_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3711_; 
v_declName_x3f_3686_ = lean_ctor_get(v_ctx_3685_, 0);
v_macroStack_3687_ = lean_ctor_get(v_ctx_3685_, 1);
v_mayPostpone_3688_ = lean_ctor_get_uint8(v_ctx_3685_, sizeof(void*)*8);
v_errToSorry_3689_ = lean_ctor_get_uint8(v_ctx_3685_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_3690_ = lean_ctor_get(v_ctx_3685_, 2);
v_autoBoundImplicitForbidden_3691_ = lean_ctor_get(v_ctx_3685_, 3);
v_sectionVars_3692_ = lean_ctor_get(v_ctx_3685_, 4);
v_sectionFVars_3693_ = lean_ctor_get(v_ctx_3685_, 5);
v_implicitLambda_3694_ = lean_ctor_get_uint8(v_ctx_3685_, sizeof(void*)*8 + 2);
v_heedElabAsElim_3695_ = lean_ctor_get_uint8(v_ctx_3685_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_3696_ = lean_ctor_get_uint8(v_ctx_3685_, sizeof(void*)*8 + 4);
v_isMetaSection_3697_ = lean_ctor_get_uint8(v_ctx_3685_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_3698_ = lean_ctor_get_uint8(v_ctx_3685_, sizeof(void*)*8 + 6);
v_inPattern_3699_ = lean_ctor_get_uint8(v_ctx_3685_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_3700_ = lean_ctor_get(v_ctx_3685_, 6);
v_saveRecAppSyntax_3701_ = lean_ctor_get_uint8(v_ctx_3685_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_3702_ = lean_ctor_get_uint8(v_ctx_3685_, sizeof(void*)*8 + 9);
v_fixedTermElabs_3703_ = lean_ctor_get(v_ctx_3685_, 7);
v_isSharedCheck_3711_ = !lean_is_exclusive(v_ctx_3685_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3705_ = v_ctx_3685_;
v_isShared_3706_ = v_isSharedCheck_3711_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_fixedTermElabs_3703_);
lean_inc(v_tacSnap_x3f_3700_);
lean_inc(v_sectionFVars_3693_);
lean_inc(v_sectionVars_3692_);
lean_inc(v_autoBoundImplicitForbidden_3691_);
lean_inc(v_autoBoundImplicitContext_3690_);
lean_inc(v_macroStack_3687_);
lean_inc(v_declName_x3f_3686_);
lean_dec(v_ctx_3685_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3711_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
uint8_t v___x_3707_; lean_object* v___x_3709_; 
v___x_3707_ = 0;
if (v_isShared_3706_ == 0)
{
v___x_3709_ = v___x_3705_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_declName_x3f_3686_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_macroStack_3687_);
lean_ctor_set(v_reuseFailAlloc_3710_, 2, v_autoBoundImplicitContext_3690_);
lean_ctor_set(v_reuseFailAlloc_3710_, 3, v_autoBoundImplicitForbidden_3691_);
lean_ctor_set(v_reuseFailAlloc_3710_, 4, v_sectionVars_3692_);
lean_ctor_set(v_reuseFailAlloc_3710_, 5, v_sectionFVars_3693_);
lean_ctor_set(v_reuseFailAlloc_3710_, 6, v_tacSnap_x3f_3700_);
lean_ctor_set(v_reuseFailAlloc_3710_, 7, v_fixedTermElabs_3703_);
lean_ctor_set_uint8(v_reuseFailAlloc_3710_, sizeof(void*)*8, v_mayPostpone_3688_);
lean_ctor_set_uint8(v_reuseFailAlloc_3710_, sizeof(void*)*8 + 1, v_errToSorry_3689_);
lean_ctor_set_uint8(v_reuseFailAlloc_3710_, sizeof(void*)*8 + 2, v_implicitLambda_3694_);
lean_ctor_set_uint8(v_reuseFailAlloc_3710_, sizeof(void*)*8 + 3, v_heedElabAsElim_3695_);
lean_ctor_set_uint8(v_reuseFailAlloc_3710_, sizeof(void*)*8 + 4, v_isNoncomputableSection_3696_);
lean_ctor_set_uint8(v_reuseFailAlloc_3710_, sizeof(void*)*8 + 5, v_isMetaSection_3697_);
lean_ctor_set_uint8(v_reuseFailAlloc_3710_, sizeof(void*)*8 + 6, v_ignoreTCFailures_3698_);
lean_ctor_set_uint8(v_reuseFailAlloc_3710_, sizeof(void*)*8 + 7, v_inPattern_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3710_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_3701_);
lean_ctor_set_uint8(v_reuseFailAlloc_3710_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_3702_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_ctor_set_uint8(v___x_3709_, sizeof(void*)*8 + 10, v___x_3707_);
return v___x_3709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg(lean_object* v_inst_3733_, lean_object* v_attrs_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; uint8_t v___x_3739_; 
v___x_3736_ = lean_unsigned_to_nat(0u);
v___x_3737_ = lean_array_get_size(v_attrs_3734_);
v___x_3738_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9));
v___x_3739_ = lean_nat_dec_lt(v___x_3736_, v___x_3737_);
if (v___x_3739_ == 0)
{
lean_dec_ref(v_attrs_3734_);
lean_dec(v_inst_3733_);
return v_a_3735_;
}
else
{
if (v___x_3739_ == 0)
{
lean_dec_ref(v_attrs_3734_);
lean_dec(v_inst_3733_);
return v_a_3735_;
}
else
{
lean_object* v___f_3740_; size_t v___x_3741_; size_t v___x_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; 
v___f_3740_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10));
v___x_3741_ = ((size_t)0ULL);
v___x_3742_ = lean_usize_of_nat(v___x_3737_);
v___x_3743_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_3738_, v___f_3740_, v_attrs_3734_, v___x_3741_, v___x_3742_);
v___x_3744_ = lean_unbox(v___x_3743_);
lean_dec(v___x_3743_);
if (v___x_3744_ == 0)
{
lean_dec(v_inst_3733_);
return v_a_3735_;
}
else
{
lean_object* v___f_3745_; lean_object* v___x_3746_; 
v___f_3745_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11));
v___x_3746_ = lean_apply_3(v_inst_3733_, lean_box(0), v___f_3745_, v_a_3735_);
return v___x_3746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs(lean_object* v_m_3747_, lean_object* v_00_u03b1_3748_, lean_object* v_inst_3749_, lean_object* v_attrs_3750_, lean_object* v_a_3751_){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3752_ = lean_unsigned_to_nat(0u);
v___x_3753_ = lean_array_get_size(v_attrs_3750_);
v___x_3754_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9));
v___x_3755_ = lean_nat_dec_lt(v___x_3752_, v___x_3753_);
if (v___x_3755_ == 0)
{
lean_dec_ref(v_attrs_3750_);
lean_dec(v_inst_3749_);
return v_a_3751_;
}
else
{
if (v___x_3755_ == 0)
{
lean_dec_ref(v_attrs_3750_);
lean_dec(v_inst_3749_);
return v_a_3751_;
}
else
{
lean_object* v___f_3756_; size_t v___x_3757_; size_t v___x_3758_; lean_object* v___x_3759_; uint8_t v___x_3760_; 
v___f_3756_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10));
v___x_3757_ = ((size_t)0ULL);
v___x_3758_ = lean_usize_of_nat(v___x_3753_);
v___x_3759_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_3754_, v___f_3756_, v_attrs_3750_, v___x_3757_, v___x_3758_);
v___x_3760_ = lean_unbox(v___x_3759_);
lean_dec(v___x_3759_);
if (v___x_3760_ == 0)
{
lean_dec(v_inst_3749_);
return v_a_3751_;
}
else
{
lean_object* v___f_3761_; lean_object* v___x_3762_; 
v___f_3761_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11));
v___x_3762_ = lean_apply_3(v_inst_3749_, lean_box(0), v___f_3761_, v_a_3751_);
return v___x_3762_;
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
