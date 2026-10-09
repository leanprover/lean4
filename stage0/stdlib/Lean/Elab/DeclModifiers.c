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
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = ((lean_object*)(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_));
v___x_53_ = ((lean_object*)(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__4_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_));
v___x_55_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0(v___x_52_, v___x_53_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_56_;
v_res_56_ = l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_();
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_();
return v_res_58_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_unsigned_to_nat(32u);
v___x_63_ = lean_mk_empty_array_with_capacity(v___x_62_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3(void){
_start:
{
size_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_65_ = ((size_t)5ULL);
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = lean_unsigned_to_nat(32u);
v___x_68_ = lean_mk_empty_array_with_capacity(v___x_67_);
v___x_69_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2);
v___x_70_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_68_);
lean_ctor_set(v___x_70_, 2, v___x_66_);
lean_ctor_set(v___x_70_, 3, v___x_66_);
lean_ctor_set_usize(v___x_70_, 4, v___x_65_);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = lean_box(1);
v___x_72_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3);
v___x_73_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1);
v___x_74_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_72_);
lean_ctor_set(v___x_74_, 2, v___x_71_);
return v___x_74_;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(lean_object* v_____do__lift_75_, uint8_t v___x_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_____do__lift_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_80_ = lean_box(0);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v_____do__lift_75_);
v___x_82_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4);
v___x_83_ = lean_box(0);
v___x_84_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_84_, 0, v___x_81_);
lean_ctor_set(v___x_84_, 1, v___x_82_);
lean_ctor_set(v___x_84_, 2, v___x_83_);
lean_ctor_set(v___x_84_, 3, v_____do__lift_79_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*4, v___x_76_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*4 + 1, v___x_76_);
v___x_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
v___x_86_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_77_, v_inst_78_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT void l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_75_ = stack[0].m_obj;
uint8_t v___x_76_ = stack[1].m_num;
lean_object* v_inst_77_ = stack[2].m_obj;
lean_object* v_inst_78_ = stack[3].m_obj;
lean_object* v_____do__lift_79_ = stack[4].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(v_____do__lift_75_, v___x_76_, v_inst_77_, v_inst_78_, v_____do__lift_79_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___boxed(lean_object* v_____do__lift_88_, lean_object* v___x_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_____do__lift_92_){
_start:
{
uint8_t v___x_688__boxed_93_; lean_object* v_res_94_; 
v___x_688__boxed_93_ = lean_unbox(v___x_89_);
v_res_94_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(v_____do__lift_88_, v___x_688__boxed_93_, v_inst_90_, v_inst_91_, v_____do__lift_92_);
return v_res_94_;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(uint8_t v___x_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_declName_100_, lean_object* v_toBind_101_, lean_object* v_____do__lift_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___f_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_103_ = lean_box(v___x_95_);
lean_inc_ref(v_inst_96_);
v___f_104_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_104_, 0, v_____do__lift_102_);
lean_closure_set(v___f_104_, 1, v___x_103_);
lean_closure_set(v___f_104_, 2, v_inst_96_);
lean_closure_set(v___f_104_, 3, v_inst_97_);
v___x_105_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_96_, v_inst_98_, v_inst_99_, v_declName_100_);
v___x_106_ = lean_apply_4(v_toBind_101_, lean_box(0), lean_box(0), v___x_105_, v___f_104_);
return v___x_106_;
}
}
LEAN_EXPORT void l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_95_ = stack[0].m_num;
lean_object* v_inst_96_ = stack[1].m_obj;
lean_object* v_inst_97_ = stack[2].m_obj;
lean_object* v_inst_98_ = stack[3].m_obj;
lean_object* v_inst_99_ = stack[4].m_obj;
lean_object* v_declName_100_ = stack[5].m_obj;
lean_object* v_toBind_101_ = stack[6].m_obj;
lean_object* v_____do__lift_102_ = stack[7].m_obj;
lean_object* v_res_107_;
v_res_107_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(v___x_95_, v_inst_96_, v_inst_97_, v_inst_98_, v_inst_99_, v_declName_100_, v_toBind_101_, v_____do__lift_102_);
stack->m_obj
 = v_res_107_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1___boxed(lean_object* v___x_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_declName_113_, lean_object* v_toBind_114_, lean_object* v_____do__lift_115_){
_start:
{
uint8_t v___x_765__boxed_116_; lean_object* v_res_117_; 
v___x_765__boxed_116_ = lean_unbox(v___x_108_);
v_res_117_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(v___x_765__boxed_116_, v_inst_109_, v_inst_110_, v_inst_111_, v_inst_112_, v_declName_113_, v_toBind_114_, v_____do__lift_115_);
return v_res_117_;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(lean_object* v_toMonadRef_118_, uint8_t v___x_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_toBind_124_, lean_object* v_declName_125_){
_start:
{
lean_object* v_getRef_126_; lean_object* v___x_127_; lean_object* v___f_128_; lean_object* v___x_129_; 
v_getRef_126_ = lean_ctor_get(v_toMonadRef_118_, 0);
lean_inc(v_getRef_126_);
lean_dec_ref(v_toMonadRef_118_);
v___x_127_ = lean_box(v___x_119_);
lean_inc(v_toBind_124_);
v___f_128_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_128_, 0, v___x_127_);
lean_closure_set(v___f_128_, 1, v_inst_120_);
lean_closure_set(v___f_128_, 2, v_inst_121_);
lean_closure_set(v___f_128_, 3, v_inst_122_);
lean_closure_set(v___f_128_, 4, v_inst_123_);
lean_closure_set(v___f_128_, 5, v_declName_125_);
lean_closure_set(v___f_128_, 6, v_toBind_124_);
v___x_129_ = lean_apply_4(v_toBind_124_, lean_box(0), lean_box(0), v_getRef_126_, v___f_128_);
return v___x_129_;
}
}
LEAN_EXPORT void l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_toMonadRef_118_ = stack[0].m_obj;
uint8_t v___x_119_ = stack[1].m_num;
lean_object* v_inst_120_ = stack[2].m_obj;
lean_object* v_inst_121_ = stack[3].m_obj;
lean_object* v_inst_122_ = stack[4].m_obj;
lean_object* v_inst_123_ = stack[5].m_obj;
lean_object* v_toBind_124_ = stack[6].m_obj;
lean_object* v_declName_125_ = stack[7].m_obj;
lean_object* v_res_130_;
v_res_130_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(v_toMonadRef_118_, v___x_119_, v_inst_120_, v_inst_121_, v_inst_122_, v_inst_123_, v_toBind_124_, v_declName_125_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2___boxed(lean_object* v_toMonadRef_131_, lean_object* v___x_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_toBind_137_, lean_object* v_declName_138_){
_start:
{
uint8_t v___x_807__boxed_139_; lean_object* v_res_140_; 
v___x_807__boxed_139_ = lean_unbox(v___x_132_);
v_res_140_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(v_toMonadRef_131_, v___x_807__boxed_139_, v_inst_133_, v_inst_134_, v_inst_135_, v_inst_136_, v_toBind_137_, v_declName_138_);
return v_res_140_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0));
v___x_143_ = l_Lean_stringToMessageData(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2));
v___x_146_ = l_Lean_stringToMessageData(v___x_145_);
return v___x_146_;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(lean_object* v_val_147_, uint8_t v___x_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_____r_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_152_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
v___x_153_ = l_Lean_MessageData_ofConstName(v_val_147_, v___x_148_);
v___x_154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_152_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
v___x_157_ = l_Lean_throwError___redArg(v_inst_149_, v_inst_150_, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT void l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_147_ = stack[0].m_obj;
uint8_t v___x_148_ = stack[1].m_num;
lean_object* v_inst_149_ = stack[2].m_obj;
lean_object* v_inst_150_ = stack[3].m_obj;
lean_object* v_____r_151_ = stack[4].m_obj;
lean_object* v_res_158_;
v_res_158_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(v_val_147_, v___x_148_, v_inst_149_, v_inst_150_, v_____r_151_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___boxed(lean_object* v_val_159_, lean_object* v___x_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_____r_163_){
_start:
{
uint8_t v___x_854__boxed_164_; lean_object* v_res_165_; 
v___x_854__boxed_164_ = lean_unbox(v___x_160_);
v_res_165_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(v_val_159_, v___x_854__boxed_164_, v_inst_161_, v_inst_162_, v_____r_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__4(lean_object* v_declName_166_, lean_object* v_toPure_167_, lean_object* v_env_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_addInfo_171_, lean_object* v_toBind_172_, lean_object* v_____r_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_privateToUserName_x3f(v_declName_166_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_toBind_172_);
lean_dec(v_addInfo_171_);
lean_dec_ref(v_inst_170_);
lean_dec_ref(v_inst_169_);
lean_dec_ref(v_env_168_);
v___x_175_ = lean_box(0);
v___x_176_ = lean_apply_2(v_toPure_167_, lean_box(0), v___x_175_);
return v___x_176_;
}
else
{
lean_object* v_val_177_; uint8_t v___x_178_; uint8_t v___x_179_; 
v_val_177_ = lean_ctor_get(v___x_174_, 0);
lean_inc_n(v_val_177_, 2);
lean_dec_ref_known(v___x_174_, 1);
v___x_178_ = 1;
v___x_179_ = l_Lean_Environment_contains(v_env_168_, v_val_177_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_val_177_);
lean_dec(v_toBind_172_);
lean_dec(v_addInfo_171_);
lean_dec_ref(v_inst_170_);
lean_dec_ref(v_inst_169_);
v___x_180_ = lean_box(0);
v___x_181_ = lean_apply_2(v_toPure_167_, lean_box(0), v___x_180_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec(v_toPure_167_);
v___x_182_ = lean_box(v___x_178_);
lean_inc(v_val_177_);
v___f_183_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_183_, 0, v_val_177_);
lean_closure_set(v___f_183_, 1, v___x_182_);
lean_closure_set(v___f_183_, 2, v_inst_169_);
lean_closure_set(v___f_183_, 3, v_inst_170_);
v___x_184_ = lean_apply_1(v_addInfo_171_, v_val_177_);
v___x_185_ = lean_apply_4(v_toBind_172_, lean_box(0), lean_box(0), v___x_184_, v___f_183_);
return v___x_185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5(lean_object* v___f_186_, lean_object* v_____r_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_apply_1(v___f_186_, v_____r_187_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__0));
v___x_191_ = l_Lean_stringToMessageData(v___x_190_);
return v___x_191_;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(lean_object* v_declName_192_, uint8_t v___x_193_, lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_toBind_196_, lean_object* v___f_197_, lean_object* v_____r_198_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_199_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1);
v___x_200_ = l_Lean_MessageData_ofConstName(v_declName_192_, v___x_193_);
v___x_201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = l_Lean_throwError___redArg(v_inst_194_, v_inst_195_, v___x_203_);
v___x_205_ = lean_apply_4(v_toBind_196_, lean_box(0), lean_box(0), v___x_204_, v___f_197_);
return v___x_205_;
}
}
LEAN_EXPORT void l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_192_ = stack[0].m_obj;
uint8_t v___x_193_ = stack[1].m_num;
lean_object* v_inst_194_ = stack[2].m_obj;
lean_object* v_inst_195_ = stack[3].m_obj;
lean_object* v_toBind_196_ = stack[4].m_obj;
lean_object* v___f_197_ = stack[5].m_obj;
lean_object* v_____r_198_ = stack[6].m_obj;
lean_object* v_res_206_;
v_res_206_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(v_declName_192_, v___x_193_, v_inst_194_, v_inst_195_, v_toBind_196_, v___f_197_, v_____r_198_);
stack->m_obj
 = v_res_206_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___boxed(lean_object* v_declName_207_, lean_object* v___x_208_, lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_toBind_211_, lean_object* v___f_212_, lean_object* v_____r_213_){
_start:
{
uint8_t v___x_971__boxed_214_; lean_object* v_res_215_; 
v___x_971__boxed_214_ = lean_unbox(v___x_208_);
v_res_215_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(v_declName_207_, v___x_971__boxed_214_, v_inst_209_, v_inst_210_, v_toBind_211_, v___f_212_, v_____r_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7(lean_object* v_env_216_, lean_object* v_declName_217_, lean_object* v___f_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_toBind_221_, lean_object* v___f_222_, lean_object* v_addInfo_223_, lean_object* v_____r_224_){
_start:
{
lean_object* v___x_225_; uint8_t v___x_226_; uint8_t v___x_227_; 
lean_inc(v_declName_217_);
v___x_225_ = l_Lean_mkPrivateName(v_env_216_, v_declName_217_);
v___x_226_ = 1;
lean_inc(v___x_225_);
v___x_227_ = l_Lean_Environment_contains(v_env_216_, v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec(v___x_225_);
lean_dec(v_addInfo_223_);
lean_dec(v___f_222_);
lean_dec(v_toBind_221_);
lean_dec_ref(v_inst_220_);
lean_dec_ref(v_inst_219_);
lean_dec(v_declName_217_);
v___x_228_ = lean_box(0);
v___x_229_ = lean_apply_1(v___f_218_, v___x_228_);
return v___x_229_;
}
else
{
lean_object* v___x_230_; lean_object* v___f_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v___f_218_);
v___x_230_ = lean_box(v___x_226_);
lean_inc(v_toBind_221_);
v___f_231_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___boxed), 7, 6);
lean_closure_set(v___f_231_, 0, v_declName_217_);
lean_closure_set(v___f_231_, 1, v___x_230_);
lean_closure_set(v___f_231_, 2, v_inst_219_);
lean_closure_set(v___f_231_, 3, v_inst_220_);
lean_closure_set(v___f_231_, 4, v_toBind_221_);
lean_closure_set(v___f_231_, 5, v___f_222_);
v___x_232_ = lean_apply_1(v_addInfo_223_, v___x_225_);
v___x_233_ = lean_apply_4(v_toBind_221_, lean_box(0), lean_box(0), v___x_232_, v___f_231_);
return v___x_233_;
}
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__0));
v___x_236_ = l_Lean_stringToMessageData(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__2));
v___x_239_ = l_Lean_stringToMessageData(v___x_238_);
return v___x_239_;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(lean_object* v___f_240_, lean_object* v_declName_241_, uint8_t v___x_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_toBind_245_, lean_object* v___f_246_, lean_object* v_env_247_, lean_object* v_____do__lift_248_){
_start:
{
uint8_t v___y_250_; lean_object* v___x_260_; uint8_t v___x_261_; 
lean_inc(v_declName_241_);
v___x_260_ = l_Lean_privateToUserName(v_declName_241_);
lean_inc_ref(v_env_247_);
v___x_261_ = lean_is_reserved_name(v_env_247_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; uint8_t v___x_263_; 
lean_inc(v_declName_241_);
v___x_262_ = l_Lean_mkPrivateName(v_____do__lift_248_, v_declName_241_);
v___x_263_ = lean_is_reserved_name(v_env_247_, v___x_262_);
v___y_250_ = v___x_263_;
goto v___jp_249_;
}
else
{
lean_dec_ref(v_env_247_);
v___y_250_ = v___x_261_;
goto v___jp_249_;
}
v___jp_249_:
{
if (v___y_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v___f_246_);
lean_dec(v_toBind_245_);
lean_dec_ref(v_inst_244_);
lean_dec_ref(v_inst_243_);
lean_dec(v_declName_241_);
v___x_251_ = lean_box(0);
v___x_252_ = lean_apply_1(v___f_240_, v___x_251_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec(v___f_240_);
v___x_253_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_254_ = l_Lean_MessageData_ofConstName(v_declName_241_, v___x_242_);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = l_Lean_throwError___redArg(v_inst_243_, v_inst_244_, v___x_257_);
v___x_259_ = lean_apply_4(v_toBind_245_, lean_box(0), lean_box(0), v___x_258_, v___f_246_);
return v___x_259_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_240_ = stack[0].m_obj;
lean_object* v_declName_241_ = stack[1].m_obj;
uint8_t v___x_242_ = stack[2].m_num;
lean_object* v_inst_243_ = stack[3].m_obj;
lean_object* v_inst_244_ = stack[4].m_obj;
lean_object* v_toBind_245_ = stack[5].m_obj;
lean_object* v___f_246_ = stack[6].m_obj;
lean_object* v_env_247_ = stack[7].m_obj;
lean_object* v_____do__lift_248_ = stack[8].m_obj;
lean_object* v_res_264_;
v_res_264_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(v___f_240_, v_declName_241_, v___x_242_, v_inst_243_, v_inst_244_, v_toBind_245_, v___f_246_, v_env_247_, v_____do__lift_248_);
stack->m_obj
 = v_res_264_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___boxed(lean_object* v___f_265_, lean_object* v_declName_266_, lean_object* v___x_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_toBind_270_, lean_object* v___f_271_, lean_object* v_env_272_, lean_object* v_____do__lift_273_){
_start:
{
uint8_t v___x_1078__boxed_274_; lean_object* v_res_275_; 
v___x_1078__boxed_274_ = lean_unbox(v___x_267_);
v_res_275_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(v___f_265_, v_declName_266_, v___x_1078__boxed_274_, v_inst_268_, v_inst_269_, v_toBind_270_, v___f_271_, v_env_272_, v_____do__lift_273_);
lean_dec_ref(v_____do__lift_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8(lean_object* v_toBind_276_, lean_object* v_getEnv_277_, lean_object* v___f_278_, lean_object* v_____r_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_apply_4(v_toBind_276_, lean_box(0), lean_box(0), v_getEnv_277_, v___f_278_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__0));
v___x_283_ = l_Lean_stringToMessageData(v___x_282_);
return v___x_283_;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(lean_object* v_declName_284_, uint8_t v___x_285_, lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_toBind_288_, lean_object* v___f_289_, lean_object* v___f_290_, lean_object* v_____r_291_){
_start:
{
lean_object* v___x_292_; 
lean_inc(v_declName_284_);
v___x_292_ = l_Lean_privateToUserName_x3f(v_declName_284_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v___f_290_);
v___x_293_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_294_ = l_Lean_MessageData_ofConstName(v_declName_284_, v___x_285_);
v___x_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = l_Lean_throwError___redArg(v_inst_286_, v_inst_287_, v___x_297_);
v___x_299_ = lean_apply_4(v_toBind_288_, lean_box(0), lean_box(0), v___x_298_, v___f_289_);
return v___x_299_;
}
else
{
lean_object* v_val_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec(v___f_289_);
lean_dec(v_declName_284_);
v_val_300_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_val_300_);
lean_dec_ref_known(v___x_292_, 1);
v___x_301_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1);
v___x_302_ = l_Lean_MessageData_ofConstName(v_val_300_, v___x_285_);
v___x_303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = l_Lean_throwError___redArg(v_inst_286_, v_inst_287_, v___x_305_);
v___x_307_ = lean_apply_4(v_toBind_288_, lean_box(0), lean_box(0), v___x_306_, v___f_290_);
return v___x_307_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_284_ = stack[0].m_obj;
uint8_t v___x_285_ = stack[1].m_num;
lean_object* v_inst_286_ = stack[2].m_obj;
lean_object* v_inst_287_ = stack[3].m_obj;
lean_object* v_toBind_288_ = stack[4].m_obj;
lean_object* v___f_289_ = stack[5].m_obj;
lean_object* v___f_290_ = stack[6].m_obj;
lean_object* v_____r_291_ = stack[7].m_obj;
lean_object* v_res_308_;
v_res_308_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(v_declName_284_, v___x_285_, v_inst_286_, v_inst_287_, v_toBind_288_, v___f_289_, v___f_290_, v_____r_291_);
stack->m_obj
 = v_res_308_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___boxed(lean_object* v_declName_309_, lean_object* v___x_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_toBind_313_, lean_object* v___f_314_, lean_object* v___f_315_, lean_object* v_____r_316_){
_start:
{
uint8_t v___x_1188__boxed_317_; lean_object* v_res_318_; 
v___x_1188__boxed_317_ = lean_unbox(v___x_310_);
v_res_318_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(v_declName_309_, v___x_1188__boxed_317_, v_inst_311_, v_inst_312_, v_toBind_313_, v___f_314_, v___f_315_, v_____r_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10(lean_object* v_toMonadRef_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_toBind_324_, lean_object* v_declName_325_, lean_object* v_toPure_326_, lean_object* v_getEnv_327_, lean_object* v_inst_328_, lean_object* v_env_329_){
_start:
{
uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v_addInfo_332_; lean_object* v_env_333_; lean_object* v___f_334_; lean_object* v___f_335_; lean_object* v___f_336_; lean_object* v___f_337_; lean_object* v___x_338_; lean_object* v___f_339_; uint8_t v___x_340_; uint8_t v___x_341_; 
v___x_330_ = 0;
v___x_331_ = lean_box(v___x_330_);
lean_inc_n(v_toBind_324_, 4);
lean_inc_ref_n(v_inst_323_, 4);
lean_inc_ref(v_inst_322_);
lean_inc_ref(v_inst_321_);
lean_inc_ref_n(v_inst_320_, 4);
lean_inc_ref(v_toMonadRef_319_);
v_addInfo_332_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v_addInfo_332_, 0, v_toMonadRef_319_);
lean_closure_set(v_addInfo_332_, 1, v___x_331_);
lean_closure_set(v_addInfo_332_, 2, v_inst_320_);
lean_closure_set(v_addInfo_332_, 3, v_inst_321_);
lean_closure_set(v_addInfo_332_, 4, v_inst_322_);
lean_closure_set(v_addInfo_332_, 5, v_inst_323_);
lean_closure_set(v_addInfo_332_, 6, v_toBind_324_);
v_env_333_ = l_Lean_Environment_setExporting(v_env_329_, v___x_330_);
lean_inc_ref(v_addInfo_332_);
lean_inc_ref_n(v_env_333_, 4);
lean_inc_n(v_declName_325_, 4);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__4), 8, 7);
lean_closure_set(v___f_334_, 0, v_declName_325_);
lean_closure_set(v___f_334_, 1, v_toPure_326_);
lean_closure_set(v___f_334_, 2, v_env_333_);
lean_closure_set(v___f_334_, 3, v_inst_320_);
lean_closure_set(v___f_334_, 4, v_inst_323_);
lean_closure_set(v___f_334_, 5, v_addInfo_332_);
lean_closure_set(v___f_334_, 6, v_toBind_324_);
lean_inc_ref(v___f_334_);
v___f_335_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_335_, 0, v___f_334_);
v___f_336_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7), 9, 8);
lean_closure_set(v___f_336_, 0, v_env_333_);
lean_closure_set(v___f_336_, 1, v_declName_325_);
lean_closure_set(v___f_336_, 2, v___f_334_);
lean_closure_set(v___f_336_, 3, v_inst_320_);
lean_closure_set(v___f_336_, 4, v_inst_323_);
lean_closure_set(v___f_336_, 5, v_toBind_324_);
lean_closure_set(v___f_336_, 6, v___f_335_);
lean_closure_set(v___f_336_, 7, v_addInfo_332_);
lean_inc_ref(v___f_336_);
v___f_337_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_337_, 0, v___f_336_);
v___x_338_ = lean_box(v___x_330_);
v___f_339_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___boxed), 9, 8);
lean_closure_set(v___f_339_, 0, v___f_336_);
lean_closure_set(v___f_339_, 1, v_declName_325_);
lean_closure_set(v___f_339_, 2, v___x_338_);
lean_closure_set(v___f_339_, 3, v_inst_320_);
lean_closure_set(v___f_339_, 4, v_inst_323_);
lean_closure_set(v___f_339_, 5, v_toBind_324_);
lean_closure_set(v___f_339_, 6, v___f_337_);
lean_closure_set(v___f_339_, 7, v_env_333_);
v___x_340_ = 1;
v___x_341_ = l_Lean_Environment_contains(v_env_333_, v_declName_325_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v_declName_325_);
lean_dec_ref(v_inst_323_);
lean_dec_ref(v_inst_321_);
lean_dec_ref(v_toMonadRef_319_);
v___x_342_ = lean_apply_4(v_toBind_324_, lean_box(0), lean_box(0), v_getEnv_327_, v___f_339_);
v___x_343_ = l_Lean_withEnv___redArg(v_inst_320_, v_inst_328_, v_inst_322_, v_env_333_, v___x_342_);
return v___x_343_;
}
else
{
lean_object* v___f_344_; lean_object* v___x_345_; lean_object* v___f_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
lean_inc_n(v_toBind_324_, 3);
v___f_344_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8), 4, 3);
lean_closure_set(v___f_344_, 0, v_toBind_324_);
lean_closure_set(v___f_344_, 1, v_getEnv_327_);
lean_closure_set(v___f_344_, 2, v___f_339_);
v___x_345_ = lean_box(v___x_340_);
lean_inc_ref(v___f_344_);
lean_inc_ref(v_inst_323_);
lean_inc_ref_n(v_inst_320_, 2);
lean_inc(v_declName_325_);
v___f_346_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_346_, 0, v_declName_325_);
lean_closure_set(v___f_346_, 1, v___x_345_);
lean_closure_set(v___f_346_, 2, v_inst_320_);
lean_closure_set(v___f_346_, 3, v_inst_323_);
lean_closure_set(v___f_346_, 4, v_toBind_324_);
lean_closure_set(v___f_346_, 5, v___f_344_);
lean_closure_set(v___f_346_, 6, v___f_344_);
lean_inc_ref(v_inst_322_);
v___x_347_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(v_toMonadRef_319_, v___x_330_, v_inst_320_, v_inst_321_, v_inst_322_, v_inst_323_, v_toBind_324_, v_declName_325_);
v___x_348_ = lean_apply_4(v_toBind_324_, lean_box(0), lean_box(0), v___x_347_, v___f_346_);
v___x_349_ = l_Lean_withEnv___redArg(v_inst_320_, v_inst_328_, v_inst_322_, v_env_333_, v___x_348_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg(lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_declName_355_){
_start:
{
lean_object* v_toApplicative_356_; lean_object* v_toBind_357_; lean_object* v_getEnv_358_; lean_object* v_toMonadRef_359_; lean_object* v_toPure_360_; lean_object* v___f_361_; lean_object* v___x_362_; 
v_toApplicative_356_ = lean_ctor_get(v_inst_350_, 0);
v_toBind_357_ = lean_ctor_get(v_inst_350_, 1);
lean_inc_n(v_toBind_357_, 2);
v_getEnv_358_ = lean_ctor_get(v_inst_351_, 0);
lean_inc_n(v_getEnv_358_, 2);
v_toMonadRef_359_ = lean_ctor_get(v_inst_352_, 1);
lean_inc_ref(v_toMonadRef_359_);
v_toPure_360_ = lean_ctor_get(v_toApplicative_356_, 1);
lean_inc(v_toPure_360_);
v___f_361_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10), 11, 10);
lean_closure_set(v___f_361_, 0, v_toMonadRef_359_);
lean_closure_set(v___f_361_, 1, v_inst_350_);
lean_closure_set(v___f_361_, 2, v_inst_354_);
lean_closure_set(v___f_361_, 3, v_inst_351_);
lean_closure_set(v___f_361_, 4, v_inst_352_);
lean_closure_set(v___f_361_, 5, v_toBind_357_);
lean_closure_set(v___f_361_, 6, v_declName_355_);
lean_closure_set(v___f_361_, 7, v_toPure_360_);
lean_closure_set(v___f_361_, 8, v_getEnv_358_);
lean_closure_set(v___f_361_, 9, v_inst_353_);
v___x_362_ = lean_apply_4(v_toBind_357_, lean_box(0), lean_box(0), v_getEnv_358_, v___f_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared(lean_object* v_m_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_declName_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(v_inst_364_, v_inst_365_, v_inst_366_, v_inst_367_, v_inst_368_, v_declName_369_);
return v___x_370_;
}
}
lean_object* l_Lean_Elab_Visibility_ctorIdx___impl(uint8_t v_x_371_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_box(v_x_371_);
v___x_373_ = lean_obj_tag_nat(v___x_372_);
lean_dec(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT void l_Lean_Elab_Visibility_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_371_ = stack[0].m_num;
lean_object* v_res_374_;
v_res_374_ = l_Lean_Elab_Visibility_ctorIdx___impl(v_x_371_);
stack->m_obj
 = v_res_374_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx___impl___boxed(lean_object* v_x_375_){
_start:
{
uint8_t v_x_4__boxed_376_; lean_object* v_res_377_; 
v_x_4__boxed_376_ = lean_unbox(v_x_375_);
v_res_377_ = l_Lean_Elab_Visibility_ctorIdx___impl(v_x_4__boxed_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___redArg(lean_object* v_k_378_){
_start:
{
lean_inc(v_k_378_);
return v_k_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___redArg___boxed(lean_object* v_k_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Elab_Visibility_ctorElim___redArg(v_k_379_);
lean_dec(v_k_379_);
return v_res_380_;
}
}
lean_object* l_Lean_Elab_Visibility_ctorElim(lean_object* v_motive_381_, lean_object* v_ctorIdx_382_, uint8_t v_t_383_, lean_object* v_h_384_, lean_object* v_k_385_){
_start:
{
lean_inc(v_k_385_);
return v_k_385_;
}
}
LEAN_EXPORT void l_Lean_Elab_Visibility_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_382_ = stack[1].m_obj;
uint8_t v_t_383_ = stack[2].m_num;
lean_object* v_k_385_ = stack[4].m_obj;
lean_object* v_res_386_;
v_res_386_ = l_Lean_Elab_Visibility_ctorElim(lean_box(0), v_ctorIdx_382_, v_t_383_, lean_box(0), v_k_385_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___boxed(lean_object* v_motive_387_, lean_object* v_ctorIdx_388_, lean_object* v_t_389_, lean_object* v_h_390_, lean_object* v_k_391_){
_start:
{
uint8_t v_t_boxed_392_; lean_object* v_res_393_; 
v_t_boxed_392_ = lean_unbox(v_t_389_);
v_res_393_ = l_Lean_Elab_Visibility_ctorElim(v_motive_387_, v_ctorIdx_388_, v_t_boxed_392_, v_h_390_, v_k_391_);
lean_dec(v_k_391_);
lean_dec(v_ctorIdx_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___redArg(lean_object* v_regular_394_){
_start:
{
lean_inc(v_regular_394_);
return v_regular_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___redArg___boxed(lean_object* v_regular_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Elab_Visibility_regular_elim___redArg(v_regular_395_);
lean_dec(v_regular_395_);
return v_res_396_;
}
}
lean_object* l_Lean_Elab_Visibility_regular_elim(lean_object* v_motive_397_, uint8_t v_t_398_, lean_object* v_h_399_, lean_object* v_regular_400_){
_start:
{
lean_inc(v_regular_400_);
return v_regular_400_;
}
}
LEAN_EXPORT void l_Lean_Elab_Visibility_regular_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_398_ = stack[1].m_num;
lean_object* v_regular_400_ = stack[3].m_obj;
lean_object* v_res_401_;
v_res_401_ = l_Lean_Elab_Visibility_regular_elim(lean_box(0), v_t_398_, lean_box(0), v_regular_400_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___boxed(lean_object* v_motive_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_regular_405_){
_start:
{
uint8_t v_t_boxed_406_; lean_object* v_res_407_; 
v_t_boxed_406_ = lean_unbox(v_t_403_);
v_res_407_ = l_Lean_Elab_Visibility_regular_elim(v_motive_402_, v_t_boxed_406_, v_h_404_, v_regular_405_);
lean_dec(v_regular_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___redArg(lean_object* v_private_408_){
_start:
{
lean_inc(v_private_408_);
return v_private_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___redArg___boxed(lean_object* v_private_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Elab_Visibility_private_elim___redArg(v_private_409_);
lean_dec(v_private_409_);
return v_res_410_;
}
}
lean_object* l_Lean_Elab_Visibility_private_elim(lean_object* v_motive_411_, uint8_t v_t_412_, lean_object* v_h_413_, lean_object* v_private_414_){
_start:
{
lean_inc(v_private_414_);
return v_private_414_;
}
}
LEAN_EXPORT void l_Lean_Elab_Visibility_private_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_412_ = stack[1].m_num;
lean_object* v_private_414_ = stack[3].m_obj;
lean_object* v_res_415_;
v_res_415_ = l_Lean_Elab_Visibility_private_elim(lean_box(0), v_t_412_, lean_box(0), v_private_414_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___boxed(lean_object* v_motive_416_, lean_object* v_t_417_, lean_object* v_h_418_, lean_object* v_private_419_){
_start:
{
uint8_t v_t_boxed_420_; lean_object* v_res_421_; 
v_t_boxed_420_ = lean_unbox(v_t_417_);
v_res_421_ = l_Lean_Elab_Visibility_private_elim(v_motive_416_, v_t_boxed_420_, v_h_418_, v_private_419_);
lean_dec(v_private_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___redArg(lean_object* v_public_422_){
_start:
{
lean_inc(v_public_422_);
return v_public_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___redArg___boxed(lean_object* v_public_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Elab_Visibility_public_elim___redArg(v_public_423_);
lean_dec(v_public_423_);
return v_res_424_;
}
}
lean_object* l_Lean_Elab_Visibility_public_elim(lean_object* v_motive_425_, uint8_t v_t_426_, lean_object* v_h_427_, lean_object* v_public_428_){
_start:
{
lean_inc(v_public_428_);
return v_public_428_;
}
}
LEAN_EXPORT void l_Lean_Elab_Visibility_public_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_426_ = stack[1].m_num;
lean_object* v_public_428_ = stack[3].m_obj;
lean_object* v_res_429_;
v_res_429_ = l_Lean_Elab_Visibility_public_elim(lean_box(0), v_t_426_, lean_box(0), v_public_428_);
stack->m_obj
 = v_res_429_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___boxed(lean_object* v_motive_430_, lean_object* v_t_431_, lean_object* v_h_432_, lean_object* v_public_433_){
_start:
{
uint8_t v_t_boxed_434_; lean_object* v_res_435_; 
v_t_boxed_434_ = lean_unbox(v_t_431_);
v_res_435_ = l_Lean_Elab_Visibility_public_elim(v_motive_430_, v_t_boxed_434_, v_h_432_, v_public_433_);
lean_dec(v_public_433_);
return v_res_435_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedVisibility_default(void){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = 0;
return v___x_436_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedVisibility(void){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = 0;
return v___x_437_;
}
}
lean_object* l_Lean_Elab_instToStringVisibility___lam__0(uint8_t v_x_441_){
_start:
{
switch(v_x_441_)
{
case 0:
{
lean_object* v___x_442_; 
v___x_442_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__0));
return v___x_442_;
}
case 1:
{
lean_object* v___x_443_; 
v___x_443_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__1));
return v___x_443_;
}
default: 
{
lean_object* v___x_444_; 
v___x_444_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__2));
return v___x_444_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_instToStringVisibility___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_441_ = stack[0].m_num;
lean_object* v_res_445_;
v_res_445_ = l_Lean_Elab_instToStringVisibility___lam__0(v_x_441_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0___boxed(lean_object* v_x_446_){
_start:
{
uint8_t v_x_36__boxed_447_; lean_object* v_res_448_; 
v_x_36__boxed_447_ = lean_unbox(v_x_446_);
v_res_448_ = l_Lean_Elab_instToStringVisibility___lam__0(v_x_36__boxed_447_);
return v_res_448_;
}
}
uint8_t l_Lean_Elab_Visibility_isPrivate(uint8_t v_x_451_){
_start:
{
if (v_x_451_ == 1)
{
uint8_t v___x_452_; 
v___x_452_ = 1;
return v___x_452_;
}
else
{
uint8_t v___x_453_; 
v___x_453_ = 0;
return v___x_453_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Visibility_isPrivate_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_451_ = stack[0].m_num;
uint8_t v_res_454_;
v_res_454_ = l_Lean_Elab_Visibility_isPrivate(v_x_451_);
stack->m_num = v_res_454_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPrivate___boxed(lean_object* v_x_455_){
_start:
{
uint8_t v_x_17__boxed_456_; uint8_t v_res_457_; lean_object* v_r_458_; 
v_x_17__boxed_456_ = lean_unbox(v_x_455_);
v_res_457_ = l_Lean_Elab_Visibility_isPrivate(v_x_17__boxed_456_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
uint8_t l_Lean_Elab_Visibility_isPublic(uint8_t v_x_459_){
_start:
{
if (v_x_459_ == 2)
{
uint8_t v___x_460_; 
v___x_460_ = 1;
return v___x_460_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Visibility_isPublic_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_459_ = stack[0].m_num;
uint8_t v_res_462_;
v_res_462_ = l_Lean_Elab_Visibility_isPublic(v_x_459_);
stack->m_num = v_res_462_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPublic___boxed(lean_object* v_x_463_){
_start:
{
uint8_t v_x_17__boxed_464_; uint8_t v_res_465_; lean_object* v_r_466_; 
v_x_17__boxed_464_ = lean_unbox(v_x_463_);
v_res_465_ = l_Lean_Elab_Visibility_isPublic(v_x_17__boxed_464_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
uint8_t l_Lean_Elab_Visibility_isInferredPublic(lean_object* v_env_467_, uint8_t v_v_468_){
_start:
{
uint8_t v___y_470_; uint8_t v_isExporting_473_; 
v_isExporting_473_ = lean_ctor_get_uint8(v_env_467_, sizeof(void*)*13);
if (v_isExporting_473_ == 0)
{
lean_object* v___x_474_; uint8_t v_isModule_475_; 
v___x_474_ = l_Lean_Environment_header(v_env_467_);
v_isModule_475_ = lean_ctor_get_uint8(v___x_474_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_474_);
if (v_isModule_475_ == 0)
{
uint8_t v___x_476_; 
v___x_476_ = 1;
v___y_470_ = v___x_476_;
goto v___jp_469_;
}
else
{
uint8_t v___x_477_; 
v___x_477_ = l_Lean_Elab_Visibility_isPublic(v_v_468_);
return v___x_477_;
}
}
else
{
v___y_470_ = v_isExporting_473_;
goto v___jp_469_;
}
v___jp_469_:
{
uint8_t v___x_471_; 
v___x_471_ = l_Lean_Elab_Visibility_isPrivate(v_v_468_);
if (v___x_471_ == 0)
{
return v___y_470_;
}
else
{
uint8_t v___x_472_; 
v___x_472_ = 0;
return v___x_472_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Visibility_isInferredPublic_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_467_ = stack[0].m_obj;
uint8_t v_v_468_ = stack[1].m_num;
uint8_t v_res_478_;
v_res_478_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_467_, v_v_468_);
stack->m_num = v_res_478_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isInferredPublic___boxed(lean_object* v_env_479_, lean_object* v_v_480_){
_start:
{
uint8_t v_v_boxed_481_; uint8_t v_res_482_; lean_object* v_r_483_; 
v_v_boxed_481_ = lean_unbox(v_v_480_);
v_res_482_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_479_, v_v_boxed_481_);
lean_dec_ref(v_env_479_);
v_r_483_ = lean_box(v_res_482_);
return v_r_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__0(lean_object* v_toPure_484_, lean_object* v_____r_485_){
_start:
{
uint8_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = 2;
v___x_487_ = lean_box(v___x_486_);
v___x_488_ = lean_apply_2(v_toPure_484_, lean_box(0), v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__2(lean_object* v_toPure_489_, lean_object* v_____r_490_){
_start:
{
uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = 1;
v___x_492_ = lean_box(v___x_491_);
v___x_493_ = lean_apply_2(v_toPure_489_, lean_box(0), v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__0));
v___x_496_ = l_Lean_stringToMessageData(v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__2));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__10));
v___x_516_ = l_Lean_stringToMessageData(v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__12));
v___x_519_ = l_Lean_stringToMessageData(v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3(lean_object* v_vis_x3f_520_, lean_object* v_toPure_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_toBind_528_, lean_object* v___f_529_, lean_object* v___f_530_, lean_object* v___f_531_, lean_object* v___f_532_, lean_object* v_env_533_){
_start:
{
if (lean_obj_tag(v_vis_x3f_520_) == 0)
{
uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
lean_dec(v___f_532_);
lean_dec(v___f_531_);
lean_dec(v___f_530_);
lean_dec(v___f_529_);
lean_dec(v_toBind_528_);
lean_dec_ref(v_inst_527_);
lean_dec_ref(v_inst_526_);
lean_dec(v_inst_525_);
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_inst_523_);
lean_dec_ref(v_inst_522_);
v___x_537_ = 0;
v___x_538_ = lean_box(v___x_537_);
v___x_539_ = lean_apply_2(v_toPure_521_, lean_box(0), v___x_538_);
return v___x_539_;
}
else
{
lean_object* v_val_540_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; uint8_t v___y_559_; lean_object* v___x_562_; uint8_t v___x_563_; uint8_t v___y_565_; 
lean_dec(v_toPure_521_);
v_val_540_ = lean_ctor_get(v_vis_x3f_520_, 0);
lean_inc_n(v_val_540_, 2);
lean_dec_ref_known(v_vis_x3f_520_, 1);
v___x_562_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8));
v___x_563_ = l_Lean_Syntax_isOfKind(v_val_540_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_569_; uint8_t v___x_570_; 
lean_dec(v___f_532_);
lean_dec(v___f_531_);
v___x_569_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9));
lean_inc(v_val_540_);
v___x_570_ = l_Lean_Syntax_isOfKind(v_val_540_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v___f_530_);
lean_dec(v___f_529_);
lean_dec(v_toBind_528_);
lean_dec_ref(v_inst_527_);
lean_dec_ref(v_inst_526_);
lean_dec(v_inst_525_);
lean_dec_ref(v_inst_524_);
v___x_571_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11);
v___x_572_ = l_Lean_throwErrorAt___redArg(v_inst_522_, v_inst_523_, v_val_540_, v___x_571_);
return v___x_572_;
}
else
{
lean_object* v___x_573_; 
lean_dec_ref(v_inst_523_);
v___x_573_ = l_Lean_Syntax_getHeadInfo(v_val_540_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_dec_ref_known(v___x_573_, 4);
v___y_565_ = v___x_570_;
goto v___jp_564_;
}
else
{
lean_dec(v___x_573_);
if (v___x_563_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v_val_540_);
lean_dec(v___f_529_);
lean_dec(v_toBind_528_);
lean_dec_ref(v_inst_527_);
lean_dec_ref(v_inst_526_);
lean_dec(v_inst_525_);
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_inst_522_);
v___x_574_ = lean_box(0);
v___x_575_ = lean_apply_1(v___f_530_, v___x_574_);
return v___x_575_;
}
else
{
v___y_565_ = v___x_563_;
goto v___jp_564_;
}
}
}
}
else
{
lean_object* v___x_576_; 
lean_dec(v___f_530_);
lean_dec(v___f_529_);
lean_dec_ref(v_inst_523_);
v___x_576_ = l_Lean_Syntax_getHeadInfo(v_val_540_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v___x_577_; uint8_t v_isModule_578_; 
lean_dec_ref_known(v___x_576_, 4);
v___x_577_ = l_Lean_Environment_header(v_env_533_);
v_isModule_578_ = lean_ctor_get_uint8(v___x_577_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_577_);
if (v_isModule_578_ == 0)
{
lean_dec(v_val_540_);
lean_dec(v___f_532_);
lean_dec(v_toBind_528_);
lean_dec_ref(v_inst_527_);
lean_dec_ref(v_inst_526_);
lean_dec(v_inst_525_);
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_inst_522_);
goto v___jp_534_;
}
else
{
uint8_t v_isExporting_579_; 
v_isExporting_579_ = lean_ctor_get_uint8(v_env_533_, sizeof(void*)*13);
if (v_isExporting_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v___f_531_);
v___x_580_ = l_Lean_linter_redundantVisibility;
v___x_581_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13);
v___x_582_ = l_Lean_Linter_logLintIf___redArg(v_inst_522_, v_inst_524_, v_inst_525_, v_inst_526_, v_inst_527_, v___x_580_, v_val_540_, v___x_581_);
v___x_583_ = lean_apply_4(v_toBind_528_, lean_box(0), lean_box(0), v___x_582_, v___f_532_);
return v___x_583_;
}
else
{
lean_dec(v_val_540_);
lean_dec(v___f_532_);
lean_dec(v_toBind_528_);
lean_dec_ref(v_inst_527_);
lean_dec_ref(v_inst_526_);
lean_dec(v_inst_525_);
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_inst_522_);
goto v___jp_534_;
}
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v___x_576_);
lean_dec(v_val_540_);
lean_dec(v___f_532_);
lean_dec(v_toBind_528_);
lean_dec_ref(v_inst_527_);
lean_dec_ref(v_inst_526_);
lean_dec(v_inst_525_);
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_inst_522_);
v___x_584_ = lean_box(0);
v___x_585_ = lean_apply_1(v___f_531_, v___x_584_);
return v___x_585_;
}
}
v___jp_541_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
lean_inc_ref(v___y_544_);
v___x_545_ = l_Lean_stringToMessageData(v___y_544_);
lean_inc_ref(v___y_542_);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___y_542_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
lean_inc_ref(v___y_543_);
v___x_549_ = l_Lean_Linter_logLintIf___redArg(v_inst_522_, v_inst_524_, v_inst_525_, v_inst_526_, v_inst_527_, v___y_543_, v_val_540_, v___x_548_);
v___x_550_ = lean_apply_4(v_toBind_528_, lean_box(0), lean_box(0), v___x_549_, v___f_529_);
return v___x_550_;
}
v___jp_551_:
{
lean_object* v___x_552_; uint8_t v_isModule_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_552_ = l_Lean_Environment_header(v_env_533_);
v_isModule_553_ = lean_ctor_get_uint8(v___x_552_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_552_);
v___x_554_ = l_Lean_linter_redundantVisibility;
v___x_555_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3);
if (v_isModule_553_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4));
v___y_542_ = v___x_555_;
v___y_543_ = v___x_554_;
v___y_544_ = v___x_556_;
goto v___jp_541_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__5));
v___y_542_ = v___x_555_;
v___y_543_ = v___x_554_;
v___y_544_ = v___x_557_;
goto v___jp_541_;
}
}
v___jp_558_:
{
if (v___y_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec(v_val_540_);
lean_dec(v___f_529_);
lean_dec(v_toBind_528_);
lean_dec_ref(v_inst_527_);
lean_dec_ref(v_inst_526_);
lean_dec(v_inst_525_);
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_inst_522_);
v___x_560_ = lean_box(0);
v___x_561_ = lean_apply_1(v___f_530_, v___x_560_);
return v___x_561_;
}
else
{
lean_dec(v___f_530_);
goto v___jp_551_;
}
}
v___jp_564_:
{
uint8_t v_isExporting_566_; 
v_isExporting_566_ = lean_ctor_get_uint8(v_env_533_, sizeof(void*)*13);
if (v_isExporting_566_ == 0)
{
lean_object* v___x_567_; uint8_t v_isModule_568_; 
v___x_567_ = l_Lean_Environment_header(v_env_533_);
v_isModule_568_ = lean_ctor_get_uint8(v___x_567_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_567_);
if (v_isModule_568_ == 0)
{
v___y_559_ = v___y_565_;
goto v___jp_558_;
}
else
{
v___y_559_ = v___x_563_;
goto v___jp_558_;
}
}
else
{
lean_dec(v___f_530_);
goto v___jp_551_;
}
}
}
v___jp_534_:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_box(0);
v___x_536_ = lean_apply_1(v___f_531_, v___x_535_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg___lam__3___boxed(lean_object* v_vis_x3f_586_, lean_object* v_toPure_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_toBind_594_, lean_object* v___f_595_, lean_object* v___f_596_, lean_object* v___f_597_, lean_object* v___f_598_, lean_object* v_env_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Elab_elabVisibility___redArg___lam__3(v_vis_x3f_586_, v_toPure_587_, v_inst_588_, v_inst_589_, v_inst_590_, v_inst_591_, v_inst_592_, v_inst_593_, v_toBind_594_, v___f_595_, v___f_596_, v___f_597_, v___f_598_, v_env_599_);
lean_dec_ref(v_env_599_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg(lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_vis_x3f_607_){
_start:
{
lean_object* v_toApplicative_608_; lean_object* v_toBind_609_; lean_object* v_getEnv_610_; lean_object* v_toPure_611_; lean_object* v___f_612_; lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v___f_615_; lean_object* v___f_616_; lean_object* v___x_617_; 
v_toApplicative_608_ = lean_ctor_get(v_inst_601_, 0);
v_toBind_609_ = lean_ctor_get(v_inst_601_, 1);
lean_inc_n(v_toBind_609_, 2);
v_getEnv_610_ = lean_ctor_get(v_inst_603_, 0);
lean_inc(v_getEnv_610_);
v_toPure_611_ = lean_ctor_get(v_toApplicative_608_, 1);
lean_inc_n(v_toPure_611_, 3);
v___f_612_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__0), 2, 1);
lean_closure_set(v___f_612_, 0, v_toPure_611_);
lean_inc_ref(v___f_612_);
v___f_613_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_613_, 0, v___f_612_);
v___f_614_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__2), 2, 1);
lean_closure_set(v___f_614_, 0, v_toPure_611_);
lean_inc_ref(v___f_614_);
v___f_615_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_615_, 0, v___f_614_);
v___f_616_ = lean_alloc_closure((void*)(l_Lean_Elab_elabVisibility___redArg___lam__3___boxed), 14, 13);
lean_closure_set(v___f_616_, 0, v_vis_x3f_607_);
lean_closure_set(v___f_616_, 1, v_toPure_611_);
lean_closure_set(v___f_616_, 2, v_inst_601_);
lean_closure_set(v___f_616_, 3, v_inst_602_);
lean_closure_set(v___f_616_, 4, v_inst_605_);
lean_closure_set(v___f_616_, 5, v_inst_606_);
lean_closure_set(v___f_616_, 6, v_inst_604_);
lean_closure_set(v___f_616_, 7, v_inst_603_);
lean_closure_set(v___f_616_, 8, v_toBind_609_);
lean_closure_set(v___f_616_, 9, v___f_613_);
lean_closure_set(v___f_616_, 10, v___f_612_);
lean_closure_set(v___f_616_, 11, v___f_614_);
lean_closure_set(v___f_616_, 12, v___f_615_);
v___x_617_ = lean_apply_4(v_toBind_609_, lean_box(0), lean_box(0), v_getEnv_610_, v___f_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility(lean_object* v_m_618_, lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_vis_x3f_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_Elab_elabVisibility___redArg(v_inst_619_, v_inst_620_, v_inst_621_, v_inst_622_, v_inst_623_, v_inst_624_, v_vis_x3f_625_);
return v___x_626_;
}
}
lean_object* l_Lean_Elab_RecKind_ctorIdx___impl(uint8_t v_x_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_box(v_x_627_);
v___x_629_ = lean_obj_tag_nat(v___x_628_);
lean_dec(v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT void l_Lean_Elab_RecKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_627_ = stack[0].m_num;
lean_object* v_res_630_;
v_res_630_ = l_Lean_Elab_RecKind_ctorIdx___impl(v_x_627_);
stack->m_obj
 = v_res_630_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___impl___boxed(lean_object* v_x_631_){
_start:
{
uint8_t v_x_4__boxed_632_; lean_object* v_res_633_; 
v_x_4__boxed_632_ = lean_unbox(v_x_631_);
v_res_633_ = l_Lean_Elab_RecKind_ctorIdx___impl(v_x_4__boxed_632_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg(lean_object* v_k_634_){
_start:
{
lean_inc(v_k_634_);
return v_k_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg___boxed(lean_object* v_k_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Elab_RecKind_ctorElim___redArg(v_k_635_);
lean_dec(v_k_635_);
return v_res_636_;
}
}
lean_object* l_Lean_Elab_RecKind_ctorElim(lean_object* v_motive_637_, lean_object* v_ctorIdx_638_, uint8_t v_t_639_, lean_object* v_h_640_, lean_object* v_k_641_){
_start:
{
lean_inc(v_k_641_);
return v_k_641_;
}
}
LEAN_EXPORT void l_Lean_Elab_RecKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_638_ = stack[1].m_obj;
uint8_t v_t_639_ = stack[2].m_num;
lean_object* v_k_641_ = stack[4].m_obj;
lean_object* v_res_642_;
v_res_642_ = l_Lean_Elab_RecKind_ctorElim(lean_box(0), v_ctorIdx_638_, v_t_639_, lean_box(0), v_k_641_);
stack->m_obj
 = v_res_642_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___boxed(lean_object* v_motive_643_, lean_object* v_ctorIdx_644_, lean_object* v_t_645_, lean_object* v_h_646_, lean_object* v_k_647_){
_start:
{
uint8_t v_t_boxed_648_; lean_object* v_res_649_; 
v_t_boxed_648_ = lean_unbox(v_t_645_);
v_res_649_ = l_Lean_Elab_RecKind_ctorElim(v_motive_643_, v_ctorIdx_644_, v_t_boxed_648_, v_h_646_, v_k_647_);
lean_dec(v_k_647_);
lean_dec(v_ctorIdx_644_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg(lean_object* v_partial_650_){
_start:
{
lean_inc(v_partial_650_);
return v_partial_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg___boxed(lean_object* v_partial_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_Elab_RecKind_partial_elim___redArg(v_partial_651_);
lean_dec(v_partial_651_);
return v_res_652_;
}
}
lean_object* l_Lean_Elab_RecKind_partial_elim(lean_object* v_motive_653_, uint8_t v_t_654_, lean_object* v_h_655_, lean_object* v_partial_656_){
_start:
{
lean_inc(v_partial_656_);
return v_partial_656_;
}
}
LEAN_EXPORT void l_Lean_Elab_RecKind_partial_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_654_ = stack[1].m_num;
lean_object* v_partial_656_ = stack[3].m_obj;
lean_object* v_res_657_;
v_res_657_ = l_Lean_Elab_RecKind_partial_elim(lean_box(0), v_t_654_, lean_box(0), v_partial_656_);
stack->m_obj
 = v_res_657_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___boxed(lean_object* v_motive_658_, lean_object* v_t_659_, lean_object* v_h_660_, lean_object* v_partial_661_){
_start:
{
uint8_t v_t_boxed_662_; lean_object* v_res_663_; 
v_t_boxed_662_ = lean_unbox(v_t_659_);
v_res_663_ = l_Lean_Elab_RecKind_partial_elim(v_motive_658_, v_t_boxed_662_, v_h_660_, v_partial_661_);
lean_dec(v_partial_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg(lean_object* v_nonrec_664_){
_start:
{
lean_inc(v_nonrec_664_);
return v_nonrec_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg___boxed(lean_object* v_nonrec_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Elab_RecKind_nonrec_elim___redArg(v_nonrec_665_);
lean_dec(v_nonrec_665_);
return v_res_666_;
}
}
lean_object* l_Lean_Elab_RecKind_nonrec_elim(lean_object* v_motive_667_, uint8_t v_t_668_, lean_object* v_h_669_, lean_object* v_nonrec_670_){
_start:
{
lean_inc(v_nonrec_670_);
return v_nonrec_670_;
}
}
LEAN_EXPORT void l_Lean_Elab_RecKind_nonrec_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_668_ = stack[1].m_num;
lean_object* v_nonrec_670_ = stack[3].m_obj;
lean_object* v_res_671_;
v_res_671_ = l_Lean_Elab_RecKind_nonrec_elim(lean_box(0), v_t_668_, lean_box(0), v_nonrec_670_);
stack->m_obj
 = v_res_671_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___boxed(lean_object* v_motive_672_, lean_object* v_t_673_, lean_object* v_h_674_, lean_object* v_nonrec_675_){
_start:
{
uint8_t v_t_boxed_676_; lean_object* v_res_677_; 
v_t_boxed_676_ = lean_unbox(v_t_673_);
v_res_677_ = l_Lean_Elab_RecKind_nonrec_elim(v_motive_672_, v_t_boxed_676_, v_h_674_, v_nonrec_675_);
lean_dec(v_nonrec_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg(lean_object* v_default_678_){
_start:
{
lean_inc(v_default_678_);
return v_default_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg___boxed(lean_object* v_default_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Elab_RecKind_default_elim___redArg(v_default_679_);
lean_dec(v_default_679_);
return v_res_680_;
}
}
lean_object* l_Lean_Elab_RecKind_default_elim(lean_object* v_motive_681_, uint8_t v_t_682_, lean_object* v_h_683_, lean_object* v_default_684_){
_start:
{
lean_inc(v_default_684_);
return v_default_684_;
}
}
LEAN_EXPORT void l_Lean_Elab_RecKind_default_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_682_ = stack[1].m_num;
lean_object* v_default_684_ = stack[3].m_obj;
lean_object* v_res_685_;
v_res_685_ = l_Lean_Elab_RecKind_default_elim(lean_box(0), v_t_682_, lean_box(0), v_default_684_);
stack->m_obj
 = v_res_685_;
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
lean_object* l_Lean_Elab_ComputeKind_ctorIdx___impl(uint8_t v_x_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_box(v_x_694_);
v___x_696_ = lean_obj_tag_nat(v___x_695_);
lean_dec(v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT void l_Lean_Elab_ComputeKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_694_ = stack[0].m_num;
lean_object* v_res_697_;
v_res_697_ = l_Lean_Elab_ComputeKind_ctorIdx___impl(v_x_694_);
stack->m_obj
 = v_res_697_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___impl___boxed(lean_object* v_x_698_){
_start:
{
uint8_t v_x_4__boxed_699_; lean_object* v_res_700_; 
v_x_4__boxed_699_ = lean_unbox(v_x_698_);
v_res_700_ = l_Lean_Elab_ComputeKind_ctorIdx___impl(v_x_4__boxed_699_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg(lean_object* v_k_701_){
_start:
{
lean_inc(v_k_701_);
return v_k_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg___boxed(lean_object* v_k_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Elab_ComputeKind_ctorElim___redArg(v_k_702_);
lean_dec(v_k_702_);
return v_res_703_;
}
}
lean_object* l_Lean_Elab_ComputeKind_ctorElim(lean_object* v_motive_704_, lean_object* v_ctorIdx_705_, uint8_t v_t_706_, lean_object* v_h_707_, lean_object* v_k_708_){
_start:
{
lean_inc(v_k_708_);
return v_k_708_;
}
}
LEAN_EXPORT void l_Lean_Elab_ComputeKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_705_ = stack[1].m_obj;
uint8_t v_t_706_ = stack[2].m_num;
lean_object* v_k_708_ = stack[4].m_obj;
lean_object* v_res_709_;
v_res_709_ = l_Lean_Elab_ComputeKind_ctorElim(lean_box(0), v_ctorIdx_705_, v_t_706_, lean_box(0), v_k_708_);
stack->m_obj
 = v_res_709_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___boxed(lean_object* v_motive_710_, lean_object* v_ctorIdx_711_, lean_object* v_t_712_, lean_object* v_h_713_, lean_object* v_k_714_){
_start:
{
uint8_t v_t_boxed_715_; lean_object* v_res_716_; 
v_t_boxed_715_ = lean_unbox(v_t_712_);
v_res_716_ = l_Lean_Elab_ComputeKind_ctorElim(v_motive_710_, v_ctorIdx_711_, v_t_boxed_715_, v_h_713_, v_k_714_);
lean_dec(v_k_714_);
lean_dec(v_ctorIdx_711_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg(lean_object* v_regular_717_){
_start:
{
lean_inc(v_regular_717_);
return v_regular_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg___boxed(lean_object* v_regular_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Elab_ComputeKind_regular_elim___redArg(v_regular_718_);
lean_dec(v_regular_718_);
return v_res_719_;
}
}
lean_object* l_Lean_Elab_ComputeKind_regular_elim(lean_object* v_motive_720_, uint8_t v_t_721_, lean_object* v_h_722_, lean_object* v_regular_723_){
_start:
{
lean_inc(v_regular_723_);
return v_regular_723_;
}
}
LEAN_EXPORT void l_Lean_Elab_ComputeKind_regular_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_721_ = stack[1].m_num;
lean_object* v_regular_723_ = stack[3].m_obj;
lean_object* v_res_724_;
v_res_724_ = l_Lean_Elab_ComputeKind_regular_elim(lean_box(0), v_t_721_, lean_box(0), v_regular_723_);
stack->m_obj
 = v_res_724_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___boxed(lean_object* v_motive_725_, lean_object* v_t_726_, lean_object* v_h_727_, lean_object* v_regular_728_){
_start:
{
uint8_t v_t_boxed_729_; lean_object* v_res_730_; 
v_t_boxed_729_ = lean_unbox(v_t_726_);
v_res_730_ = l_Lean_Elab_ComputeKind_regular_elim(v_motive_725_, v_t_boxed_729_, v_h_727_, v_regular_728_);
lean_dec(v_regular_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg(lean_object* v_meta_731_){
_start:
{
lean_inc(v_meta_731_);
return v_meta_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg___boxed(lean_object* v_meta_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Elab_ComputeKind_meta_elim___redArg(v_meta_732_);
lean_dec(v_meta_732_);
return v_res_733_;
}
}
lean_object* l_Lean_Elab_ComputeKind_meta_elim(lean_object* v_motive_734_, uint8_t v_t_735_, lean_object* v_h_736_, lean_object* v_meta_737_){
_start:
{
lean_inc(v_meta_737_);
return v_meta_737_;
}
}
LEAN_EXPORT void l_Lean_Elab_ComputeKind_meta_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_735_ = stack[1].m_num;
lean_object* v_meta_737_ = stack[3].m_obj;
lean_object* v_res_738_;
v_res_738_ = l_Lean_Elab_ComputeKind_meta_elim(lean_box(0), v_t_735_, lean_box(0), v_meta_737_);
stack->m_obj
 = v_res_738_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___boxed(lean_object* v_motive_739_, lean_object* v_t_740_, lean_object* v_h_741_, lean_object* v_meta_742_){
_start:
{
uint8_t v_t_boxed_743_; lean_object* v_res_744_; 
v_t_boxed_743_ = lean_unbox(v_t_740_);
v_res_744_ = l_Lean_Elab_ComputeKind_meta_elim(v_motive_739_, v_t_boxed_743_, v_h_741_, v_meta_742_);
lean_dec(v_meta_742_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(lean_object* v_noncomputable_745_){
_start:
{
lean_inc(v_noncomputable_745_);
return v_noncomputable_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg___boxed(lean_object* v_noncomputable_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(v_noncomputable_746_);
lean_dec(v_noncomputable_746_);
return v_res_747_;
}
}
lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim(lean_object* v_motive_748_, uint8_t v_t_749_, lean_object* v_h_750_, lean_object* v_noncomputable_751_){
_start:
{
lean_inc(v_noncomputable_751_);
return v_noncomputable_751_;
}
}
LEAN_EXPORT void l_Lean_Elab_ComputeKind_noncomputable_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_749_ = stack[1].m_num;
lean_object* v_noncomputable_751_ = stack[3].m_obj;
lean_object* v_res_752_;
v_res_752_ = l_Lean_Elab_ComputeKind_noncomputable_elim(lean_box(0), v_t_749_, lean_box(0), v_noncomputable_751_);
stack->m_obj
 = v_res_752_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___boxed(lean_object* v_motive_753_, lean_object* v_t_754_, lean_object* v_h_755_, lean_object* v_noncomputable_756_){
_start:
{
uint8_t v_t_boxed_757_; lean_object* v_res_758_; 
v_t_boxed_757_ = lean_unbox(v_t_754_);
v_res_758_ = l_Lean_Elab_ComputeKind_noncomputable_elim(v_motive_753_, v_t_boxed_757_, v_h_755_, v_noncomputable_756_);
lean_dec(v_noncomputable_756_);
return v_res_758_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind_default(void){
_start:
{
uint8_t v___x_759_; 
v___x_759_ = 0;
return v___x_759_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind(void){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = 0;
return v___x_760_;
}
}
uint8_t l_Lean_Elab_instBEqComputeKind_beq(uint8_t v_x_761_, uint8_t v_y_762_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_763_ = lean_box(v_x_761_);
v___x_764_ = lean_obj_tag_nat(v___x_763_);
lean_dec(v___x_763_);
v___x_765_ = lean_box(v_y_762_);
v___x_766_ = lean_obj_tag_nat(v___x_765_);
lean_dec(v___x_765_);
v___x_767_ = lean_nat_dec_eq(v___x_764_, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT void l_Lean_Elab_instBEqComputeKind_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_761_ = stack[0].m_num;
uint8_t v_y_762_ = stack[1].m_num;
uint8_t v_res_768_;
v_res_768_ = l_Lean_Elab_instBEqComputeKind_beq(v_x_761_, v_y_762_);
stack->m_num = v_res_768_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqComputeKind_beq___boxed(lean_object* v_x_769_, lean_object* v_y_770_){
_start:
{
uint8_t v_x_24__boxed_771_; uint8_t v_y_25__boxed_772_; uint8_t v_res_773_; lean_object* v_r_774_; 
v_x_24__boxed_771_ = lean_unbox(v_x_769_);
v_y_25__boxed_772_ = lean_unbox(v_y_770_);
v_res_773_ = l_Lean_Elab_instBEqComputeKind_beq(v_x_24__boxed_771_, v_y_25__boxed_772_);
v_r_774_ = lean_box(v_res_773_);
return v_r_774_;
}
}
static lean_object* _init_l_Lean_Elab_instReprComputeKind_repr___closed__6(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_unsigned_to_nat(2u);
v___x_787_ = lean_nat_to_int(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_Elab_instReprComputeKind_repr___closed__7(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_unsigned_to_nat(1u);
v___x_789_ = lean_nat_to_int(v___x_788_);
return v___x_789_;
}
}
lean_object* l_Lean_Elab_instReprComputeKind_repr(uint8_t v_x_790_, lean_object* v_prec_791_){
_start:
{
lean_object* v___y_793_; lean_object* v___y_800_; lean_object* v___y_807_; 
switch(v_x_790_)
{
case 0:
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = lean_unsigned_to_nat(1024u);
v___x_814_ = lean_nat_dec_le(v___x_813_, v_prec_791_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; 
v___x_815_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_793_ = v___x_815_;
goto v___jp_792_;
}
else
{
lean_object* v___x_816_; 
v___x_816_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_793_ = v___x_816_;
goto v___jp_792_;
}
}
case 1:
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = lean_unsigned_to_nat(1024u);
v___x_818_ = lean_nat_dec_le(v___x_817_, v_prec_791_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; 
v___x_819_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_800_ = v___x_819_;
goto v___jp_799_;
}
else
{
lean_object* v___x_820_; 
v___x_820_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_800_ = v___x_820_;
goto v___jp_799_;
}
}
default: 
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(1024u);
v___x_822_ = lean_nat_dec_le(v___x_821_, v_prec_791_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; 
v___x_823_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_807_ = v___x_823_;
goto v___jp_806_;
}
else
{
lean_object* v___x_824_; 
v___x_824_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_807_ = v___x_824_;
goto v___jp_806_;
}
}
}
v___jp_792_:
{
lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_794_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__1));
lean_inc(v___y_793_);
v___x_795_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_795_, 0, v___y_793_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = 0;
v___x_797_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*1, v___x_796_);
v___x_798_ = l_Repr_addAppParen(v___x_797_, v_prec_791_);
return v___x_798_;
}
v___jp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_801_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__3));
lean_inc(v___y_800_);
v___x_802_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_802_, 0, v___y_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = 0;
v___x_804_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*1, v___x_803_);
v___x_805_ = l_Repr_addAppParen(v___x_804_, v_prec_791_);
return v___x_805_;
}
v___jp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_808_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__5));
lean_inc(v___y_807_);
v___x_809_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_809_, 0, v___y_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = 0;
v___x_811_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*1, v___x_810_);
v___x_812_ = l_Repr_addAppParen(v___x_811_, v_prec_791_);
return v___x_812_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_instReprComputeKind_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_790_ = stack[0].m_num;
lean_object* v_prec_791_ = stack[1].m_obj;
lean_object* v_res_825_;
v_res_825_ = l_Lean_Elab_instReprComputeKind_repr(v_x_790_, v_prec_791_);
stack->m_obj
 = v_res_825_;
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
uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object* v_m_844_){
_start:
{
uint8_t v_visibility_845_; uint8_t v___x_846_; 
v_visibility_845_ = lean_ctor_get_uint8(v_m_844_, sizeof(void*)*3);
v___x_846_ = l_Lean_Elab_Visibility_isPrivate(v_visibility_845_);
return v___x_846_;
}
}
LEAN_EXPORT void l_Lean_Elab_Modifiers_isPrivate_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_844_ = stack[0].m_obj;
uint8_t v_res_847_;
v_res_847_ = l_Lean_Elab_Modifiers_isPrivate(v_m_844_);
stack->m_num = v_res_847_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPrivate___boxed(lean_object* v_m_848_){
_start:
{
uint8_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l_Lean_Elab_Modifiers_isPrivate(v_m_848_);
lean_dec_ref(v_m_848_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
uint8_t l_Lean_Elab_Modifiers_isPublic(lean_object* v_m_851_){
_start:
{
uint8_t v_visibility_852_; uint8_t v___x_853_; 
v_visibility_852_ = lean_ctor_get_uint8(v_m_851_, sizeof(void*)*3);
v___x_853_ = l_Lean_Elab_Visibility_isPublic(v_visibility_852_);
return v___x_853_;
}
}
LEAN_EXPORT void l_Lean_Elab_Modifiers_isPublic_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_851_ = stack[0].m_obj;
uint8_t v_res_854_;
v_res_854_ = l_Lean_Elab_Modifiers_isPublic(v_m_851_);
stack->m_num = v_res_854_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPublic___boxed(lean_object* v_m_855_){
_start:
{
uint8_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l_Lean_Elab_Modifiers_isPublic(v_m_855_);
lean_dec_ref(v_m_855_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
uint8_t l_Lean_Elab_Modifiers_isInferredPublic(lean_object* v_env_858_, lean_object* v_m_859_){
_start:
{
uint8_t v_visibility_860_; uint8_t v___x_861_; 
v_visibility_860_ = lean_ctor_get_uint8(v_m_859_, sizeof(void*)*3);
v___x_861_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_858_, v_visibility_860_);
return v___x_861_;
}
}
LEAN_EXPORT void l_Lean_Elab_Modifiers_isInferredPublic_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_858_ = stack[0].m_obj;
lean_object* v_m_859_ = stack[1].m_obj;
uint8_t v_res_862_;
v_res_862_ = l_Lean_Elab_Modifiers_isInferredPublic(v_env_858_, v_m_859_);
stack->m_num = v_res_862_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isInferredPublic___boxed(lean_object* v_env_863_, lean_object* v_m_864_){
_start:
{
uint8_t v_res_865_; lean_object* v_r_866_; 
v_res_865_ = l_Lean_Elab_Modifiers_isInferredPublic(v_env_863_, v_m_864_);
lean_dec_ref(v_m_864_);
lean_dec_ref(v_env_863_);
v_r_866_ = lean_box(v_res_865_);
return v_r_866_;
}
}
uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object* v_x_867_){
_start:
{
uint8_t v_recKind_868_; 
v_recKind_868_ = lean_ctor_get_uint8(v_x_867_, sizeof(void*)*3 + 3);
if (v_recKind_868_ == 0)
{
uint8_t v___x_869_; 
v___x_869_ = 1;
return v___x_869_;
}
else
{
uint8_t v___x_870_; 
v___x_870_ = 0;
return v___x_870_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Modifiers_isPartial_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_867_ = stack[0].m_obj;
uint8_t v_res_871_;
v_res_871_ = l_Lean_Elab_Modifiers_isPartial(v_x_867_);
stack->m_num = v_res_871_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPartial___boxed(lean_object* v_x_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l_Lean_Elab_Modifiers_isPartial(v_x_872_);
lean_dec_ref(v_x_872_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
uint8_t l_Lean_Elab_Modifiers_isNonrec(lean_object* v_x_875_){
_start:
{
uint8_t v_recKind_876_; 
v_recKind_876_ = lean_ctor_get_uint8(v_x_875_, sizeof(void*)*3 + 3);
if (v_recKind_876_ == 1)
{
uint8_t v___x_877_; 
v___x_877_ = 1;
return v___x_877_;
}
else
{
uint8_t v___x_878_; 
v___x_878_ = 0;
return v___x_878_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Modifiers_isNonrec_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_875_ = stack[0].m_obj;
uint8_t v_res_879_;
v_res_879_ = l_Lean_Elab_Modifiers_isNonrec(v_x_875_);
stack->m_num = v_res_879_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNonrec___boxed(lean_object* v_x_880_){
_start:
{
uint8_t v_res_881_; lean_object* v_r_882_; 
v_res_881_ = l_Lean_Elab_Modifiers_isNonrec(v_x_880_);
lean_dec_ref(v_x_880_);
v_r_882_ = lean_box(v_res_881_);
return v_r_882_;
}
}
uint8_t l_Lean_Elab_Modifiers_isMeta(lean_object* v_m_883_){
_start:
{
uint8_t v_computeKind_884_; 
v_computeKind_884_ = lean_ctor_get_uint8(v_m_883_, sizeof(void*)*3 + 2);
if (v_computeKind_884_ == 1)
{
uint8_t v___x_885_; 
v___x_885_ = 1;
return v___x_885_;
}
else
{
uint8_t v___x_886_; 
v___x_886_ = 0;
return v___x_886_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Modifiers_isMeta_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_883_ = stack[0].m_obj;
uint8_t v_res_887_;
v_res_887_ = l_Lean_Elab_Modifiers_isMeta(v_m_883_);
stack->m_num = v_res_887_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isMeta___boxed(lean_object* v_m_888_){
_start:
{
uint8_t v_res_889_; lean_object* v_r_890_; 
v_res_889_ = l_Lean_Elab_Modifiers_isMeta(v_m_888_);
lean_dec_ref(v_m_888_);
v_r_890_ = lean_box(v_res_889_);
return v_r_890_;
}
}
uint8_t l_Lean_Elab_Modifiers_isNoncomputable(lean_object* v_m_891_){
_start:
{
uint8_t v_computeKind_892_; 
v_computeKind_892_ = lean_ctor_get_uint8(v_m_891_, sizeof(void*)*3 + 2);
if (v_computeKind_892_ == 2)
{
uint8_t v___x_893_; 
v___x_893_ = 1;
return v___x_893_;
}
else
{
uint8_t v___x_894_; 
v___x_894_ = 0;
return v___x_894_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Modifiers_isNoncomputable_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_891_ = stack[0].m_obj;
uint8_t v_res_895_;
v_res_895_ = l_Lean_Elab_Modifiers_isNoncomputable(v_m_891_);
stack->m_num = v_res_895_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNoncomputable___boxed(lean_object* v_m_896_){
_start:
{
uint8_t v_res_897_; lean_object* v_r_898_; 
v_res_897_ = l_Lean_Elab_Modifiers_isNoncomputable(v_m_896_);
lean_dec_ref(v_m_896_);
v_r_898_ = lean_box(v_res_897_);
return v_r_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addAttr(lean_object* v_modifiers_899_, lean_object* v_attr_900_){
_start:
{
lean_object* v_stx_901_; lean_object* v_docString_x3f_902_; uint8_t v_visibility_903_; uint8_t v_isProtected_904_; uint8_t v_computeKind_905_; uint8_t v_recKind_906_; uint8_t v_isUnsafe_907_; lean_object* v_attrs_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_916_; 
v_stx_901_ = lean_ctor_get(v_modifiers_899_, 0);
v_docString_x3f_902_ = lean_ctor_get(v_modifiers_899_, 1);
v_visibility_903_ = lean_ctor_get_uint8(v_modifiers_899_, sizeof(void*)*3);
v_isProtected_904_ = lean_ctor_get_uint8(v_modifiers_899_, sizeof(void*)*3 + 1);
v_computeKind_905_ = lean_ctor_get_uint8(v_modifiers_899_, sizeof(void*)*3 + 2);
v_recKind_906_ = lean_ctor_get_uint8(v_modifiers_899_, sizeof(void*)*3 + 3);
v_isUnsafe_907_ = lean_ctor_get_uint8(v_modifiers_899_, sizeof(void*)*3 + 4);
v_attrs_908_ = lean_ctor_get(v_modifiers_899_, 2);
v_isSharedCheck_916_ = !lean_is_exclusive(v_modifiers_899_);
if (v_isSharedCheck_916_ == 0)
{
v___x_910_ = v_modifiers_899_;
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_attrs_908_);
lean_inc(v_docString_x3f_902_);
lean_inc(v_stx_901_);
lean_dec(v_modifiers_899_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = lean_array_push(v_attrs_908_, v_attr_900_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 2, v___x_912_);
v___x_914_ = v___x_910_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_stx_901_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_docString_x3f_902_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v___x_912_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*3, v_visibility_903_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*3 + 1, v_isProtected_904_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*3 + 2, v_computeKind_905_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*3 + 3, v_recKind_906_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*3 + 4, v_isUnsafe_907_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addFirstAttr(lean_object* v_modifiers_917_, lean_object* v_attr_918_){
_start:
{
lean_object* v_stx_919_; lean_object* v_docString_x3f_920_; uint8_t v_visibility_921_; uint8_t v_isProtected_922_; uint8_t v_computeKind_923_; uint8_t v_recKind_924_; uint8_t v_isUnsafe_925_; lean_object* v_attrs_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_937_; 
v_stx_919_ = lean_ctor_get(v_modifiers_917_, 0);
v_docString_x3f_920_ = lean_ctor_get(v_modifiers_917_, 1);
v_visibility_921_ = lean_ctor_get_uint8(v_modifiers_917_, sizeof(void*)*3);
v_isProtected_922_ = lean_ctor_get_uint8(v_modifiers_917_, sizeof(void*)*3 + 1);
v_computeKind_923_ = lean_ctor_get_uint8(v_modifiers_917_, sizeof(void*)*3 + 2);
v_recKind_924_ = lean_ctor_get_uint8(v_modifiers_917_, sizeof(void*)*3 + 3);
v_isUnsafe_925_ = lean_ctor_get_uint8(v_modifiers_917_, sizeof(void*)*3 + 4);
v_attrs_926_ = lean_ctor_get(v_modifiers_917_, 2);
v_isSharedCheck_937_ = !lean_is_exclusive(v_modifiers_917_);
if (v_isSharedCheck_937_ == 0)
{
v___x_928_ = v_modifiers_917_;
v_isShared_929_ = v_isSharedCheck_937_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_attrs_926_);
lean_inc(v_docString_x3f_920_);
lean_inc(v_stx_919_);
lean_dec(v_modifiers_917_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_937_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_930_ = lean_unsigned_to_nat(1u);
v___x_931_ = lean_mk_empty_array_with_capacity(v___x_930_);
v___x_932_ = lean_array_push(v___x_931_, v_attr_918_);
v___x_933_ = l_Array_append___redArg(v___x_932_, v_attrs_926_);
lean_dec_ref(v_attrs_926_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 2, v___x_933_);
v___x_935_ = v___x_928_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_stx_919_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_docString_x3f_920_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v___x_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*3, v_visibility_921_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*3 + 1, v_isProtected_922_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*3 + 2, v_computeKind_923_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*3 + 3, v_recKind_924_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*3 + 4, v_isUnsafe_925_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(lean_object* v_p_938_, lean_object* v_as_939_, size_t v_i_940_, size_t v_stop_941_, lean_object* v_b_942_){
_start:
{
lean_object* v___y_944_; uint8_t v___x_948_; 
v___x_948_ = lean_usize_dec_eq(v_i_940_, v_stop_941_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_949_ = lean_array_uget_borrowed(v_as_939_, v_i_940_);
lean_inc_ref(v_p_938_);
lean_inc(v___x_949_);
v___x_950_ = lean_apply_1(v_p_938_, v___x_949_);
v___x_951_ = lean_unbox(v___x_950_);
if (v___x_951_ == 0)
{
v___y_944_ = v_b_942_;
goto v___jp_943_;
}
else
{
lean_object* v___x_952_; 
lean_inc(v___x_949_);
v___x_952_ = lean_array_push(v_b_942_, v___x_949_);
v___y_944_ = v___x_952_;
goto v___jp_943_;
}
}
else
{
lean_dec_ref(v_p_938_);
return v_b_942_;
}
v___jp_943_:
{
size_t v___x_945_; size_t v___x_946_; 
v___x_945_ = ((size_t)1ULL);
v___x_946_ = lean_usize_add(v_i_940_, v___x_945_);
v_i_940_ = v___x_946_;
v_b_942_ = v___y_944_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_938_ = stack[0].m_obj;
lean_object* v_as_939_ = stack[1].m_obj;
size_t v_i_940_ = stack[2].m_num;
size_t v_stop_941_ = stack[3].m_num;
lean_object* v_b_942_ = stack[4].m_obj;
lean_object* v_res_953_;
v_res_953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_938_, v_as_939_, v_i_940_, v_stop_941_, v_b_942_);
stack->m_obj
 = v_res_953_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0___boxed(lean_object* v_p_954_, lean_object* v_as_955_, lean_object* v_i_956_, lean_object* v_stop_957_, lean_object* v_b_958_){
_start:
{
size_t v_i_boxed_959_; size_t v_stop_boxed_960_; lean_object* v_res_961_; 
v_i_boxed_959_ = lean_unbox_usize(v_i_956_);
lean_dec(v_i_956_);
v_stop_boxed_960_ = lean_unbox_usize(v_stop_957_);
lean_dec(v_stop_957_);
v_res_961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_954_, v_as_955_, v_i_boxed_959_, v_stop_boxed_960_, v_b_958_);
lean_dec_ref(v_as_955_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object* v_modifiers_962_, lean_object* v_p_963_){
_start:
{
lean_object* v_stx_964_; lean_object* v_docString_x3f_965_; uint8_t v_visibility_966_; uint8_t v_isProtected_967_; uint8_t v_computeKind_968_; uint8_t v_recKind_969_; uint8_t v_isUnsafe_970_; lean_object* v_attrs_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_998_; 
v_stx_964_ = lean_ctor_get(v_modifiers_962_, 0);
v_docString_x3f_965_ = lean_ctor_get(v_modifiers_962_, 1);
v_visibility_966_ = lean_ctor_get_uint8(v_modifiers_962_, sizeof(void*)*3);
v_isProtected_967_ = lean_ctor_get_uint8(v_modifiers_962_, sizeof(void*)*3 + 1);
v_computeKind_968_ = lean_ctor_get_uint8(v_modifiers_962_, sizeof(void*)*3 + 2);
v_recKind_969_ = lean_ctor_get_uint8(v_modifiers_962_, sizeof(void*)*3 + 3);
v_isUnsafe_970_ = lean_ctor_get_uint8(v_modifiers_962_, sizeof(void*)*3 + 4);
v_attrs_971_ = lean_ctor_get(v_modifiers_962_, 2);
v_isSharedCheck_998_ = !lean_is_exclusive(v_modifiers_962_);
if (v_isSharedCheck_998_ == 0)
{
v___x_973_ = v_modifiers_962_;
v_isShared_974_ = v_isSharedCheck_998_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_attrs_971_);
lean_inc(v_docString_x3f_965_);
lean_inc(v_stx_964_);
lean_dec(v_modifiers_962_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_998_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = lean_array_get_size(v_attrs_971_);
v___x_977_ = ((lean_object*)(l_Lean_Elab_instInhabitedModifiers_default___closed__0));
v___x_978_ = lean_nat_dec_lt(v___x_975_, v___x_976_);
if (v___x_978_ == 0)
{
lean_object* v___x_980_; 
lean_dec_ref(v_attrs_971_);
lean_dec_ref(v_p_963_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 2, v___x_977_);
v___x_980_ = v___x_973_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_stx_964_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_docString_x3f_965_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v___x_977_);
lean_ctor_set_uint8(v_reuseFailAlloc_981_, sizeof(void*)*3, v_visibility_966_);
lean_ctor_set_uint8(v_reuseFailAlloc_981_, sizeof(void*)*3 + 1, v_isProtected_967_);
lean_ctor_set_uint8(v_reuseFailAlloc_981_, sizeof(void*)*3 + 2, v_computeKind_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_981_, sizeof(void*)*3 + 3, v_recKind_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_981_, sizeof(void*)*3 + 4, v_isUnsafe_970_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
else
{
uint8_t v___x_982_; 
v___x_982_ = lean_nat_dec_le(v___x_976_, v___x_976_);
if (v___x_982_ == 0)
{
if (v___x_978_ == 0)
{
lean_object* v___x_984_; 
lean_dec_ref(v_attrs_971_);
lean_dec_ref(v_p_963_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 2, v___x_977_);
v___x_984_ = v___x_973_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_stx_964_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_docString_x3f_965_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v___x_977_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*3, v_visibility_966_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*3 + 1, v_isProtected_967_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*3 + 2, v_computeKind_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*3 + 3, v_recKind_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*3 + 4, v_isUnsafe_970_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
else
{
size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_986_ = ((size_t)0ULL);
v___x_987_ = lean_usize_of_nat(v___x_976_);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_963_, v_attrs_971_, v___x_986_, v___x_987_, v___x_977_);
lean_dec_ref(v_attrs_971_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 2, v___x_988_);
v___x_990_ = v___x_973_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_stx_964_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_docString_x3f_965_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v___x_988_);
lean_ctor_set_uint8(v_reuseFailAlloc_991_, sizeof(void*)*3, v_visibility_966_);
lean_ctor_set_uint8(v_reuseFailAlloc_991_, sizeof(void*)*3 + 1, v_isProtected_967_);
lean_ctor_set_uint8(v_reuseFailAlloc_991_, sizeof(void*)*3 + 2, v_computeKind_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_991_, sizeof(void*)*3 + 3, v_recKind_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_991_, sizeof(void*)*3 + 4, v_isUnsafe_970_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
else
{
size_t v___x_992_; size_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_992_ = ((size_t)0ULL);
v___x_993_ = lean_usize_of_nat(v___x_976_);
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_963_, v_attrs_971_, v___x_992_, v___x_993_, v___x_977_);
lean_dec_ref(v_attrs_971_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 2, v___x_994_);
v___x_996_ = v___x_973_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_stx_964_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_docString_x3f_965_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v___x_994_);
lean_ctor_set_uint8(v_reuseFailAlloc_997_, sizeof(void*)*3, v_visibility_966_);
lean_ctor_set_uint8(v_reuseFailAlloc_997_, sizeof(void*)*3 + 1, v_isProtected_967_);
lean_ctor_set_uint8(v_reuseFailAlloc_997_, sizeof(void*)*3 + 2, v_computeKind_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_997_, sizeof(void*)*3 + 3, v_recKind_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_997_, sizeof(void*)*3 + 4, v_isUnsafe_970_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(lean_object* v_p_999_, lean_object* v_as_1000_, size_t v_i_1001_, size_t v_stop_1002_){
_start:
{
uint8_t v___x_1003_; 
v___x_1003_ = lean_usize_dec_eq(v_i_1001_, v_stop_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1004_ = lean_array_uget_borrowed(v_as_1000_, v_i_1001_);
lean_inc_ref(v_p_999_);
lean_inc(v___x_1004_);
v___x_1005_ = lean_apply_1(v_p_999_, v___x_1004_);
v___x_1006_ = lean_unbox(v___x_1005_);
if (v___x_1006_ == 0)
{
size_t v___x_1007_; size_t v___x_1008_; 
v___x_1007_ = ((size_t)1ULL);
v___x_1008_ = lean_usize_add(v_i_1001_, v___x_1007_);
v_i_1001_ = v___x_1008_;
goto _start;
}
else
{
uint8_t v___x_1010_; 
lean_dec_ref(v_p_999_);
v___x_1010_ = lean_unbox(v___x_1005_);
return v___x_1010_;
}
}
else
{
uint8_t v___x_1011_; 
lean_dec_ref(v_p_999_);
v___x_1011_ = 0;
return v___x_1011_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_999_ = stack[0].m_obj;
lean_object* v_as_1000_ = stack[1].m_obj;
size_t v_i_1001_ = stack[2].m_num;
size_t v_stop_1002_ = stack[3].m_num;
uint8_t v_res_1012_;
v_res_1012_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_999_, v_as_1000_, v_i_1001_, v_stop_1002_);
stack->m_num = v_res_1012_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0___boxed(lean_object* v_p_1013_, lean_object* v_as_1014_, lean_object* v_i_1015_, lean_object* v_stop_1016_){
_start:
{
size_t v_i_boxed_1017_; size_t v_stop_boxed_1018_; uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_i_boxed_1017_ = lean_unbox_usize(v_i_1015_);
lean_dec(v_i_1015_);
v_stop_boxed_1018_ = lean_unbox_usize(v_stop_1016_);
lean_dec(v_stop_1016_);
v_res_1019_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_1013_, v_as_1014_, v_i_boxed_1017_, v_stop_boxed_1018_);
lean_dec_ref(v_as_1014_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
uint8_t l_Lean_Elab_Modifiers_anyAttr(lean_object* v_modifiers_1021_, lean_object* v_p_1022_){
_start:
{
lean_object* v_attrs_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_attrs_1023_ = lean_ctor_get(v_modifiers_1021_, 2);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_array_get_size(v_attrs_1023_);
v___x_1026_ = lean_nat_dec_lt(v___x_1024_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_dec_ref(v_p_1022_);
return v___x_1026_;
}
else
{
if (v___x_1026_ == 0)
{
lean_dec_ref(v_p_1022_);
return v___x_1026_;
}
else
{
size_t v___x_1027_; size_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1027_ = ((size_t)0ULL);
v___x_1028_ = lean_usize_of_nat(v___x_1025_);
v___x_1029_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_1022_, v_attrs_1023_, v___x_1027_, v___x_1028_);
return v___x_1029_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Modifiers_anyAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_modifiers_1021_ = stack[0].m_obj;
lean_object* v_p_1022_ = stack[1].m_obj;
uint8_t v_res_1030_;
v_res_1030_ = l_Lean_Elab_Modifiers_anyAttr(v_modifiers_1021_, v_p_1022_);
stack->m_num = v_res_1030_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_anyAttr___boxed(lean_object* v_modifiers_1031_, lean_object* v_p_1032_){
_start:
{
uint8_t v_res_1033_; lean_object* v_r_1034_; 
v_res_1033_ = l_Lean_Elab_Modifiers_anyAttr(v_modifiers_1031_, v_p_1032_);
lean_dec_ref(v_modifiers_1031_);
v_r_1034_ = lean_box(v_res_1033_);
return v_r_1034_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__0));
v___x_1038_ = lean_string_length(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__2, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__2_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2);
v___x_1040_ = lean_nat_to_int(v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__0(lean_object* v_attr_1047_){
_start:
{
uint8_t v_kind_1048_; lean_object* v_name_1049_; lean_object* v_stx_1050_; lean_object* v___y_1052_; 
v_kind_1048_ = lean_ctor_get_uint8(v_attr_1047_, sizeof(void*)*2);
v_name_1049_ = lean_ctor_get(v_attr_1047_, 0);
lean_inc(v_name_1049_);
v_stx_1050_ = lean_ctor_get(v_attr_1047_, 1);
lean_inc(v_stx_1050_);
lean_dec_ref(v_attr_1047_);
switch(v_kind_1048_)
{
case 0:
{
lean_object* v___x_1074_; 
v___x_1074_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4));
v___y_1052_ = v___x_1074_;
goto v___jp_1051_;
}
case 1:
{
lean_object* v___x_1075_; 
v___x_1075_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__6));
v___y_1052_ = v___x_1075_;
goto v___jp_1051_;
}
default: 
{
lean_object* v___x_1076_; 
v___x_1076_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__7));
v___y_1052_ = v___x_1076_;
goto v___jp_1051_;
}
}
v___jp_1051_:
{
lean_object* v___x_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; lean_object* v___x_1073_; 
lean_inc_ref(v___y_1052_);
v___x_1053_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___y_1052_);
v___x_1054_ = 1;
v___x_1055_ = l_Lean_Name_toString(v_name_1049_, v___x_1054_);
v___x_1056_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1053_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_box(0);
v___x_1059_ = 0;
v___x_1060_ = l_Lean_Syntax_formatStx(v_stx_1050_, v___x_1058_, v___x_1059_);
v___x_1061_ = l_Std_Format_defWidth;
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = l_Std_Format_pretty(v___x_1060_, v___x_1061_, v___x_1062_, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1057_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__3, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__3_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3);
v___x_1067_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__4));
v___x_1068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v___x_1065_);
v___x_1069_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__5));
v___x_1070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1066_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = 0;
v___x_1073_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*1, v___x_1072_);
return v___x_1073_;
}
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__0));
v___x_1086_ = lean_string_length(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__5, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__5_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5);
v___x_1088_ = lean_nat_to_int(v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__1(lean_object* v___f_1145_, lean_object* v___f_1146_, lean_object* v_m_1147_){
_start:
{
lean_object* v_docString_x3f_1148_; uint8_t v_visibility_1149_; uint8_t v_isProtected_1150_; uint8_t v_computeKind_1151_; uint8_t v_recKind_1152_; uint8_t v_isUnsafe_1153_; lean_object* v_attrs_1154_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1200_; 
v_docString_x3f_1148_ = lean_ctor_get(v_m_1147_, 1);
lean_inc(v_docString_x3f_1148_);
v_visibility_1149_ = lean_ctor_get_uint8(v_m_1147_, sizeof(void*)*3);
v_isProtected_1150_ = lean_ctor_get_uint8(v_m_1147_, sizeof(void*)*3 + 1);
v_computeKind_1151_ = lean_ctor_get_uint8(v_m_1147_, sizeof(void*)*3 + 2);
v_recKind_1152_ = lean_ctor_get_uint8(v_m_1147_, sizeof(void*)*3 + 3);
v_isUnsafe_1153_ = lean_ctor_get_uint8(v_m_1147_, sizeof(void*)*3 + 4);
v_attrs_1154_ = lean_ctor_get(v_m_1147_, 2);
lean_inc_ref(v_attrs_1154_);
lean_dec_ref(v_m_1147_);
if (lean_obj_tag(v_docString_x3f_1148_) == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_box(0);
v___y_1200_ = v___x_1204_;
goto v___jp_1199_;
}
else
{
lean_object* v_val_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v_val_1205_ = lean_ctor_get(v_docString_x3f_1148_, 0);
lean_inc(v_val_1205_);
lean_dec_ref_known(v_docString_x3f_1148_, 1);
v___x_1206_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__32));
v___x_1207_ = lean_box(0);
v___x_1208_ = 0;
v___x_1209_ = l_Lean_Syntax_formatStx(v_val_1205_, v___x_1207_, v___x_1208_);
v___x_1210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1206_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_1211_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__34));
v___x_1212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_box(0);
v___x_1214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___y_1200_ = v___x_1214_;
goto v___jp_1199_;
}
v___jp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v_components_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; 
lean_inc(v___y_1157_);
v___x_1158_ = l_List_appendTR___redArg(v___y_1156_, v___y_1157_);
v___x_1159_ = lean_array_to_list(v_attrs_1154_);
v___x_1160_ = lean_box(0);
v___x_1161_ = l_List_mapTR_loop___redArg(v___f_1145_, v___x_1159_, v___x_1160_);
v_components_1162_ = l_List_appendTR___redArg(v___x_1158_, v___x_1161_);
v___x_1163_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__3));
v___x_1164_ = l_Std_Format_joinSep___redArg(v___f_1146_, v_components_1162_, v___x_1163_);
v___x_1165_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__6, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__6_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6);
v___x_1166_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__7));
v___x_1167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v___x_1164_);
v___x_1168_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__8));
v___x_1169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1165_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = 0;
v___x_1172_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set_uint8(v___x_1172_, sizeof(void*)*1, v___x_1171_);
return v___x_1172_;
}
v___jp_1173_:
{
lean_object* v___x_1176_; 
lean_inc(v___y_1175_);
v___x_1176_ = l_List_appendTR___redArg(v___y_1174_, v___y_1175_);
if (v_isUnsafe_1153_ == 0)
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_box(0);
v___y_1156_ = v___x_1176_;
v___y_1157_ = v___x_1177_;
goto v___jp_1155_;
}
else
{
lean_object* v___x_1178_; 
v___x_1178_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__11));
v___y_1156_ = v___x_1176_;
v___y_1157_ = v___x_1178_;
goto v___jp_1155_;
}
}
v___jp_1179_:
{
lean_object* v___x_1182_; 
lean_inc(v___y_1181_);
v___x_1182_ = l_List_appendTR___redArg(v___y_1180_, v___y_1181_);
switch(v_recKind_1152_)
{
case 0:
{
lean_object* v___x_1183_; 
v___x_1183_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__14));
v___y_1174_ = v___x_1182_;
v___y_1175_ = v___x_1183_;
goto v___jp_1173_;
}
case 1:
{
lean_object* v___x_1184_; 
v___x_1184_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__17));
v___y_1174_ = v___x_1182_;
v___y_1175_ = v___x_1184_;
goto v___jp_1173_;
}
default: 
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_box(0);
v___y_1174_ = v___x_1182_;
v___y_1175_ = v___x_1185_;
goto v___jp_1173_;
}
}
}
v___jp_1186_:
{
lean_object* v___x_1189_; 
lean_inc(v___y_1188_);
v___x_1189_ = l_List_appendTR___redArg(v___y_1187_, v___y_1188_);
switch(v_computeKind_1151_)
{
case 0:
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_box(0);
v___y_1180_ = v___x_1189_;
v___y_1181_ = v___x_1190_;
goto v___jp_1179_;
}
case 1:
{
lean_object* v___x_1191_; 
v___x_1191_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__20));
v___y_1180_ = v___x_1189_;
v___y_1181_ = v___x_1191_;
goto v___jp_1179_;
}
default: 
{
lean_object* v___x_1192_; 
v___x_1192_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__23));
v___y_1180_ = v___x_1189_;
v___y_1181_ = v___x_1192_;
goto v___jp_1179_;
}
}
}
v___jp_1193_:
{
lean_object* v___x_1196_; 
lean_inc(v___y_1195_);
v___x_1196_ = l_List_appendTR___redArg(v___y_1194_, v___y_1195_);
if (v_isProtected_1150_ == 0)
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_box(0);
v___y_1187_ = v___x_1196_;
v___y_1188_ = v___x_1197_;
goto v___jp_1186_;
}
else
{
lean_object* v___x_1198_; 
v___x_1198_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__26));
v___y_1187_ = v___x_1196_;
v___y_1188_ = v___x_1198_;
goto v___jp_1186_;
}
}
v___jp_1199_:
{
switch(v_visibility_1149_)
{
case 0:
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_box(0);
v___y_1194_ = v___y_1200_;
v___y_1195_ = v___x_1201_;
goto v___jp_1193_;
}
case 1:
{
lean_object* v___x_1202_; 
v___x_1202_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__28));
v___y_1194_ = v___y_1200_;
v___y_1195_ = v___x_1202_;
goto v___jp_1193_;
}
default: 
{
lean_object* v___x_1203_; 
v___x_1203_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__30));
v___y_1194_ = v___y_1200_;
v___y_1195_ = v___x_1203_;
goto v___jp_1193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lam__0(lean_object* v_f_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = l_Std_Format_defWidth;
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = l_Std_Format_pretty(v_f_1221_, v___x_1222_, v___x_1223_, v___x_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = ((lean_object*)(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0));
v___x_1232_ = l_Lean_stringToMessageData(v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg(lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_optDocComment_1236_){
_start:
{
lean_object* v_toApplicative_1237_; lean_object* v_toPure_1238_; lean_object* v___x_1239_; 
v_toApplicative_1237_ = lean_ctor_get(v_inst_1234_, 0);
v_toPure_1238_ = lean_ctor_get(v_toApplicative_1237_, 1);
v___x_1239_ = l_Lean_Syntax_getOptional_x3f(v_optDocComment_1236_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_inc(v_toPure_1238_);
lean_dec_ref(v_inst_1235_);
lean_dec_ref(v_inst_1234_);
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_apply_2(v_toPure_1238_, lean_box(0), v___x_1240_);
return v___x_1241_;
}
else
{
lean_object* v_val_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1284_; 
v_val_1242_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1244_ = v___x_1239_;
v_isShared_1245_ = v_isSharedCheck_1284_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_val_1242_);
lean_dec(v___x_1239_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1284_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_unsigned_to_nat(1u);
v___x_1255_ = l_Lean_Syntax_getArg(v_val_1242_, v___x_1254_);
if (lean_obj_tag(v___x_1255_) == 1)
{
lean_object* v_kind_1256_; 
v_kind_1256_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_kind_1256_);
if (lean_obj_tag(v_kind_1256_) == 1)
{
lean_object* v_pre_1257_; 
v_pre_1257_ = lean_ctor_get(v_kind_1256_, 0);
lean_inc(v_pre_1257_);
if (lean_obj_tag(v_pre_1257_) == 1)
{
lean_object* v_pre_1258_; 
v_pre_1258_ = lean_ctor_get(v_pre_1257_, 0);
lean_inc(v_pre_1258_);
if (lean_obj_tag(v_pre_1258_) == 1)
{
lean_object* v_pre_1259_; 
v_pre_1259_ = lean_ctor_get(v_pre_1258_, 0);
lean_inc(v_pre_1259_);
if (lean_obj_tag(v_pre_1259_) == 1)
{
lean_object* v_pre_1260_; 
v_pre_1260_ = lean_ctor_get(v_pre_1259_, 0);
if (lean_obj_tag(v_pre_1260_) == 0)
{
lean_object* v_args_1261_; lean_object* v_str_1262_; lean_object* v_str_1263_; lean_object* v_str_1264_; lean_object* v_str_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v_args_1261_ = lean_ctor_get(v___x_1255_, 2);
lean_inc_ref(v_args_1261_);
lean_dec_ref_known(v___x_1255_, 3);
v_str_1262_ = lean_ctor_get(v_kind_1256_, 1);
lean_inc_ref(v_str_1262_);
lean_dec_ref_known(v_kind_1256_, 2);
v_str_1263_ = lean_ctor_get(v_pre_1257_, 1);
lean_inc_ref(v_str_1263_);
lean_dec_ref_known(v_pre_1257_, 2);
v_str_1264_ = lean_ctor_get(v_pre_1258_, 1);
lean_inc_ref(v_str_1264_);
lean_dec_ref_known(v_pre_1258_, 2);
v_str_1265_ = lean_ctor_get(v_pre_1259_, 1);
lean_inc_ref(v_str_1265_);
lean_dec_ref_known(v_pre_1259_, 2);
v___x_1266_ = ((lean_object*)(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_));
v___x_1267_ = lean_string_dec_eq(v_str_1265_, v___x_1266_);
lean_dec_ref(v_str_1265_);
if (v___x_1267_ == 0)
{
lean_dec_ref(v_str_1264_);
lean_dec_ref(v_str_1263_);
lean_dec_ref(v_str_1262_);
lean_dec_ref(v_args_1261_);
lean_del_object(v___x_1244_);
goto v___jp_1246_;
}
else
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6));
v___x_1269_ = lean_string_dec_eq(v_str_1264_, v___x_1268_);
lean_dec_ref(v_str_1264_);
if (v___x_1269_ == 0)
{
lean_dec_ref(v_str_1263_);
lean_dec_ref(v_str_1262_);
lean_dec_ref(v_args_1261_);
lean_del_object(v___x_1244_);
goto v___jp_1246_;
}
else
{
lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7));
v___x_1271_ = lean_string_dec_eq(v_str_1263_, v___x_1270_);
lean_dec_ref(v_str_1263_);
if (v___x_1271_ == 0)
{
lean_dec_ref(v_str_1262_);
lean_dec_ref(v_args_1261_);
lean_del_object(v___x_1244_);
goto v___jp_1246_;
}
else
{
lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = ((lean_object*)(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__2));
v___x_1273_ = lean_string_dec_eq(v_str_1262_, v___x_1272_);
lean_dec_ref(v_str_1262_);
if (v___x_1273_ == 0)
{
lean_dec_ref(v_args_1261_);
lean_del_object(v___x_1244_);
goto v___jp_1246_;
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1274_ = lean_array_get_size(v_args_1261_);
v___x_1275_ = lean_unsigned_to_nat(2u);
v___x_1276_ = lean_nat_dec_eq(v___x_1274_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_dec_ref(v_args_1261_);
lean_del_object(v___x_1244_);
goto v___jp_1246_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = lean_array_fget(v_args_1261_, v___x_1277_);
lean_dec_ref(v_args_1261_);
if (lean_obj_tag(v___x_1278_) == 2)
{
lean_object* v_val_1279_; lean_object* v___x_1281_; 
lean_inc(v_toPure_1238_);
lean_dec(v_val_1242_);
lean_dec_ref(v_inst_1235_);
lean_dec_ref(v_inst_1234_);
v_val_1279_ = lean_ctor_get(v___x_1278_, 1);
lean_inc_ref(v_val_1279_);
lean_dec_ref_known(v___x_1278_, 2);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v_val_1279_);
v___x_1281_ = v___x_1244_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_val_1279_);
v___x_1281_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_apply_2(v_toPure_1238_, lean_box(0), v___x_1281_);
return v___x_1282_;
}
}
else
{
lean_dec(v___x_1278_);
lean_del_object(v___x_1244_);
goto v___jp_1246_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1259_, 2);
lean_dec_ref_known(v_pre_1258_, 2);
lean_dec_ref_known(v_pre_1257_, 2);
lean_dec_ref_known(v_kind_1256_, 2);
lean_dec_ref_known(v___x_1255_, 3);
lean_del_object(v___x_1244_);
goto v___jp_1246_;
}
}
else
{
lean_dec(v_pre_1259_);
lean_dec_ref_known(v_pre_1258_, 2);
lean_dec_ref_known(v_pre_1257_, 2);
lean_dec_ref_known(v_kind_1256_, 2);
lean_dec_ref_known(v___x_1255_, 3);
lean_del_object(v___x_1244_);
goto v___jp_1246_;
}
}
else
{
lean_dec_ref_known(v_pre_1257_, 2);
lean_dec(v_pre_1258_);
lean_dec_ref_known(v_kind_1256_, 2);
lean_dec_ref_known(v___x_1255_, 3);
lean_del_object(v___x_1244_);
goto v___jp_1246_;
}
}
else
{
lean_dec(v_pre_1257_);
lean_dec_ref_known(v_kind_1256_, 2);
lean_dec_ref_known(v___x_1255_, 3);
lean_del_object(v___x_1244_);
goto v___jp_1246_;
}
}
else
{
lean_dec(v_kind_1256_);
lean_dec_ref_known(v___x_1255_, 3);
lean_del_object(v___x_1244_);
goto v___jp_1246_;
}
}
else
{
lean_dec(v___x_1255_);
lean_del_object(v___x_1244_);
goto v___jp_1246_;
}
v___jp_1246_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1247_ = lean_obj_once(&l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1, &l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1_once, _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1);
v___x_1248_ = lean_unsigned_to_nat(1u);
v___x_1249_ = l_Lean_Syntax_getArg(v_val_1242_, v___x_1248_);
v___x_1250_ = l_Lean_MessageData_ofSyntax(v___x_1249_);
v___x_1251_ = l_Lean_indentD(v___x_1250_);
v___x_1252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1247_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = l_Lean_throwErrorAt___redArg(v_inst_1234_, v_inst_1235_, v_val_1242_, v___x_1252_);
return v___x_1253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___boxed(lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_optDocComment_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1285_, v_inst_1286_, v_optDocComment_1287_);
lean_dec(v_optDocComment_1287_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f(lean_object* v_m_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_optDocComment_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1290_, v_inst_1291_, v_optDocComment_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___boxed(lean_object* v_m_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_optDocComment_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_Elab_expandOptDocComment_x3f(v_m_1294_, v_inst_1295_, v_inst_1296_, v_optDocComment_1297_);
lean_dec(v_optDocComment_1297_);
return v_res_1298_;
}
}
lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0(lean_object* v_stx_1299_, lean_object* v___y_1300_, uint8_t v_visibility_1301_, uint8_t v___y_1302_, uint8_t v___y_1303_, uint8_t v___y_1304_, lean_object* v_toPure_1305_, lean_object* v_unsafeStx_1306_, lean_object* v_attrs_1307_){
_start:
{
uint8_t v___y_1309_; uint8_t v___x_1312_; 
v___x_1312_ = l_Lean_Syntax_isNone(v_unsafeStx_1306_);
if (v___x_1312_ == 0)
{
uint8_t v___x_1313_; 
v___x_1313_ = 1;
v___y_1309_ = v___x_1313_;
goto v___jp_1308_;
}
else
{
uint8_t v___x_1314_; 
v___x_1314_ = 0;
v___y_1309_ = v___x_1314_;
goto v___jp_1308_;
}
v___jp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1310_, 0, v_stx_1299_);
lean_ctor_set(v___x_1310_, 1, v___y_1300_);
lean_ctor_set(v___x_1310_, 2, v_attrs_1307_);
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*3, v_visibility_1301_);
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*3 + 1, v___y_1302_);
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*3 + 2, v___y_1303_);
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*3 + 3, v___y_1304_);
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*3 + 4, v___y_1309_);
v___x_1311_ = lean_apply_2(v_toPure_1305_, lean_box(0), v___x_1310_);
return v___x_1311_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_elabModifiers___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1299_ = stack[0].m_obj;
lean_object* v___y_1300_ = stack[1].m_obj;
uint8_t v_visibility_1301_ = stack[2].m_num;
uint8_t v___y_1302_ = stack[3].m_num;
uint8_t v___y_1303_ = stack[4].m_num;
uint8_t v___y_1304_ = stack[5].m_num;
lean_object* v_toPure_1305_ = stack[6].m_obj;
lean_object* v_unsafeStx_1306_ = stack[7].m_obj;
lean_object* v_attrs_1307_ = stack[8].m_obj;
lean_object* v_res_1315_;
v_res_1315_ = l_Lean_Elab_elabModifiers___redArg___lam__0(v_stx_1299_, v___y_1300_, v_visibility_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v_toPure_1305_, v_unsafeStx_1306_, v_attrs_1307_);
stack->m_obj
 = v_res_1315_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0___boxed(lean_object* v_stx_1316_, lean_object* v___y_1317_, lean_object* v_visibility_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v_toPure_1322_, lean_object* v_unsafeStx_1323_, lean_object* v_attrs_1324_){
_start:
{
uint8_t v_visibility_boxed_1325_; uint8_t v___y_305__boxed_1326_; uint8_t v___y_306__boxed_1327_; uint8_t v___y_307__boxed_1328_; lean_object* v_res_1329_; 
v_visibility_boxed_1325_ = lean_unbox(v_visibility_1318_);
v___y_305__boxed_1326_ = lean_unbox(v___y_1319_);
v___y_306__boxed_1327_ = lean_unbox(v___y_1320_);
v___y_307__boxed_1328_ = lean_unbox(v___y_1321_);
v_res_1329_ = l_Lean_Elab_elabModifiers___redArg___lam__0(v_stx_1316_, v___y_1317_, v_visibility_boxed_1325_, v___y_305__boxed_1326_, v___y_306__boxed_1327_, v___y_307__boxed_1328_, v_toPure_1322_, v_unsafeStx_1323_, v_attrs_1324_);
lean_dec(v_unsafeStx_1323_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__1(lean_object* v___f_1330_, lean_object* v_attrs_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_apply_1(v___f_1330_, v_attrs_1331_);
return v___x_1332_;
}
}
lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3(lean_object* v_stx_1333_, lean_object* v___y_1334_, uint8_t v___y_1335_, uint8_t v___y_1336_, lean_object* v_toPure_1337_, lean_object* v_unsafeStx_1338_, lean_object* v_attrsStx_1339_, lean_object* v___x_1340_, lean_object* v_toBind_1341_, lean_object* v_inst_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_protectedStx_1354_, uint8_t v_visibility_1355_){
_start:
{
uint8_t v___y_1357_; uint8_t v___x_1372_; 
v___x_1372_ = l_Lean_Syntax_isNone(v_protectedStx_1354_);
if (v___x_1372_ == 0)
{
uint8_t v___x_1373_; 
v___x_1373_ = 1;
v___y_1357_ = v___x_1373_;
goto v___jp_1356_;
}
else
{
uint8_t v___x_1374_; 
v___x_1374_ = 0;
v___y_1357_ = v___x_1374_;
goto v___jp_1356_;
}
v___jp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___f_1362_; lean_object* v___x_1363_; 
v___x_1358_ = lean_box(v_visibility_1355_);
v___x_1359_ = lean_box(v___y_1357_);
v___x_1360_ = lean_box(v___y_1335_);
v___x_1361_ = lean_box(v___y_1336_);
lean_inc(v_toPure_1337_);
v___f_1362_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_1362_, 0, v_stx_1333_);
lean_closure_set(v___f_1362_, 1, v___y_1334_);
lean_closure_set(v___f_1362_, 2, v___x_1358_);
lean_closure_set(v___f_1362_, 3, v___x_1359_);
lean_closure_set(v___f_1362_, 4, v___x_1360_);
lean_closure_set(v___f_1362_, 5, v___x_1361_);
lean_closure_set(v___f_1362_, 6, v_toPure_1337_);
lean_closure_set(v___f_1362_, 7, v_unsafeStx_1338_);
v___x_1363_ = l_Lean_Syntax_getOptional_x3f(v_attrsStx_1339_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v___f_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec(v_inst_1353_);
lean_dec(v_inst_1352_);
lean_dec_ref(v_inst_1351_);
lean_dec(v_inst_1350_);
lean_dec_ref(v_inst_1349_);
lean_dec_ref(v_inst_1348_);
lean_dec_ref(v_inst_1347_);
lean_dec_ref(v_inst_1346_);
lean_dec_ref(v_inst_1345_);
lean_dec_ref(v_inst_1344_);
lean_dec_ref(v_inst_1343_);
lean_dec_ref(v_inst_1342_);
v___f_1364_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1364_, 0, v___f_1362_);
v___x_1365_ = lean_mk_empty_array_with_capacity(v___x_1340_);
v___x_1366_ = lean_apply_2(v_toPure_1337_, lean_box(0), v___x_1365_);
v___x_1367_ = lean_apply_4(v_toBind_1341_, lean_box(0), lean_box(0), v___x_1366_, v___f_1364_);
return v___x_1367_;
}
else
{
lean_object* v_val_1368_; lean_object* v___f_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_dec(v_toPure_1337_);
v_val_1368_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_val_1368_);
lean_dec_ref_known(v___x_1363_, 1);
v___f_1369_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1369_, 0, v___f_1362_);
v___x_1370_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_1342_, v_inst_1343_, v_inst_1344_, v_inst_1345_, v_inst_1346_, v_inst_1347_, v_inst_1348_, v_inst_1349_, v_inst_1350_, v_inst_1351_, v_inst_1352_, v_inst_1353_, v_val_1368_);
lean_dec(v_val_1368_);
v___x_1371_ = lean_apply_4(v_toBind_1341_, lean_box(0), lean_box(0), v___x_1370_, v___f_1369_);
return v___x_1371_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_elabModifiers___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1333_ = stack[0].m_obj;
lean_object* v___y_1334_ = stack[1].m_obj;
uint8_t v___y_1335_ = stack[2].m_num;
uint8_t v___y_1336_ = stack[3].m_num;
lean_object* v_toPure_1337_ = stack[4].m_obj;
lean_object* v_unsafeStx_1338_ = stack[5].m_obj;
lean_object* v_attrsStx_1339_ = stack[6].m_obj;
lean_object* v___x_1340_ = stack[7].m_obj;
lean_object* v_toBind_1341_ = stack[8].m_obj;
lean_object* v_inst_1342_ = stack[9].m_obj;
lean_object* v_inst_1343_ = stack[10].m_obj;
lean_object* v_inst_1344_ = stack[11].m_obj;
lean_object* v_inst_1345_ = stack[12].m_obj;
lean_object* v_inst_1346_ = stack[13].m_obj;
lean_object* v_inst_1347_ = stack[14].m_obj;
lean_object* v_inst_1348_ = stack[15].m_obj;
lean_object* v_inst_1349_ = stack[16].m_obj;
lean_object* v_inst_1350_ = stack[17].m_obj;
lean_object* v_inst_1351_ = stack[18].m_obj;
lean_object* v_inst_1352_ = stack[19].m_obj;
lean_object* v_inst_1353_ = stack[20].m_obj;
lean_object* v_protectedStx_1354_ = stack[21].m_obj;
uint8_t v_visibility_1355_ = stack[22].m_num;
lean_object* v_res_1375_;
v_res_1375_ = l_Lean_Elab_elabModifiers___redArg___lam__3(v_stx_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v_toPure_1337_, v_unsafeStx_1338_, v_attrsStx_1339_, v___x_1340_, v_toBind_1341_, v_inst_1342_, v_inst_1343_, v_inst_1344_, v_inst_1345_, v_inst_1346_, v_inst_1347_, v_inst_1348_, v_inst_1349_, v_inst_1350_, v_inst_1351_, v_inst_1352_, v_inst_1353_, v_protectedStx_1354_, v_visibility_1355_);
stack->m_obj
 = v_res_1375_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_stx_1376_ = _args[0];
lean_object* v___y_1377_ = _args[1];
lean_object* v___y_1378_ = _args[2];
lean_object* v___y_1379_ = _args[3];
lean_object* v_toPure_1380_ = _args[4];
lean_object* v_unsafeStx_1381_ = _args[5];
lean_object* v_attrsStx_1382_ = _args[6];
lean_object* v___x_1383_ = _args[7];
lean_object* v_toBind_1384_ = _args[8];
lean_object* v_inst_1385_ = _args[9];
lean_object* v_inst_1386_ = _args[10];
lean_object* v_inst_1387_ = _args[11];
lean_object* v_inst_1388_ = _args[12];
lean_object* v_inst_1389_ = _args[13];
lean_object* v_inst_1390_ = _args[14];
lean_object* v_inst_1391_ = _args[15];
lean_object* v_inst_1392_ = _args[16];
lean_object* v_inst_1393_ = _args[17];
lean_object* v_inst_1394_ = _args[18];
lean_object* v_inst_1395_ = _args[19];
lean_object* v_inst_1396_ = _args[20];
lean_object* v_protectedStx_1397_ = _args[21];
lean_object* v_visibility_1398_ = _args[22];
_start:
{
uint8_t v___y_352__boxed_1399_; uint8_t v___y_353__boxed_1400_; uint8_t v_visibility_boxed_1401_; lean_object* v_res_1402_; 
v___y_352__boxed_1399_ = lean_unbox(v___y_1378_);
v___y_353__boxed_1400_ = lean_unbox(v___y_1379_);
v_visibility_boxed_1401_ = lean_unbox(v_visibility_1398_);
v_res_1402_ = l_Lean_Elab_elabModifiers___redArg___lam__3(v_stx_1376_, v___y_1377_, v___y_352__boxed_1399_, v___y_353__boxed_1400_, v_toPure_1380_, v_unsafeStx_1381_, v_attrsStx_1382_, v___x_1383_, v_toBind_1384_, v_inst_1385_, v_inst_1386_, v_inst_1387_, v_inst_1388_, v_inst_1389_, v_inst_1390_, v_inst_1391_, v_inst_1392_, v_inst_1393_, v_inst_1394_, v_inst_1395_, v_inst_1396_, v_protectedStx_1397_, v_visibility_boxed_1401_);
lean_dec(v_protectedStx_1397_);
lean_dec(v___x_1383_);
lean_dec(v_attrsStx_1382_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg(lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_inst_1415_, lean_object* v_inst_1416_, lean_object* v_inst_1417_, lean_object* v_inst_1418_, lean_object* v_inst_1419_, lean_object* v_inst_1420_, lean_object* v_inst_1421_, lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_stx_1425_){
_start:
{
lean_object* v_toApplicative_1426_; lean_object* v_toBind_1427_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v_toPure_1433_; lean_object* v___x_1434_; lean_object* v_docCommentStx_1435_; lean_object* v___x_1436_; lean_object* v_attrsStx_1437_; lean_object* v___x_1438_; lean_object* v_visibilityStx_1439_; lean_object* v___x_1440_; lean_object* v_protectedStx_1441_; uint8_t v___y_1443_; uint8_t v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; uint8_t v___y_1461_; lean_object* v___y_1462_; uint8_t v___y_1463_; uint8_t v___y_1475_; lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v_toApplicative_1426_ = lean_ctor_get(v_inst_1413_, 0);
v_toBind_1427_ = lean_ctor_get(v_inst_1413_, 1);
lean_inc(v_toBind_1427_);
v_toPure_1433_ = lean_ctor_get(v_toApplicative_1426_, 1);
v___x_1434_ = lean_unsigned_to_nat(0u);
v_docCommentStx_1435_ = l_Lean_Syntax_getArg(v_stx_1425_, v___x_1434_);
v___x_1436_ = lean_unsigned_to_nat(1u);
v_attrsStx_1437_ = l_Lean_Syntax_getArg(v_stx_1425_, v___x_1436_);
v___x_1438_ = lean_unsigned_to_nat(2u);
v_visibilityStx_1439_ = l_Lean_Syntax_getArg(v_stx_1425_, v___x_1438_);
v___x_1440_ = lean_unsigned_to_nat(3u);
v_protectedStx_1441_ = l_Lean_Syntax_getArg(v_stx_1425_, v___x_1440_);
v___x_1488_ = lean_unsigned_to_nat(4u);
v___x_1489_ = l_Lean_Syntax_getArg(v_stx_1425_, v___x_1488_);
v___x_1490_ = l_Lean_Syntax_isNone(v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1491_ = l_Lean_Syntax_getArg(v___x_1489_, v___x_1434_);
lean_dec(v___x_1489_);
v___x_1492_ = l_Lean_Syntax_getKind(v___x_1491_);
v___x_1493_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__1));
v___x_1494_ = lean_name_eq(v___x_1492_, v___x_1493_);
lean_dec(v___x_1492_);
if (v___x_1494_ == 0)
{
uint8_t v___x_1495_; 
v___x_1495_ = 2;
v___y_1475_ = v___x_1495_;
goto v___jp_1474_;
}
else
{
uint8_t v___x_1496_; 
v___x_1496_ = 1;
v___y_1475_ = v___x_1496_;
goto v___jp_1474_;
}
}
else
{
uint8_t v___x_1497_; 
lean_dec(v___x_1489_);
v___x_1497_ = 0;
v___y_1475_ = v___x_1497_;
goto v___jp_1474_;
}
v___jp_1428_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = l_Lean_Elab_elabVisibility___redArg(v_inst_1413_, v_inst_1416_, v_inst_1414_, v_inst_1421_, v_inst_1423_, v_inst_1422_, v___y_1430_);
v___x_1432_ = lean_apply_4(v_toBind_1427_, lean_box(0), lean_box(0), v___x_1431_, v___y_1429_);
return v___x_1432_;
}
v___jp_1442_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___f_1449_; lean_object* v___x_1450_; 
v___x_1447_ = lean_box(v___y_1444_);
v___x_1448_ = lean_box(v___y_1443_);
lean_inc_ref(v_inst_1423_);
lean_inc(v_inst_1422_);
lean_inc_ref(v_inst_1421_);
lean_inc_ref(v_inst_1416_);
lean_inc_ref(v_inst_1414_);
lean_inc_ref(v_inst_1413_);
lean_inc(v_toBind_1427_);
lean_inc(v_toPure_1433_);
v___f_1449_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__3___boxed), 23, 22);
lean_closure_set(v___f_1449_, 0, v_stx_1425_);
lean_closure_set(v___f_1449_, 1, v___y_1446_);
lean_closure_set(v___f_1449_, 2, v___x_1447_);
lean_closure_set(v___f_1449_, 3, v___x_1448_);
lean_closure_set(v___f_1449_, 4, v_toPure_1433_);
lean_closure_set(v___f_1449_, 5, v___y_1445_);
lean_closure_set(v___f_1449_, 6, v_attrsStx_1437_);
lean_closure_set(v___f_1449_, 7, v___x_1434_);
lean_closure_set(v___f_1449_, 8, v_toBind_1427_);
lean_closure_set(v___f_1449_, 9, v_inst_1413_);
lean_closure_set(v___f_1449_, 10, v_inst_1414_);
lean_closure_set(v___f_1449_, 11, v_inst_1415_);
lean_closure_set(v___f_1449_, 12, v_inst_1416_);
lean_closure_set(v___f_1449_, 13, v_inst_1418_);
lean_closure_set(v___f_1449_, 14, v_inst_1419_);
lean_closure_set(v___f_1449_, 15, v_inst_1420_);
lean_closure_set(v___f_1449_, 16, v_inst_1421_);
lean_closure_set(v___f_1449_, 17, v_inst_1422_);
lean_closure_set(v___f_1449_, 18, v_inst_1423_);
lean_closure_set(v___f_1449_, 19, v_inst_1424_);
lean_closure_set(v___f_1449_, 20, v_inst_1417_);
lean_closure_set(v___f_1449_, 21, v_protectedStx_1441_);
v___x_1450_ = l_Lean_Syntax_getOptional_x3f(v_visibilityStx_1439_);
lean_dec(v_visibilityStx_1439_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_box(0);
v___y_1429_ = v___f_1449_;
v___y_1430_ = v___x_1451_;
goto v___jp_1428_;
}
else
{
lean_object* v_val_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
v_val_1452_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1450_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_val_1452_);
lean_dec(v___x_1450_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_val_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
v___y_1429_ = v___f_1449_;
v___y_1430_ = v___x_1457_;
goto v___jp_1428_;
}
}
}
}
v___jp_1460_:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_Syntax_getOptional_x3f(v_docCommentStx_1435_);
lean_dec(v_docCommentStx_1435_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_box(0);
v___y_1443_ = v___y_1463_;
v___y_1444_ = v___y_1461_;
v___y_1445_ = v___y_1462_;
v___y_1446_ = v___x_1465_;
goto v___jp_1442_;
}
else
{
lean_object* v_val_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
v_val_1466_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1464_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_val_1466_);
lean_dec(v___x_1464_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_val_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
v___y_1443_ = v___y_1463_;
v___y_1444_ = v___y_1461_;
v___y_1445_ = v___y_1462_;
v___y_1446_ = v___x_1471_;
goto v___jp_1442_;
}
}
}
}
v___jp_1474_:
{
lean_object* v___x_1476_; lean_object* v_unsafeStx_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1476_ = lean_unsigned_to_nat(5u);
v_unsafeStx_1477_ = l_Lean_Syntax_getArg(v_stx_1425_, v___x_1476_);
v___x_1478_ = lean_unsigned_to_nat(6u);
v___x_1479_ = l_Lean_Syntax_getArg(v_stx_1425_, v___x_1478_);
v___x_1480_ = l_Lean_Syntax_isNone(v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1481_ = l_Lean_Syntax_getArg(v___x_1479_, v___x_1434_);
lean_dec(v___x_1479_);
v___x_1482_ = l_Lean_Syntax_getKind(v___x_1481_);
v___x_1483_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__0));
v___x_1484_ = lean_name_eq(v___x_1482_, v___x_1483_);
lean_dec(v___x_1482_);
if (v___x_1484_ == 0)
{
uint8_t v___x_1485_; 
v___x_1485_ = 1;
v___y_1461_ = v___y_1475_;
v___y_1462_ = v_unsafeStx_1477_;
v___y_1463_ = v___x_1485_;
goto v___jp_1460_;
}
else
{
uint8_t v___x_1486_; 
v___x_1486_ = 0;
v___y_1461_ = v___y_1475_;
v___y_1462_ = v_unsafeStx_1477_;
v___y_1463_ = v___x_1486_;
goto v___jp_1460_;
}
}
else
{
uint8_t v___x_1487_; 
lean_dec(v___x_1479_);
v___x_1487_ = 2;
v___y_1461_ = v___y_1475_;
v___y_1462_ = v_unsafeStx_1477_;
v___y_1463_ = v___x_1487_;
goto v___jp_1460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object* v_m_1498_, lean_object* v_inst_1499_, lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_stx_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_Elab_elabModifiers___redArg(v_inst_1499_, v_inst_1500_, v_inst_1501_, v_inst_1502_, v_inst_1503_, v_inst_1504_, v_inst_1505_, v_inst_1506_, v_inst_1507_, v_inst_1508_, v_inst_1509_, v_inst_1510_, v_stx_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__0(lean_object* v_toPure_1513_, lean_object* v_declName_1514_, lean_object* v_____r_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_apply_2(v_toPure_1513_, lean_box(0), v_declName_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__1(lean_object* v_declName_1517_, lean_object* v_env_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_addProtected(v_env_1518_, v_declName_1517_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2(lean_object* v_modifiers_1520_, lean_object* v_toPure_1521_, lean_object* v_declName_1522_, lean_object* v_modifyEnv_1523_, lean_object* v___f_1524_, lean_object* v_toBind_1525_, lean_object* v___f_1526_, lean_object* v_____r_1527_){
_start:
{
uint8_t v_isProtected_1528_; 
v_isProtected_1528_ = lean_ctor_get_uint8(v_modifiers_1520_, sizeof(void*)*3 + 1);
if (v_isProtected_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_dec(v___f_1526_);
lean_dec(v_toBind_1525_);
lean_dec_ref(v___f_1524_);
lean_dec(v_modifyEnv_1523_);
v___x_1529_ = lean_apply_2(v_toPure_1521_, lean_box(0), v_declName_1522_);
return v___x_1529_;
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec(v_declName_1522_);
lean_dec(v_toPure_1521_);
v___x_1530_ = lean_apply_1(v_modifyEnv_1523_, v___f_1524_);
v___x_1531_ = lean_apply_4(v_toBind_1525_, lean_box(0), lean_box(0), v___x_1530_, v___f_1526_);
return v___x_1531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2___boxed(lean_object* v_modifiers_1532_, lean_object* v_toPure_1533_, lean_object* v_declName_1534_, lean_object* v_modifyEnv_1535_, lean_object* v___f_1536_, lean_object* v_toBind_1537_, lean_object* v___f_1538_, lean_object* v_____r_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_Elab_applyVisibility___redArg___lam__2(v_modifiers_1532_, v_toPure_1533_, v_declName_1534_, v_modifyEnv_1535_, v___f_1536_, v_toBind_1537_, v___f_1538_, v_____r_1539_);
lean_dec_ref(v_modifiers_1532_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__3(lean_object* v_toPure_1541_, lean_object* v_modifiers_1542_, lean_object* v_modifyEnv_1543_, lean_object* v_toBind_1544_, lean_object* v_inst_1545_, lean_object* v_inst_1546_, lean_object* v_inst_1547_, lean_object* v_inst_1548_, lean_object* v_inst_1549_, lean_object* v_____r_1550_, lean_object* v_declName_1551_){
_start:
{
lean_object* v___f_1552_; lean_object* v___f_1553_; lean_object* v___f_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_inc_n(v_declName_1551_, 3);
lean_inc(v_toPure_1541_);
v___f_1552_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1552_, 0, v_toPure_1541_);
lean_closure_set(v___f_1552_, 1, v_declName_1551_);
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1553_, 0, v_declName_1551_);
lean_inc(v_toBind_1544_);
v___f_1554_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1554_, 0, v_modifiers_1542_);
lean_closure_set(v___f_1554_, 1, v_toPure_1541_);
lean_closure_set(v___f_1554_, 2, v_declName_1551_);
lean_closure_set(v___f_1554_, 3, v_modifyEnv_1543_);
lean_closure_set(v___f_1554_, 4, v___f_1553_);
lean_closure_set(v___f_1554_, 5, v_toBind_1544_);
lean_closure_set(v___f_1554_, 6, v___f_1552_);
v___x_1555_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(v_inst_1545_, v_inst_1546_, v_inst_1547_, v_inst_1548_, v_inst_1549_, v_declName_1551_);
v___x_1556_ = lean_apply_4(v_toBind_1544_, lean_box(0), lean_box(0), v___x_1555_, v___f_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4(lean_object* v_declName_1557_, lean_object* v___f_1558_, lean_object* v_____do__lift_1559_){
_start:
{
lean_object* v_declName_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_declName_1560_ = l_Lean_mkPrivateName(v_____do__lift_1559_, v_declName_1557_);
v___x_1561_ = lean_box(0);
v___x_1562_ = lean_apply_2(v___f_1558_, v___x_1561_, v_declName_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4___boxed(lean_object* v_declName_1563_, lean_object* v___f_1564_, lean_object* v_____do__lift_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Elab_applyVisibility___redArg___lam__4(v_declName_1563_, v___f_1564_, v_____do__lift_1565_);
lean_dec_ref(v_____do__lift_1565_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5(lean_object* v_modifiers_1567_, lean_object* v_toBind_1568_, lean_object* v_getEnv_1569_, lean_object* v___f_1570_, lean_object* v___f_1571_, lean_object* v_declName_1572_, lean_object* v_____do__lift_1573_){
_start:
{
uint8_t v_visibility_1574_; uint8_t v___x_1575_; 
v_visibility_1574_ = lean_ctor_get_uint8(v_modifiers_1567_, sizeof(void*)*3);
v___x_1575_ = l_Lean_Elab_Visibility_isInferredPublic(v_____do__lift_1573_, v_visibility_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_dec(v_declName_1572_);
lean_dec(v___f_1571_);
v___x_1576_ = lean_apply_4(v_toBind_1568_, lean_box(0), lean_box(0), v_getEnv_1569_, v___f_1570_);
return v___x_1576_;
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_dec(v___f_1570_);
lean_dec(v_getEnv_1569_);
lean_dec(v_toBind_1568_);
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_apply_2(v___f_1571_, v___x_1577_, v_declName_1572_);
return v___x_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5___boxed(lean_object* v_modifiers_1579_, lean_object* v_toBind_1580_, lean_object* v_getEnv_1581_, lean_object* v___f_1582_, lean_object* v___f_1583_, lean_object* v_declName_1584_, lean_object* v_____do__lift_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_Elab_applyVisibility___redArg___lam__5(v_modifiers_1579_, v_toBind_1580_, v_getEnv_1581_, v___f_1582_, v___f_1583_, v_declName_1584_, v_____do__lift_1585_);
lean_dec_ref(v_____do__lift_1585_);
lean_dec_ref(v_modifiers_1579_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg(lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_inst_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_modifiers_1592_, lean_object* v_declName_1593_){
_start:
{
lean_object* v_toApplicative_1594_; lean_object* v_toBind_1595_; lean_object* v_getEnv_1596_; lean_object* v_modifyEnv_1597_; lean_object* v_toPure_1598_; lean_object* v___f_1599_; lean_object* v___f_1600_; lean_object* v___f_1601_; lean_object* v___x_1602_; 
v_toApplicative_1594_ = lean_ctor_get(v_inst_1587_, 0);
v_toBind_1595_ = lean_ctor_get(v_inst_1587_, 1);
lean_inc_n(v_toBind_1595_, 3);
v_getEnv_1596_ = lean_ctor_get(v_inst_1588_, 0);
lean_inc_n(v_getEnv_1596_, 2);
v_modifyEnv_1597_ = lean_ctor_get(v_inst_1588_, 1);
lean_inc(v_modifyEnv_1597_);
v_toPure_1598_ = lean_ctor_get(v_toApplicative_1594_, 1);
lean_inc(v_toPure_1598_);
lean_inc_ref(v_modifiers_1592_);
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__3), 11, 9);
lean_closure_set(v___f_1599_, 0, v_toPure_1598_);
lean_closure_set(v___f_1599_, 1, v_modifiers_1592_);
lean_closure_set(v___f_1599_, 2, v_modifyEnv_1597_);
lean_closure_set(v___f_1599_, 3, v_toBind_1595_);
lean_closure_set(v___f_1599_, 4, v_inst_1587_);
lean_closure_set(v___f_1599_, 5, v_inst_1588_);
lean_closure_set(v___f_1599_, 6, v_inst_1589_);
lean_closure_set(v___f_1599_, 7, v_inst_1590_);
lean_closure_set(v___f_1599_, 8, v_inst_1591_);
lean_inc_ref(v___f_1599_);
lean_inc(v_declName_1593_);
v___f_1600_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_1600_, 0, v_declName_1593_);
lean_closure_set(v___f_1600_, 1, v___f_1599_);
v___f_1601_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1601_, 0, v_modifiers_1592_);
lean_closure_set(v___f_1601_, 1, v_toBind_1595_);
lean_closure_set(v___f_1601_, 2, v_getEnv_1596_);
lean_closure_set(v___f_1601_, 3, v___f_1600_);
lean_closure_set(v___f_1601_, 4, v___f_1599_);
lean_closure_set(v___f_1601_, 5, v_declName_1593_);
v___x_1602_ = lean_apply_4(v_toBind_1595_, lean_box(0), lean_box(0), v_getEnv_1596_, v___f_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility(lean_object* v_m_1603_, lean_object* v_inst_1604_, lean_object* v_inst_1605_, lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_modifiers_1609_, lean_object* v_declName_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1604_, v_inst_1605_, v_inst_1606_, v_inst_1607_, v_inst_1608_, v_modifiers_1609_, v_declName_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0(lean_object* v_toPure_1612_, lean_object* v_____s_1613_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_box(0);
v___x_1615_ = lean_apply_2(v_toPure_1612_, lean_box(0), v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1(lean_object* v___x_1616_, lean_object* v_toPure_1617_, lean_object* v_r_1618_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1616_);
v___x_1620_ = lean_apply_2(v_toPure_1617_, lean_box(0), v___x_1619_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0));
v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
return v___x_1623_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2));
v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
return v___x_1626_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4));
v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2(lean_object* v_pre_1630_, lean_object* v_declName_1631_, lean_object* v___x_1632_, lean_object* v_toPure_1633_, lean_object* v_inst_1634_, lean_object* v_inst_1635_, lean_object* v_toBind_1636_, lean_object* v___f_1637_, lean_object* v_a_1638_, lean_object* v_x_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
lean_inc(v_a_1638_);
lean_inc(v_pre_1630_);
v___x_1641_ = l_Lean_Name_append(v_pre_1630_, v_a_1638_);
v___x_1642_ = lean_name_eq(v___x_1641_, v_declName_1631_);
lean_dec(v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_dec(v_a_1638_);
lean_dec(v___f_1637_);
lean_dec(v_toBind_1636_);
lean_dec_ref(v_inst_1635_);
lean_dec_ref(v_inst_1634_);
lean_dec(v_declName_1631_);
lean_dec(v_pre_1630_);
v___x_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1632_);
v___x_1644_ = lean_apply_2(v_toPure_1633_, lean_box(0), v___x_1643_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; uint8_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_dec(v_toPure_1633_);
v___x_1645_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1646_ = 0;
v___x_1647_ = l_Lean_MessageData_ofConstName(v_declName_1631_, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1645_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = l_Lean_MessageData_ofName(v_pre_1630_);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = l_Lean_MessageData_ofName(v_a_1638_);
v___x_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = l_Lean_throwError___redArg(v_inst_1634_, v_inst_1635_, v___x_1658_);
v___x_1660_ = lean_apply_4(v_toBind_1636_, lean_box(0), lean_box(0), v___x_1659_, v___f_1637_);
return v___x_1660_;
}
}
}
lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(lean_object* v_pre_1661_, uint8_t v___x_1662_, lean_object* v_toPure_1663_, lean_object* v_declName_1664_, lean_object* v_inst_1665_, lean_object* v_inst_1666_, lean_object* v_toBind_1667_, lean_object* v___f_1668_, lean_object* v_____do__lift_1669_){
_start:
{
lean_object* v_fieldNames_1670_; lean_object* v___x_1671_; lean_object* v___f_1672_; lean_object* v___f_1673_; size_t v_sz_1674_; size_t v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_inc(v_pre_1661_);
v_fieldNames_1670_ = l_Lean_getStructureFieldsFlattened(v_____do__lift_1669_, v_pre_1661_, v___x_1662_);
v___x_1671_ = lean_box(0);
lean_inc(v_toPure_1663_);
v___f_1672_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1672_, 0, v___x_1671_);
lean_closure_set(v___f_1672_, 1, v_toPure_1663_);
lean_inc(v_toBind_1667_);
lean_inc_ref(v_inst_1665_);
v___f_1673_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2), 11, 8);
lean_closure_set(v___f_1673_, 0, v_pre_1661_);
lean_closure_set(v___f_1673_, 1, v_declName_1664_);
lean_closure_set(v___f_1673_, 2, v___x_1671_);
lean_closure_set(v___f_1673_, 3, v_toPure_1663_);
lean_closure_set(v___f_1673_, 4, v_inst_1665_);
lean_closure_set(v___f_1673_, 5, v_inst_1666_);
lean_closure_set(v___f_1673_, 6, v_toBind_1667_);
lean_closure_set(v___f_1673_, 7, v___f_1672_);
v_sz_1674_ = lean_array_size(v_fieldNames_1670_);
v___x_1675_ = ((size_t)0ULL);
v___x_1676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1665_, v_fieldNames_1670_, v___f_1673_, v_sz_1674_, v___x_1675_, v___x_1671_);
v___x_1677_ = lean_apply_4(v_toBind_1667_, lean_box(0), lean_box(0), v___x_1676_, v___f_1668_);
return v___x_1677_;
}
}
LEAN_EXPORT void l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1661_ = stack[0].m_obj;
uint8_t v___x_1662_ = stack[1].m_num;
lean_object* v_toPure_1663_ = stack[2].m_obj;
lean_object* v_declName_1664_ = stack[3].m_obj;
lean_object* v_inst_1665_ = stack[4].m_obj;
lean_object* v_inst_1666_ = stack[5].m_obj;
lean_object* v_toBind_1667_ = stack[6].m_obj;
lean_object* v___f_1668_ = stack[7].m_obj;
lean_object* v_____do__lift_1669_ = stack[8].m_obj;
lean_object* v_res_1678_;
v_res_1678_ = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(v_pre_1661_, v___x_1662_, v_toPure_1663_, v_declName_1664_, v_inst_1665_, v_inst_1666_, v_toBind_1667_, v___f_1668_, v_____do__lift_1669_);
stack->m_obj
 = v_res_1678_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed(lean_object* v_pre_1679_, lean_object* v___x_1680_, lean_object* v_toPure_1681_, lean_object* v_declName_1682_, lean_object* v_inst_1683_, lean_object* v_inst_1684_, lean_object* v_toBind_1685_, lean_object* v___f_1686_, lean_object* v_____do__lift_1687_){
_start:
{
uint8_t v___x_512__boxed_1688_; lean_object* v_res_1689_; 
v___x_512__boxed_1688_ = lean_unbox(v___x_1680_);
v_res_1689_ = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(v_pre_1679_, v___x_512__boxed_1688_, v_toPure_1681_, v_declName_1682_, v_inst_1683_, v_inst_1684_, v_toBind_1685_, v___f_1686_, v_____do__lift_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4(lean_object* v_pre_1690_, lean_object* v_toPure_1691_, lean_object* v_declName_1692_, lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v_toBind_1695_, lean_object* v___f_1696_, lean_object* v_getEnv_1697_, lean_object* v_____do__lift_1698_){
_start:
{
uint8_t v___x_1699_; 
lean_inc(v_pre_1690_);
v___x_1699_ = l_Lean_isStructure(v_____do__lift_1698_, v_pre_1690_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
lean_dec(v_getEnv_1697_);
lean_dec(v___f_1696_);
lean_dec(v_toBind_1695_);
lean_dec_ref(v_inst_1694_);
lean_dec_ref(v_inst_1693_);
lean_dec(v_declName_1692_);
lean_dec(v_pre_1690_);
v___x_1700_ = lean_box(0);
v___x_1701_ = lean_apply_2(v_toPure_1691_, lean_box(0), v___x_1700_);
return v___x_1701_;
}
else
{
lean_object* v___x_1702_; lean_object* v___f_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_box(v___x_1699_);
lean_inc(v_toBind_1695_);
v___f_1703_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1703_, 0, v_pre_1690_);
lean_closure_set(v___f_1703_, 1, v___x_1702_);
lean_closure_set(v___f_1703_, 2, v_toPure_1691_);
lean_closure_set(v___f_1703_, 3, v_declName_1692_);
lean_closure_set(v___f_1703_, 4, v_inst_1693_);
lean_closure_set(v___f_1703_, 5, v_inst_1694_);
lean_closure_set(v___f_1703_, 6, v_toBind_1695_);
lean_closure_set(v___f_1703_, 7, v___f_1696_);
v___x_1704_ = lean_apply_4(v_toBind_1695_, lean_box(0), lean_box(0), v_getEnv_1697_, v___f_1703_);
return v___x_1704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg(lean_object* v_inst_1705_, lean_object* v_inst_1706_, lean_object* v_inst_1707_, lean_object* v_declName_1708_){
_start:
{
if (lean_obj_tag(v_declName_1708_) == 1)
{
lean_object* v_toApplicative_1709_; lean_object* v_toBind_1710_; lean_object* v_toPure_1711_; lean_object* v_pre_1712_; lean_object* v_getEnv_1713_; lean_object* v___f_1714_; lean_object* v___f_1715_; lean_object* v___x_1716_; 
v_toApplicative_1709_ = lean_ctor_get(v_inst_1705_, 0);
v_toBind_1710_ = lean_ctor_get(v_inst_1705_, 1);
lean_inc_n(v_toBind_1710_, 2);
v_toPure_1711_ = lean_ctor_get(v_toApplicative_1709_, 1);
lean_inc_n(v_toPure_1711_, 2);
v_pre_1712_ = lean_ctor_get(v_declName_1708_, 0);
lean_inc(v_pre_1712_);
v_getEnv_1713_ = lean_ctor_get(v_inst_1706_, 0);
lean_inc_n(v_getEnv_1713_, 2);
lean_dec_ref(v_inst_1706_);
v___f_1714_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1714_, 0, v_toPure_1711_);
v___f_1715_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1715_, 0, v_pre_1712_);
lean_closure_set(v___f_1715_, 1, v_toPure_1711_);
lean_closure_set(v___f_1715_, 2, v_declName_1708_);
lean_closure_set(v___f_1715_, 3, v_inst_1705_);
lean_closure_set(v___f_1715_, 4, v_inst_1707_);
lean_closure_set(v___f_1715_, 5, v_toBind_1710_);
lean_closure_set(v___f_1715_, 6, v___f_1714_);
lean_closure_set(v___f_1715_, 7, v_getEnv_1713_);
v___x_1716_ = lean_apply_4(v_toBind_1710_, lean_box(0), lean_box(0), v_getEnv_1713_, v___f_1715_);
return v___x_1716_;
}
else
{
lean_object* v_toApplicative_1717_; lean_object* v_toPure_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v_toApplicative_1717_ = lean_ctor_get(v_inst_1705_, 0);
lean_inc_ref(v_toApplicative_1717_);
lean_dec(v_declName_1708_);
lean_dec_ref(v_inst_1707_);
lean_dec_ref(v_inst_1706_);
lean_dec_ref(v_inst_1705_);
v_toPure_1718_ = lean_ctor_get(v_toApplicative_1717_, 1);
lean_inc(v_toPure_1718_);
lean_dec_ref(v_toApplicative_1717_);
v___x_1719_ = lean_box(0);
v___x_1720_ = lean_apply_2(v_toPure_1718_, lean_box(0), v___x_1719_);
return v___x_1720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField(lean_object* v_m_1721_, lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_declName_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1722_, v_inst_1723_, v_inst_1724_, v_declName_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__0(lean_object* v_declName_1727_, lean_object* v_shortName_1728_, lean_object* v_toPure_1729_, lean_object* v_____r_1730_){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_declName_1727_);
lean_ctor_set(v___x_1731_, 1, v_shortName_1728_);
v___x_1732_ = lean_apply_2(v_toPure_1729_, lean_box(0), v___x_1731_);
return v___x_1732_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0));
v___x_1735_ = l_Lean_stringToMessageData(v___x_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2(lean_object* v_modifiers_1736_, lean_object* v_shortName_1737_, lean_object* v_toPure_1738_, lean_object* v_currNamespace_1739_, lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_toBind_1742_, lean_object* v_declName_1743_){
_start:
{
uint8_t v_isProtected_1744_; 
v_isProtected_1744_ = lean_ctor_get_uint8(v_modifiers_1736_, sizeof(void*)*3 + 1);
if (v_isProtected_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_dec(v_toBind_1742_);
lean_dec_ref(v_inst_1741_);
lean_dec_ref(v_inst_1740_);
lean_dec(v_currNamespace_1739_);
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v_declName_1743_);
lean_ctor_set(v___x_1745_, 1, v_shortName_1737_);
v___x_1746_ = lean_apply_2(v_toPure_1738_, lean_box(0), v___x_1745_);
return v___x_1746_;
}
else
{
if (lean_obj_tag(v_currNamespace_1739_) == 1)
{
lean_object* v_str_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec(v_toBind_1742_);
lean_dec_ref(v_inst_1741_);
lean_dec_ref(v_inst_1740_);
v_str_1747_ = lean_ctor_get(v_currNamespace_1739_, 1);
lean_inc_ref(v_str_1747_);
lean_dec_ref_known(v_currNamespace_1739_, 2);
v___x_1748_ = lean_box(0);
v___x_1749_ = l_Lean_Name_str___override(v___x_1748_, v_str_1747_);
v___x_1750_ = l_Lean_Name_append(v___x_1749_, v_shortName_1737_);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v_declName_1743_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = lean_apply_2(v_toPure_1738_, lean_box(0), v___x_1751_);
return v___x_1752_;
}
else
{
lean_object* v___f_1753_; uint8_t v___x_1754_; 
lean_dec(v_currNamespace_1739_);
lean_inc(v_toPure_1738_);
lean_inc(v_shortName_1737_);
lean_inc(v_declName_1743_);
v___f_1753_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1753_, 0, v_declName_1743_);
lean_closure_set(v___f_1753_, 1, v_shortName_1737_);
lean_closure_set(v___f_1753_, 2, v_toPure_1738_);
v___x_1754_ = l_Lean_Name_isAtomic(v_shortName_1737_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec_ref(v___f_1753_);
lean_dec(v_toBind_1742_);
lean_dec_ref(v_inst_1741_);
lean_dec_ref(v_inst_1740_);
v___x_1755_ = lean_box(0);
v___x_1756_ = l_Lean_Elab_mkDeclName___redArg___lam__0(v_declName_1743_, v_shortName_1737_, v_toPure_1738_, v___x_1755_);
return v___x_1756_;
}
else
{
lean_object* v___f_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v_declName_1743_);
lean_dec(v_toPure_1738_);
lean_dec(v_shortName_1737_);
v___f_1757_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1757_, 0, v___f_1753_);
v___x_1758_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_1759_ = l_Lean_throwError___redArg(v_inst_1740_, v_inst_1741_, v___x_1758_);
v___x_1760_ = lean_apply_4(v_toBind_1742_, lean_box(0), lean_box(0), v___x_1759_, v___f_1757_);
return v___x_1760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2___boxed(lean_object* v_modifiers_1761_, lean_object* v_shortName_1762_, lean_object* v_toPure_1763_, lean_object* v_currNamespace_1764_, lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_toBind_1767_, lean_object* v_declName_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_Elab_mkDeclName___redArg___lam__2(v_modifiers_1761_, v_shortName_1762_, v_toPure_1763_, v_currNamespace_1764_, v_inst_1765_, v_inst_1766_, v_toBind_1767_, v_declName_1768_);
lean_dec_ref(v_modifiers_1761_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__1(lean_object* v_inst_1770_, lean_object* v_inst_1771_, lean_object* v_inst_1772_, lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_modifiers_1775_, lean_object* v___y_1776_, lean_object* v_toBind_1777_, lean_object* v___f_1778_, lean_object* v_____r_1779_){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1770_, v_inst_1771_, v_inst_1772_, v_inst_1773_, v_inst_1774_, v_modifiers_1775_, v___y_1776_);
v___x_1781_ = lean_apply_4(v_toBind_1777_, lean_box(0), lean_box(0), v___x_1780_, v___f_1778_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3(lean_object* v_modifiers_1782_, lean_object* v_toPure_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_toBind_1786_, lean_object* v_inst_1787_, lean_object* v_inst_1788_, lean_object* v_inst_1789_, lean_object* v___y_1790_, lean_object* v_____r_1791_, lean_object* v_shortName_1792_, lean_object* v_currNamespace_1793_){
_start:
{
lean_object* v___f_1794_; lean_object* v___f_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_inc_n(v_toBind_1786_, 2);
lean_inc_ref_n(v_inst_1785_, 2);
lean_inc_ref_n(v_inst_1784_, 2);
lean_inc_ref(v_modifiers_1782_);
v___f_1794_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1794_, 0, v_modifiers_1782_);
lean_closure_set(v___f_1794_, 1, v_shortName_1792_);
lean_closure_set(v___f_1794_, 2, v_toPure_1783_);
lean_closure_set(v___f_1794_, 3, v_currNamespace_1793_);
lean_closure_set(v___f_1794_, 4, v_inst_1784_);
lean_closure_set(v___f_1794_, 5, v_inst_1785_);
lean_closure_set(v___f_1794_, 6, v_toBind_1786_);
lean_inc(v___y_1790_);
lean_inc_ref(v_inst_1787_);
v___f_1795_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1795_, 0, v_inst_1784_);
lean_closure_set(v___f_1795_, 1, v_inst_1787_);
lean_closure_set(v___f_1795_, 2, v_inst_1785_);
lean_closure_set(v___f_1795_, 3, v_inst_1788_);
lean_closure_set(v___f_1795_, 4, v_inst_1789_);
lean_closure_set(v___f_1795_, 5, v_modifiers_1782_);
lean_closure_set(v___f_1795_, 6, v___y_1790_);
lean_closure_set(v___f_1795_, 7, v_toBind_1786_);
lean_closure_set(v___f_1795_, 8, v___f_1794_);
v___x_1796_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1784_, v_inst_1787_, v_inst_1785_, v___y_1790_);
v___x_1797_ = lean_apply_4(v_toBind_1786_, lean_box(0), lean_box(0), v___x_1796_, v___f_1795_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__4(lean_object* v___f_1798_, lean_object* v_shortName_1799_, lean_object* v_currNamespace_1800_, lean_object* v_____r_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_apply_3(v___f_1798_, v_____r_1801_, v_shortName_1799_, v_currNamespace_1800_);
return v___x_1802_;
}
}
lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5(lean_object* v_modifiers_1803_, lean_object* v_toPure_1804_, lean_object* v_inst_1805_, lean_object* v_inst_1806_, lean_object* v_toBind_1807_, lean_object* v_inst_1808_, lean_object* v_inst_1809_, lean_object* v_inst_1810_, uint8_t v_isRootName_1811_, lean_object* v_shortName_1812_, lean_object* v_currNamespace_1813_, lean_object* v_name_1814_, lean_object* v___x_1815_, lean_object* v_imported_1816_, lean_object* v_ctx_1817_, lean_object* v_scopes_1818_, lean_object* v_____r_1819_){
_start:
{
lean_object* v___y_1821_; 
if (v_isRootName_1811_ == 0)
{
lean_object* v___x_1840_; 
lean_dec(v_scopes_1818_);
lean_dec(v_ctx_1817_);
lean_dec(v_imported_1816_);
lean_inc(v_shortName_1812_);
lean_inc(v_currNamespace_1813_);
v___x_1840_ = l_Lean_Name_append(v_currNamespace_1813_, v_shortName_1812_);
v___y_1821_ = v___x_1840_;
goto v___jp_1820_;
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1841_ = lean_box(0);
lean_inc(v_name_1814_);
v___x_1842_ = l_Lean_Name_replacePrefix(v_name_1814_, v___x_1815_, v___x_1841_);
v___x_1843_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v_imported_1816_);
lean_ctor_set(v___x_1843_, 2, v_ctx_1817_);
lean_ctor_set(v___x_1843_, 3, v_scopes_1818_);
v___x_1844_ = l_Lean_MacroScopesView_review(v___x_1843_);
v___y_1821_ = v___x_1844_;
goto v___jp_1820_;
}
v___jp_1820_:
{
lean_object* v___f_1822_; 
lean_inc(v___y_1821_);
lean_inc_ref(v_inst_1810_);
lean_inc(v_inst_1809_);
lean_inc_ref(v_inst_1808_);
lean_inc(v_toBind_1807_);
lean_inc_ref(v_inst_1806_);
lean_inc_ref(v_inst_1805_);
lean_inc(v_toPure_1804_);
lean_inc_ref(v_modifiers_1803_);
v___f_1822_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__3), 12, 9);
lean_closure_set(v___f_1822_, 0, v_modifiers_1803_);
lean_closure_set(v___f_1822_, 1, v_toPure_1804_);
lean_closure_set(v___f_1822_, 2, v_inst_1805_);
lean_closure_set(v___f_1822_, 3, v_inst_1806_);
lean_closure_set(v___f_1822_, 4, v_toBind_1807_);
lean_closure_set(v___f_1822_, 5, v_inst_1808_);
lean_closure_set(v___f_1822_, 6, v_inst_1809_);
lean_closure_set(v___f_1822_, 7, v_inst_1810_);
lean_closure_set(v___f_1822_, 8, v___y_1821_);
if (v_isRootName_1811_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec_ref(v___f_1822_);
lean_dec(v_name_1814_);
v___x_1823_ = lean_box(0);
v___x_1824_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1803_, v_toPure_1804_, v_inst_1805_, v_inst_1806_, v_toBind_1807_, v_inst_1808_, v_inst_1809_, v_inst_1810_, v___y_1821_, v___x_1823_, v_shortName_1812_, v_currNamespace_1813_);
return v___x_1824_;
}
else
{
if (lean_obj_tag(v_name_1814_) == 1)
{
lean_object* v_pre_1825_; lean_object* v_str_1826_; lean_object* v___x_1827_; lean_object* v_shortName_1828_; lean_object* v_currNamespace_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec_ref(v___f_1822_);
lean_dec(v_currNamespace_1813_);
lean_dec(v_shortName_1812_);
v_pre_1825_ = lean_ctor_get(v_name_1814_, 0);
lean_inc(v_pre_1825_);
v_str_1826_ = lean_ctor_get(v_name_1814_, 1);
lean_inc_ref(v_str_1826_);
lean_dec_ref_known(v_name_1814_, 2);
v___x_1827_ = lean_box(0);
v_shortName_1828_ = l_Lean_Name_str___override(v___x_1827_, v_str_1826_);
v_currNamespace_1829_ = l_Lean_Name_replacePrefix(v_pre_1825_, v___x_1815_, v___x_1827_);
v___x_1830_ = lean_box(0);
v___x_1831_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1803_, v_toPure_1804_, v_inst_1805_, v_inst_1806_, v_toBind_1807_, v_inst_1808_, v_inst_1809_, v_inst_1810_, v___y_1821_, v___x_1830_, v_shortName_1828_, v_currNamespace_1829_);
return v___x_1831_;
}
else
{
lean_object* v___f_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec(v___y_1821_);
lean_dec_ref(v_inst_1810_);
lean_dec(v_inst_1809_);
lean_dec_ref(v_inst_1808_);
lean_dec(v_toPure_1804_);
lean_dec_ref(v_modifiers_1803_);
v___f_1832_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__4), 4, 3);
lean_closure_set(v___f_1832_, 0, v___f_1822_);
lean_closure_set(v___f_1832_, 1, v_shortName_1812_);
lean_closure_set(v___f_1832_, 2, v_currNamespace_1813_);
v___x_1833_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1834_ = l_Lean_MessageData_ofName(v_name_1814_);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1835_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = l_Lean_throwError___redArg(v_inst_1805_, v_inst_1806_, v___x_1837_);
v___x_1839_ = lean_apply_4(v_toBind_1807_, lean_box(0), lean_box(0), v___x_1838_, v___f_1832_);
return v___x_1839_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_mkDeclName___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_modifiers_1803_ = stack[0].m_obj;
lean_object* v_toPure_1804_ = stack[1].m_obj;
lean_object* v_inst_1805_ = stack[2].m_obj;
lean_object* v_inst_1806_ = stack[3].m_obj;
lean_object* v_toBind_1807_ = stack[4].m_obj;
lean_object* v_inst_1808_ = stack[5].m_obj;
lean_object* v_inst_1809_ = stack[6].m_obj;
lean_object* v_inst_1810_ = stack[7].m_obj;
uint8_t v_isRootName_1811_ = stack[8].m_num;
lean_object* v_shortName_1812_ = stack[9].m_obj;
lean_object* v_currNamespace_1813_ = stack[10].m_obj;
lean_object* v_name_1814_ = stack[11].m_obj;
lean_object* v___x_1815_ = stack[12].m_obj;
lean_object* v_imported_1816_ = stack[13].m_obj;
lean_object* v_ctx_1817_ = stack[14].m_obj;
lean_object* v_scopes_1818_ = stack[15].m_obj;
lean_object* v_____r_1819_ = stack[16].m_obj;
lean_object* v_res_1845_;
v_res_1845_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1803_, v_toPure_1804_, v_inst_1805_, v_inst_1806_, v_toBind_1807_, v_inst_1808_, v_inst_1809_, v_inst_1810_, v_isRootName_1811_, v_shortName_1812_, v_currNamespace_1813_, v_name_1814_, v___x_1815_, v_imported_1816_, v_ctx_1817_, v_scopes_1818_, v_____r_1819_);
stack->m_obj
 = v_res_1845_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_modifiers_1846_ = _args[0];
lean_object* v_toPure_1847_ = _args[1];
lean_object* v_inst_1848_ = _args[2];
lean_object* v_inst_1849_ = _args[3];
lean_object* v_toBind_1850_ = _args[4];
lean_object* v_inst_1851_ = _args[5];
lean_object* v_inst_1852_ = _args[6];
lean_object* v_inst_1853_ = _args[7];
lean_object* v_isRootName_1854_ = _args[8];
lean_object* v_shortName_1855_ = _args[9];
lean_object* v_currNamespace_1856_ = _args[10];
lean_object* v_name_1857_ = _args[11];
lean_object* v___x_1858_ = _args[12];
lean_object* v_imported_1859_ = _args[13];
lean_object* v_ctx_1860_ = _args[14];
lean_object* v_scopes_1861_ = _args[15];
lean_object* v_____r_1862_ = _args[16];
_start:
{
uint8_t v_isRootName_boxed_1863_; lean_object* v_res_1864_; 
v_isRootName_boxed_1863_ = lean_unbox(v_isRootName_1854_);
v_res_1864_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1846_, v_toPure_1847_, v_inst_1848_, v_inst_1849_, v_toBind_1850_, v_inst_1851_, v_inst_1852_, v_inst_1853_, v_isRootName_boxed_1863_, v_shortName_1855_, v_currNamespace_1856_, v_name_1857_, v___x_1858_, v_imported_1859_, v_ctx_1860_, v_scopes_1861_, v_____r_1862_);
lean_dec(v___x_1858_);
return v_res_1864_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___closed__3(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__2));
v___x_1870_ = l_Lean_stringToMessageData(v___x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg(lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_inst_1875_, lean_object* v_currNamespace_1876_, lean_object* v_modifiers_1877_, lean_object* v_shortName_1878_){
_start:
{
lean_object* v_view_1879_; lean_object* v_toApplicative_1880_; lean_object* v_name_1881_; lean_object* v_imported_1882_; lean_object* v_ctx_1883_; lean_object* v_scopes_1884_; lean_object* v_toBind_1885_; lean_object* v_toPure_1886_; lean_object* v___x_1887_; uint8_t v_isRootName_1888_; lean_object* v___x_1889_; lean_object* v___f_1890_; uint8_t v___x_1891_; 
lean_inc_n(v_shortName_1878_, 2);
v_view_1879_ = l_Lean_extractMacroScopes(v_shortName_1878_);
v_toApplicative_1880_ = lean_ctor_get(v_inst_1871_, 0);
v_name_1881_ = lean_ctor_get(v_view_1879_, 0);
lean_inc_n(v_name_1881_, 2);
v_imported_1882_ = lean_ctor_get(v_view_1879_, 1);
lean_inc_n(v_imported_1882_, 2);
v_ctx_1883_ = lean_ctor_get(v_view_1879_, 2);
lean_inc_n(v_ctx_1883_, 2);
v_scopes_1884_ = lean_ctor_get(v_view_1879_, 3);
lean_inc_n(v_scopes_1884_, 2);
lean_dec_ref(v_view_1879_);
v_toBind_1885_ = lean_ctor_get(v_inst_1871_, 1);
lean_inc_n(v_toBind_1885_, 2);
v_toPure_1886_ = lean_ctor_get(v_toApplicative_1880_, 1);
v___x_1887_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_1888_ = l_Lean_Name_isPrefixOf(v___x_1887_, v_name_1881_);
v___x_1889_ = lean_box(v_isRootName_1888_);
lean_inc(v_currNamespace_1876_);
lean_inc_ref(v_inst_1875_);
lean_inc(v_inst_1874_);
lean_inc_ref(v_inst_1872_);
lean_inc_ref(v_inst_1873_);
lean_inc_ref(v_inst_1871_);
lean_inc(v_toPure_1886_);
lean_inc_ref(v_modifiers_1877_);
v___f_1890_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1890_, 0, v_modifiers_1877_);
lean_closure_set(v___f_1890_, 1, v_toPure_1886_);
lean_closure_set(v___f_1890_, 2, v_inst_1871_);
lean_closure_set(v___f_1890_, 3, v_inst_1873_);
lean_closure_set(v___f_1890_, 4, v_toBind_1885_);
lean_closure_set(v___f_1890_, 5, v_inst_1872_);
lean_closure_set(v___f_1890_, 6, v_inst_1874_);
lean_closure_set(v___f_1890_, 7, v_inst_1875_);
lean_closure_set(v___f_1890_, 8, v___x_1889_);
lean_closure_set(v___f_1890_, 9, v_shortName_1878_);
lean_closure_set(v___f_1890_, 10, v_currNamespace_1876_);
lean_closure_set(v___f_1890_, 11, v_name_1881_);
lean_closure_set(v___f_1890_, 12, v___x_1887_);
lean_closure_set(v___f_1890_, 13, v_imported_1882_);
lean_closure_set(v___f_1890_, 14, v_ctx_1883_);
lean_closure_set(v___f_1890_, 15, v_scopes_1884_);
v___x_1891_ = lean_name_eq(v_name_1881_, v___x_1887_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_inc(v_toPure_1886_);
lean_dec_ref(v___f_1890_);
v___x_1892_ = lean_box(0);
v___x_1893_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1877_, v_toPure_1886_, v_inst_1871_, v_inst_1873_, v_toBind_1885_, v_inst_1872_, v_inst_1874_, v_inst_1875_, v_isRootName_1888_, v_shortName_1878_, v_currNamespace_1876_, v_name_1881_, v___x_1887_, v_imported_1882_, v_ctx_1883_, v_scopes_1884_, v___x_1892_);
return v___x_1893_;
}
else
{
lean_object* v___f_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec(v_scopes_1884_);
lean_dec(v_ctx_1883_);
lean_dec(v_imported_1882_);
lean_dec(v_name_1881_);
lean_dec(v_shortName_1878_);
lean_dec_ref(v_modifiers_1877_);
lean_dec(v_currNamespace_1876_);
lean_dec_ref(v_inst_1875_);
lean_dec(v_inst_1874_);
lean_dec_ref(v_inst_1872_);
v___f_1894_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1894_, 0, v___f_1890_);
v___x_1895_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_1896_ = l_Lean_throwError___redArg(v_inst_1871_, v_inst_1873_, v___x_1895_);
v___x_1897_ = lean_apply_4(v_toBind_1885_, lean_box(0), lean_box(0), v___x_1896_, v___f_1894_);
return v___x_1897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName(lean_object* v_m_1898_, lean_object* v_inst_1899_, lean_object* v_inst_1900_, lean_object* v_inst_1901_, lean_object* v_inst_1902_, lean_object* v_inst_1903_, lean_object* v_currNamespace_1904_, lean_object* v_modifiers_1905_, lean_object* v_shortName_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_Elab_mkDeclName___redArg(v_inst_1899_, v_inst_1900_, v_inst_1901_, v_inst_1902_, v_inst_1903_, v_currNamespace_1904_, v_modifiers_1905_, v_shortName_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore(lean_object* v_declId_1917_){
_start:
{
uint8_t v___x_1918_; 
v___x_1918_ = l_Lean_Syntax_isIdent(v_declId_1917_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v_id_1921_; lean_object* v___x_1922_; lean_object* v_optUnivDeclStx_1923_; lean_object* v___x_1924_; 
v___x_1919_ = lean_unsigned_to_nat(0u);
v___x_1920_ = l_Lean_Syntax_getArg(v_declId_1917_, v___x_1919_);
v_id_1921_ = l_Lean_Syntax_getId(v___x_1920_);
lean_dec(v___x_1920_);
v___x_1922_ = lean_unsigned_to_nat(1u);
v_optUnivDeclStx_1923_ = l_Lean_Syntax_getArg(v_declId_1917_, v___x_1922_);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v_id_1921_);
lean_ctor_set(v___x_1924_, 1, v_optUnivDeclStx_1923_);
return v___x_1924_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = l_Lean_Syntax_getId(v_declId_1917_);
v___x_1926_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__3));
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
return v___x_1927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore___boxed(lean_object* v_declId_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_Elab_expandDeclIdCore(v_declId_1928_);
lean_dec(v_declId_1928_);
return v_res_1929_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(lean_object* v_msgData_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v___x_1936_; lean_object* v_env_1937_; uint8_t v___x_1938_; lean_object* v_env_1939_; lean_object* v___x_1940_; lean_object* v_toCold_1941_; lean_object* v_mctx_1942_; lean_object* v_lctx_1943_; lean_object* v_options_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1936_ = lean_st_ref_get(v___y_1934_);
v_env_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc_ref(v_env_1937_);
lean_dec(v___x_1936_);
v___x_1938_ = 0;
v_env_1939_ = l_Lean_Environment_setRecordingDeps(v_env_1937_, v___x_1938_);
v___x_1940_ = lean_st_ref_get(v___y_1932_);
v_toCold_1941_ = lean_ctor_get(v___y_1933_, 0);
v_mctx_1942_ = lean_ctor_get(v___x_1940_, 0);
lean_inc_ref(v_mctx_1942_);
lean_dec(v___x_1940_);
v_lctx_1943_ = lean_ctor_get(v___y_1931_, 2);
v_options_1944_ = lean_ctor_get(v_toCold_1941_, 2);
lean_inc_ref(v_options_1944_);
lean_inc_ref(v_lctx_1943_);
v___x_1945_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1945_, 0, v_env_1939_);
lean_ctor_set(v___x_1945_, 1, v_mctx_1942_);
lean_ctor_set(v___x_1945_, 2, v_lctx_1943_);
lean_ctor_set(v___x_1945_, 3, v_options_1944_);
v___x_1946_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
lean_ctor_set(v___x_1946_, 1, v_msgData_1930_);
v___x_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1930_ = stack[0].m_obj;
lean_object* v___y_1931_ = stack[1].m_obj;
lean_object* v___y_1932_ = stack[2].m_obj;
lean_object* v___y_1933_ = stack[3].m_obj;
lean_object* v___y_1934_ = stack[4].m_obj;
lean_object* v_res_1948_;
v_res_1948_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msgData_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
stack->m_obj
 = v_res_1948_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msgData_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
return v_res_1955_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(lean_object* v_opts_1956_, lean_object* v_opt_1957_){
_start:
{
lean_object* v_name_1958_; lean_object* v_defValue_1959_; lean_object* v_map_1960_; lean_object* v___x_1961_; 
v_name_1958_ = lean_ctor_get(v_opt_1957_, 0);
v_defValue_1959_ = lean_ctor_get(v_opt_1957_, 1);
v_map_1960_ = lean_ctor_get(v_opts_1956_, 0);
v___x_1961_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1960_, v_name_1958_);
if (lean_obj_tag(v___x_1961_) == 0)
{
uint8_t v___x_1962_; 
v___x_1962_ = lean_unbox(v_defValue_1959_);
return v___x_1962_;
}
else
{
lean_object* v_val_1963_; 
v_val_1963_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_val_1963_);
lean_dec_ref_known(v___x_1961_, 1);
if (lean_obj_tag(v_val_1963_) == 1)
{
uint8_t v_v_1964_; 
v_v_1964_ = lean_ctor_get_uint8(v_val_1963_, 0);
lean_dec_ref_known(v_val_1963_, 0);
return v_v_1964_;
}
else
{
uint8_t v___x_1965_; 
lean_dec(v_val_1963_);
v___x_1965_ = lean_unbox(v_defValue_1959_);
return v___x_1965_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1956_ = stack[0].m_obj;
lean_object* v_opt_1957_ = stack[1].m_obj;
uint8_t v_res_1966_;
v_res_1966_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_opts_1956_, v_opt_1957_);
stack->m_num = v_res_1966_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_opts_1967_, lean_object* v_opt_1968_){
_start:
{
uint8_t v_res_1969_; lean_object* v_r_1970_; 
v_res_1969_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_opts_1967_, v_opt_1968_);
lean_dec_ref(v_opt_1968_);
lean_dec_ref(v_opts_1967_);
v_r_1970_ = lean_box(v_res_1969_);
return v_r_1970_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = lean_box(1);
v___x_1972_ = l_Lean_MessageData_ofFormat(v___x_1971_);
return v___x_1972_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2));
v___x_1977_ = l_Lean_MessageData_ofFormat(v___x_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(lean_object* v_x_1978_, lean_object* v_x_1979_){
_start:
{
if (lean_obj_tag(v_x_1979_) == 0)
{
return v_x_1978_;
}
else
{
lean_object* v_head_1980_; lean_object* v_tail_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2003_; 
v_head_1980_ = lean_ctor_get(v_x_1979_, 0);
v_tail_1981_ = lean_ctor_get(v_x_1979_, 1);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_x_1979_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1983_ = v_x_1979_;
v_isShared_1984_ = v_isSharedCheck_2003_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_tail_1981_);
lean_inc(v_head_1980_);
lean_dec(v_x_1979_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2003_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_before_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2001_; 
v_before_1985_ = lean_ctor_get(v_head_1980_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_head_1980_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; 
v_unused_2002_ = lean_ctor_get(v_head_1980_, 1);
lean_dec(v_unused_2002_);
v___x_1987_ = v_head_1980_;
v_isShared_1988_ = v_isSharedCheck_2001_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_before_1985_);
lean_dec(v_head_1980_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2001_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1989_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 7);
lean_ctor_set(v___x_1987_, 1, v___x_1989_);
lean_ctor_set(v___x_1987_, 0, v_x_1978_);
v___x_1991_ = v___x_1987_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_x_1978_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1992_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3);
if (v_isShared_1984_ == 0)
{
lean_ctor_set_tag(v___x_1983_, 7);
lean_ctor_set(v___x_1983_, 1, v___x_1992_);
lean_ctor_set(v___x_1983_, 0, v___x_1991_);
v___x_1994_ = v___x_1983_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = l_Lean_MessageData_ofSyntax(v_before_1985_);
v___x_1996_ = l_Lean_indentD(v___x_1995_);
v___x_1997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1994_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v_x_1978_ = v___x_1997_;
v_x_1979_ = v_tail_1981_;
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
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1));
v___x_2008_ = l_Lean_MessageData_ofFormat(v___x_2007_);
return v___x_2008_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_2009_, lean_object* v_macroStack_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2013_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2011_);
v___x_2014_ = l_Lean_Elab_pp_macroStack;
v___x_2015_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v___x_2013_, v___x_2014_);
lean_dec_ref(v___x_2013_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; 
lean_dec(v_macroStack_2010_);
v___x_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2016_, 0, v_msgData_2009_);
return v___x_2016_;
}
else
{
if (lean_obj_tag(v_macroStack_2010_) == 0)
{
lean_object* v___x_2017_; 
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v_msgData_2009_);
return v___x_2017_;
}
else
{
lean_object* v_head_2018_; lean_object* v_after_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2034_; 
v_head_2018_ = lean_ctor_get(v_macroStack_2010_, 0);
lean_inc(v_head_2018_);
v_after_2019_ = lean_ctor_get(v_head_2018_, 1);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_head_2018_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; 
v_unused_2035_ = lean_ctor_get(v_head_2018_, 0);
lean_dec(v_unused_2035_);
v___x_2021_ = v_head_2018_;
v_isShared_2022_ = v_isSharedCheck_2034_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_after_2019_);
lean_dec(v_head_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2034_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2023_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_2022_ == 0)
{
lean_ctor_set_tag(v___x_2021_, 7);
lean_ctor_set(v___x_2021_, 1, v___x_2023_);
lean_ctor_set(v___x_2021_, 0, v_msgData_2009_);
v___x_2025_ = v___x_2021_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_msgData_2009_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v_msgData_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2026_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_2027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2025_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v___x_2028_ = l_Lean_MessageData_ofSyntax(v_after_2019_);
v___x_2029_ = l_Lean_indentD(v___x_2028_);
v_msgData_2030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2030_, 0, v___x_2027_);
lean_ctor_set(v_msgData_2030_, 1, v___x_2029_);
v___x_2031_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(v_msgData_2030_, v_macroStack_2010_);
v___x_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
return v___x_2032_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2009_ = stack[0].m_obj;
lean_object* v_macroStack_2010_ = stack[1].m_obj;
lean_object* v___y_2011_ = stack[2].m_obj;
lean_object* v_res_2036_;
v_res_2036_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_2009_, v_macroStack_2010_, v___y_2011_);
stack->m_obj
 = v_res_2036_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_2037_, lean_object* v_macroStack_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_2037_, v_macroStack_2038_, v___y_2039_);
lean_dec_ref(v___y_2039_);
return v_res_2041_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(lean_object* v_msg_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_ref_2050_; lean_object* v_macroStack_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v_a_2054_; lean_object* v___x_2055_; lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2064_; 
v_ref_2050_ = lean_ctor_get(v___y_2047_, 2);
v_macroStack_2051_ = lean_ctor_get(v___y_2043_, 1);
v___x_2052_ = l_Lean_Elab_getBetterRef(v_ref_2050_, v_macroStack_2051_);
v___x_2053_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msg_2042_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref(v___x_2053_);
lean_inc(v_macroStack_2051_);
v___x_2055_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_a_2054_, v_macroStack_2051_, v___y_2047_);
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2052_);
lean_ctor_set(v___x_2060_, 1, v_a_2056_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set_tag(v___x_2058_, 1);
lean_ctor_set(v___x_2058_, 0, v___x_2060_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2042_ = stack[0].m_obj;
lean_object* v___y_2043_ = stack[1].m_obj;
lean_object* v___y_2044_ = stack[2].m_obj;
lean_object* v___y_2045_ = stack[3].m_obj;
lean_object* v___y_2046_ = stack[4].m_obj;
lean_object* v___y_2047_ = stack[5].m_obj;
lean_object* v___y_2048_ = stack[6].m_obj;
lean_object* v_res_2065_;
v_res_2065_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
stack->m_obj
 = v_res_2065_;
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
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(lean_object* v_env_2075_, lean_object* v_declName_2076_, lean_object* v___f_2077_, lean_object* v_addInfo_2078_, lean_object* v_____r_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; uint8_t v___x_2088_; uint8_t v___x_2089_; 
lean_inc(v_declName_2076_);
v___x_2087_ = l_Lean_mkPrivateName(v_env_2075_, v_declName_2076_);
v___x_2088_ = 1;
lean_inc(v___x_2087_);
v___x_2089_ = l_Lean_Environment_contains(v_env_2075_, v___x_2087_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_dec(v___x_2087_);
lean_dec_ref(v_addInfo_2078_);
lean_dec(v_declName_2076_);
v___x_2090_ = lean_box(0);
lean_inc(v___y_2085_);
lean_inc_ref(v___y_2084_);
lean_inc(v___y_2083_);
lean_inc_ref(v___y_2082_);
lean_inc(v___y_2081_);
lean_inc_ref(v___y_2080_);
v___x_2091_ = lean_apply_8(v___f_2077_, v___x_2090_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, lean_box(0));
return v___x_2091_;
}
else
{
lean_object* v___x_2092_; 
lean_dec_ref(v___f_2077_);
lean_inc(v___y_2085_);
lean_inc_ref(v___y_2084_);
lean_inc(v___y_2083_);
lean_inc_ref(v___y_2082_);
lean_inc(v___y_2081_);
lean_inc_ref(v___y_2080_);
v___x_2092_ = lean_apply_8(v_addInfo_2078_, v___x_2087_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, lean_box(0));
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_dec_ref_known(v___x_2092_, 1);
v___x_2093_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1);
v___x_2094_ = l_Lean_MessageData_ofConstName(v_declName_2076_, v___x_2088_);
v___x_2095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2093_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
v___x_2096_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2095_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2097_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
return v___x_2098_;
}
else
{
lean_dec(v_declName_2076_);
return v___x_2092_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2075_ = stack[0].m_obj;
lean_object* v_declName_2076_ = stack[1].m_obj;
lean_object* v___f_2077_ = stack[2].m_obj;
lean_object* v_addInfo_2078_ = stack[3].m_obj;
lean_object* v_____r_2079_ = stack[4].m_obj;
lean_object* v___y_2080_ = stack[5].m_obj;
lean_object* v___y_2081_ = stack[6].m_obj;
lean_object* v___y_2082_ = stack[7].m_obj;
lean_object* v___y_2083_ = stack[8].m_obj;
lean_object* v___y_2084_ = stack[9].m_obj;
lean_object* v___y_2085_ = stack[10].m_obj;
lean_object* v_res_2099_;
v_res_2099_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(v_env_2075_, v_declName_2076_, v___f_2077_, v_addInfo_2078_, v_____r_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
stack->m_obj
 = v_res_2099_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed(lean_object* v_env_2100_, lean_object* v_declName_2101_, lean_object* v___f_2102_, lean_object* v_addInfo_2103_, lean_object* v_____r_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(v_env_2100_, v_declName_2101_, v___f_2102_, v_addInfo_2103_, v_____r_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2112_;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(lean_object* v___f_2113_, lean_object* v_declName_2114_, uint8_t v___x_2115_, lean_object* v_env_2116_, lean_object* v_____do__lift_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
uint8_t v___y_2126_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
lean_inc(v_declName_2114_);
v___x_2135_ = l_Lean_privateToUserName(v_declName_2114_);
lean_inc_ref(v_env_2116_);
v___x_2136_ = lean_is_reserved_name(v_env_2116_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
lean_inc(v_declName_2114_);
v___x_2137_ = l_Lean_mkPrivateName(v_____do__lift_2117_, v_declName_2114_);
v___x_2138_ = lean_is_reserved_name(v_env_2116_, v___x_2137_);
v___y_2126_ = v___x_2138_;
goto v___jp_2125_;
}
else
{
lean_dec_ref(v_env_2116_);
v___y_2126_ = v___x_2136_;
goto v___jp_2125_;
}
v___jp_2125_:
{
if (v___y_2126_ == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec(v_declName_2114_);
v___x_2127_ = lean_box(0);
lean_inc(v___y_2123_);
lean_inc_ref(v___y_2122_);
lean_inc(v___y_2121_);
lean_inc_ref(v___y_2120_);
lean_inc(v___y_2119_);
lean_inc_ref(v___y_2118_);
v___x_2128_ = lean_apply_8(v___f_2113_, v___x_2127_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, lean_box(0));
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_dec_ref(v___f_2113_);
v___x_2129_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2130_ = l_Lean_MessageData_ofConstName(v_declName_2114_, v___x_2115_);
v___x_2131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2129_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3);
v___x_2133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2131_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2133_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
return v___x_2134_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2113_ = stack[0].m_obj;
lean_object* v_declName_2114_ = stack[1].m_obj;
uint8_t v___x_2115_ = stack[2].m_num;
lean_object* v_env_2116_ = stack[3].m_obj;
lean_object* v_____do__lift_2117_ = stack[4].m_obj;
lean_object* v___y_2118_ = stack[5].m_obj;
lean_object* v___y_2119_ = stack[6].m_obj;
lean_object* v___y_2120_ = stack[7].m_obj;
lean_object* v___y_2121_ = stack[8].m_obj;
lean_object* v___y_2122_ = stack[9].m_obj;
lean_object* v___y_2123_ = stack[10].m_obj;
lean_object* v_res_2139_;
v_res_2139_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(v___f_2113_, v_declName_2114_, v___x_2115_, v_env_2116_, v_____do__lift_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
stack->m_obj
 = v_res_2139_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed(lean_object* v___f_2140_, lean_object* v_declName_2141_, lean_object* v___x_2142_, lean_object* v_env_2143_, lean_object* v_____do__lift_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
uint8_t v___x_16754__boxed_2152_; lean_object* v_res_2153_; 
v___x_16754__boxed_2152_ = lean_unbox(v___x_2142_);
v_res_2153_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(v___f_2140_, v_declName_2141_, v___x_16754__boxed_2152_, v_env_2143_, v_____do__lift_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec_ref(v_____do__lift_2144_);
return v_res_2153_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(lean_object* v_t_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; lean_object* v_infoState_2158_; uint8_t v_enabled_2159_; 
v___x_2157_ = lean_st_ref_get(v___y_2155_);
v_infoState_2158_ = lean_ctor_get(v___x_2157_, 8);
lean_inc_ref(v_infoState_2158_);
lean_dec(v___x_2157_);
v_enabled_2159_ = lean_ctor_get_uint8(v_infoState_2158_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2158_);
if (v_enabled_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_dec_ref(v_t_2154_);
v___x_2160_ = lean_box(0);
v___x_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
return v___x_2161_;
}
else
{
lean_object* v___x_2162_; lean_object* v_infoState_2163_; lean_object* v_env_2164_; lean_object* v_nextMacroScope_2165_; lean_object* v_ngen_2166_; lean_object* v_auxDeclNGen_2167_; lean_object* v_traceState_2168_; lean_object* v_cache_2169_; lean_object* v_recordedDeps_2170_; lean_object* v_messages_2171_; lean_object* v_snapshotTasks_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2194_; 
v___x_2162_ = lean_st_ref_take(v___y_2155_);
v_infoState_2163_ = lean_ctor_get(v___x_2162_, 8);
v_env_2164_ = lean_ctor_get(v___x_2162_, 0);
v_nextMacroScope_2165_ = lean_ctor_get(v___x_2162_, 1);
v_ngen_2166_ = lean_ctor_get(v___x_2162_, 2);
v_auxDeclNGen_2167_ = lean_ctor_get(v___x_2162_, 3);
v_traceState_2168_ = lean_ctor_get(v___x_2162_, 4);
v_cache_2169_ = lean_ctor_get(v___x_2162_, 5);
v_recordedDeps_2170_ = lean_ctor_get(v___x_2162_, 6);
v_messages_2171_ = lean_ctor_get(v___x_2162_, 7);
v_snapshotTasks_2172_ = lean_ctor_get(v___x_2162_, 9);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2174_ = v___x_2162_;
v_isShared_2175_ = v_isSharedCheck_2194_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_snapshotTasks_2172_);
lean_inc(v_infoState_2163_);
lean_inc(v_messages_2171_);
lean_inc(v_recordedDeps_2170_);
lean_inc(v_cache_2169_);
lean_inc(v_traceState_2168_);
lean_inc(v_auxDeclNGen_2167_);
lean_inc(v_ngen_2166_);
lean_inc(v_nextMacroScope_2165_);
lean_inc(v_env_2164_);
lean_dec(v___x_2162_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2194_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
uint8_t v_enabled_2176_; lean_object* v_assignment_2177_; lean_object* v_lazyAssignment_2178_; lean_object* v_trees_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2193_; 
v_enabled_2176_ = lean_ctor_get_uint8(v_infoState_2163_, sizeof(void*)*3);
v_assignment_2177_ = lean_ctor_get(v_infoState_2163_, 0);
v_lazyAssignment_2178_ = lean_ctor_get(v_infoState_2163_, 1);
v_trees_2179_ = lean_ctor_get(v_infoState_2163_, 2);
v_isSharedCheck_2193_ = !lean_is_exclusive(v_infoState_2163_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2181_ = v_infoState_2163_;
v_isShared_2182_ = v_isSharedCheck_2193_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_trees_2179_);
lean_inc(v_lazyAssignment_2178_);
lean_inc(v_assignment_2177_);
lean_dec(v_infoState_2163_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2193_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2183_ = lean_box(0);
v___x_2184_ = l_Lean_PersistentArray_push___redArg(v_trees_2179_, v_t_2154_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 2, v___x_2184_);
v___x_2186_ = v___x_2181_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_assignment_2177_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_lazyAssignment_2178_);
lean_ctor_set(v_reuseFailAlloc_2192_, 2, v___x_2184_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, sizeof(void*)*3, v_enabled_2176_);
v___x_2186_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2188_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 8, v___x_2186_);
v___x_2188_ = v___x_2174_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_env_2164_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_nextMacroScope_2165_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_ngen_2166_);
lean_ctor_set(v_reuseFailAlloc_2191_, 3, v_auxDeclNGen_2167_);
lean_ctor_set(v_reuseFailAlloc_2191_, 4, v_traceState_2168_);
lean_ctor_set(v_reuseFailAlloc_2191_, 5, v_cache_2169_);
lean_ctor_set(v_reuseFailAlloc_2191_, 6, v_recordedDeps_2170_);
lean_ctor_set(v_reuseFailAlloc_2191_, 7, v_messages_2171_);
lean_ctor_set(v_reuseFailAlloc_2191_, 8, v___x_2186_);
lean_ctor_set(v_reuseFailAlloc_2191_, 9, v_snapshotTasks_2172_);
v___x_2188_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = lean_st_ref_put(v___y_2155_, v___x_2188_);
v___x_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2183_);
return v___x_2190_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2154_ = stack[0].m_obj;
lean_object* v___y_2155_ = stack[1].m_obj;
lean_object* v_res_2195_;
v_res_2195_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_2154_, v___y_2155_);
stack->m_obj
 = v_res_2195_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg___boxed(lean_object* v_t_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_2196_, v___y_2197_);
lean_dec(v___y_2197_);
return v_res_2199_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = lean_unsigned_to_nat(32u);
v___x_2201_ = lean_mk_empty_array_with_capacity(v___x_2200_);
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1(void){
_start:
{
size_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2203_ = ((size_t)5ULL);
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = lean_unsigned_to_nat(32u);
v___x_2206_ = lean_mk_empty_array_with_capacity(v___x_2205_);
v___x_2207_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0);
v___x_2208_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___x_2206_);
lean_ctor_set(v___x_2208_, 2, v___x_2204_);
lean_ctor_set(v___x_2208_, 3, v___x_2204_);
lean_ctor_set_usize(v___x_2208_, 4, v___x_2203_);
return v___x_2208_;
}
}
lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(lean_object* v_t_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___x_2217_; lean_object* v_infoState_2218_; uint8_t v_enabled_2219_; 
v___x_2217_ = lean_st_ref_get(v___y_2215_);
v_infoState_2218_ = lean_ctor_get(v___x_2217_, 8);
lean_inc_ref(v_infoState_2218_);
lean_dec(v___x_2217_);
v_enabled_2219_ = lean_ctor_get_uint8(v_infoState_2218_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2218_);
if (v_enabled_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_dec_ref(v_t_2209_);
v___x_2220_ = lean_box(0);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
else
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1);
v___x_2223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2223_, 0, v_t_2209_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v___x_2223_, v___y_2215_);
return v___x_2224_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2209_ = stack[0].m_obj;
lean_object* v___y_2210_ = stack[1].m_obj;
lean_object* v___y_2211_ = stack[2].m_obj;
lean_object* v___y_2212_ = stack[3].m_obj;
lean_object* v___y_2213_ = stack[4].m_obj;
lean_object* v___y_2214_ = stack[5].m_obj;
lean_object* v___y_2215_ = stack[6].m_obj;
lean_object* v_res_2225_;
v_res_2225_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v_t_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
stack->m_obj
 = v_res_2225_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___boxed(lean_object* v_t_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v_t_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
if (lean_obj_tag(v_a_2235_) == 0)
{
lean_object* v___x_2237_; 
v___x_2237_ = l_List_reverse___redArg(v_a_2236_);
return v___x_2237_;
}
else
{
lean_object* v_head_2238_; lean_object* v_tail_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2248_; 
v_head_2238_ = lean_ctor_get(v_a_2235_, 0);
v_tail_2239_ = lean_ctor_get(v_a_2235_, 1);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_a_2235_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2241_ = v_a_2235_;
v_isShared_2242_ = v_isSharedCheck_2248_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_tail_2239_);
lean_inc(v_head_2238_);
lean_dec(v_a_2235_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2248_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
v___x_2243_ = l_Lean_mkLevelParam(v_head_2238_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 1, v_a_2236_);
lean_ctor_set(v___x_2241_, 0, v___x_2243_);
v___x_2245_ = v___x_2241_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2243_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_a_2236_);
v___x_2245_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
v_a_2235_ = v_tail_2239_;
v_a_2236_ = v___x_2245_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1(void){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2251_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0);
v___x_2253_ = lean_unsigned_to_nat(0u);
v___x_2254_ = lean_alloc_ctor(0, 12, 0);
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
lean_ctor_set(v___x_2254_, 11, v___x_2251_);
return v___x_2254_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2255_ = lean_box(1);
v___x_2256_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3);
v___x_2257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0);
v___x_2258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set(v___x_2258_, 1, v___x_2256_);
lean_ctor_set(v___x_2258_, 2, v___x_2255_);
return v___x_2258_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4(void){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3));
v___x_2261_ = l_Lean_stringToMessageData(v___x_2260_);
return v___x_2261_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5));
v___x_2264_ = l_Lean_stringToMessageData(v___x_2263_);
return v___x_2264_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7));
v___x_2267_ = l_Lean_stringToMessageData(v___x_2266_);
return v___x_2267_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9));
v___x_2270_ = l_Lean_stringToMessageData(v___x_2269_);
return v___x_2270_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11));
v___x_2273_ = l_Lean_stringToMessageData(v___x_2272_);
return v___x_2273_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13));
v___x_2276_ = l_Lean_stringToMessageData(v___x_2275_);
return v___x_2276_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15));
v___x_2279_ = l_Lean_stringToMessageData(v___x_2278_);
return v___x_2279_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__18(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17));
v___x_2282_ = l_Lean_stringToMessageData(v___x_2281_);
return v___x_2282_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__20(void){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__19));
v___x_2285_ = l_Lean_stringToMessageData(v___x_2284_);
return v___x_2285_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__22(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__21));
v___x_2288_ = l_Lean_stringToMessageData(v___x_2287_);
return v___x_2288_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__24(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__23));
v___x_2291_ = l_Lean_stringToMessageData(v___x_2290_);
return v___x_2291_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(lean_object* v_msg_2292_, lean_object* v_declHint_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v_env_2298_; uint8_t v___x_2299_; 
v___x_2296_ = lean_box(0);
v___x_2297_ = lean_st_ref_get(v___y_2294_);
v_env_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc_ref(v_env_2298_);
lean_dec(v___x_2297_);
v___x_2299_ = l_Lean_Name_isAnonymous(v_declHint_2293_);
if (v___x_2299_ == 0)
{
uint8_t v_isExporting_2300_; 
v_isExporting_2300_ = lean_ctor_get_uint8(v_env_2298_, sizeof(void*)*13);
if (v_isExporting_2300_ == 0)
{
lean_object* v___x_2301_; 
lean_dec_ref(v_env_2298_);
lean_dec(v_declHint_2293_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v_msg_2292_);
return v___x_2301_;
}
else
{
lean_object* v___x_2302_; uint8_t v___x_2303_; 
lean_inc_ref(v_env_2298_);
v___x_2302_ = l_Lean_Environment_setExporting(v_env_2298_, v___x_2299_);
lean_inc(v_declHint_2293_);
lean_inc_ref(v___x_2302_);
v___x_2303_ = l_Lean_Environment_contains(v___x_2302_, v_declHint_2293_, v_isExporting_2300_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; 
lean_dec_ref(v___x_2302_);
lean_dec_ref(v_env_2298_);
lean_dec(v_declHint_2293_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_msg_2292_);
return v___x_2304_;
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v_c_2310_; lean_object* v___x_2311_; 
v___x_2305_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
v___x_2306_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2);
v___x_2307_ = l_Lean_Options_empty;
v___x_2308_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2302_);
lean_ctor_set(v___x_2308_, 1, v___x_2305_);
lean_ctor_set(v___x_2308_, 2, v___x_2306_);
lean_ctor_set(v___x_2308_, 3, v___x_2307_);
lean_inc(v_declHint_2293_);
v___x_2309_ = l_Lean_MessageData_ofConstName(v_declHint_2293_, v___x_2299_);
v_c_2310_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2310_, 0, v___x_2308_);
lean_ctor_set(v_c_2310_, 1, v___x_2309_);
v___x_2311_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2298_, v_declHint_2293_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_dec_ref(v_env_2298_);
lean_dec(v_declHint_2293_);
v___x_2312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4);
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
lean_ctor_set(v___x_2313_, 1, v_c_2310_);
v___x_2314_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = l_Lean_MessageData_note(v___x_2315_);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v_msg_2292_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
else
{
lean_object* v_val_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2375_; 
v_val_2319_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2321_ = v___x_2311_;
v_isShared_2322_ = v_isSharedCheck_2375_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_val_2319_);
lean_dec(v___x_2311_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2375_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; lean_object* v_modules_2324_; lean_object* v_moduleNames_2325_; lean_object* v_mod_2326_; uint8_t v___y_2328_; uint8_t v___x_2358_; 
v___x_2323_ = l_Lean_Environment_header(v_env_2298_);
lean_dec_ref(v_env_2298_);
v_modules_2324_ = lean_ctor_get(v___x_2323_, 3);
lean_inc_ref(v_modules_2324_);
v_moduleNames_2325_ = lean_ctor_get(v___x_2323_, 4);
lean_inc_ref(v_moduleNames_2325_);
lean_dec_ref(v___x_2323_);
v_mod_2326_ = lean_array_get(v___x_2296_, v_moduleNames_2325_, v_val_2319_);
lean_dec_ref(v_moduleNames_2325_);
v___x_2358_ = l_Lean_isPrivateName(v_declHint_2293_);
lean_dec(v_declHint_2293_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2359_ = lean_array_get_size(v_modules_2324_);
v___x_2360_ = lean_nat_dec_lt(v_val_2319_, v___x_2359_);
if (v___x_2360_ == 0)
{
lean_dec_ref(v_modules_2324_);
lean_dec(v_val_2319_);
v___y_2328_ = v___x_2358_;
goto v___jp_2327_;
}
else
{
lean_object* v___x_2361_; lean_object* v_toImport_2362_; uint8_t v_isExported_2363_; 
v___x_2361_ = lean_array_fget(v_modules_2324_, v_val_2319_);
lean_dec(v_val_2319_);
lean_dec_ref(v_modules_2324_);
v_toImport_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc_ref(v_toImport_2362_);
lean_dec(v___x_2361_);
v_isExported_2363_ = lean_ctor_get_uint8(v_toImport_2362_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2362_);
v___y_2328_ = v_isExported_2363_;
goto v___jp_2327_;
}
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec_ref(v_modules_2324_);
lean_del_object(v___x_2321_);
lean_dec(v_val_2319_);
v___x_2364_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4);
v___x_2365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
lean_ctor_set(v___x_2365_, 1, v_c_2310_);
v___x_2366_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__22);
v___x_2367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = l_Lean_MessageData_ofName(v_mod_2326_);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__24);
v___x_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = l_Lean_MessageData_note(v___x_2371_);
v___x_2373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2373_, 0, v_msg_2292_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
v___jp_2327_:
{
if (v___y_2328_ == 0)
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2329_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8);
v___x_2330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
lean_ctor_set(v___x_2330_, 1, v_c_2310_);
v___x_2331_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10);
v___x_2332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = l_Lean_MessageData_ofName(v_mod_2326_);
v___x_2334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12);
v___x_2336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = l_Lean_MessageData_note(v___x_2336_);
v___x_2338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2338_, 0, v_msg_2292_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set_tag(v___x_2321_, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2338_);
v___x_2340_ = v___x_2321_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2342_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14);
v___x_2343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v_c_2310_);
v___x_2344_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16);
v___x_2345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2343_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
v___x_2346_ = l_Lean_MessageData_ofName(v_mod_2326_);
lean_inc_ref(v___x_2346_);
v___x_2347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__18);
v___x_2349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2347_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set(v___x_2350_, 1, v___x_2346_);
v___x_2351_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__20);
v___x_2352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2350_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = l_Lean_MessageData_note(v___x_2352_);
v___x_2354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2354_, 0, v_msg_2292_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set_tag(v___x_2321_, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2354_);
v___x_2356_ = v___x_2321_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
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
lean_object* v___x_2376_; 
lean_dec_ref(v_env_2298_);
lean_dec(v_declHint_2293_);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v_msg_2292_);
return v___x_2376_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2292_ = stack[0].m_obj;
lean_object* v_declHint_2293_ = stack[1].m_obj;
lean_object* v___y_2294_ = stack[2].m_obj;
lean_object* v_res_2377_;
v_res_2377_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2292_, v_declHint_2293_, v___y_2294_);
stack->m_obj
 = v_res_2377_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___boxed(lean_object* v_msg_2378_, lean_object* v_declHint_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2378_, v_declHint_2379_, v___y_2380_);
lean_dec(v___y_2380_);
return v_res_2382_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(lean_object* v_msg_2383_, lean_object* v_declHint_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2402_; 
v___x_2392_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2383_, v_declHint_2384_, v___y_2390_);
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2402_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2402_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2397_ = l_Lean_unknownIdentifierMessageTag;
v___x_2398_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
lean_ctor_set(v___x_2398_, 1, v_a_2393_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2398_);
v___x_2400_ = v___x_2395_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2383_ = stack[0].m_obj;
lean_object* v_declHint_2384_ = stack[1].m_obj;
lean_object* v___y_2385_ = stack[2].m_obj;
lean_object* v___y_2386_ = stack[3].m_obj;
lean_object* v___y_2387_ = stack[4].m_obj;
lean_object* v___y_2388_ = stack[5].m_obj;
lean_object* v___y_2389_ = stack[6].m_obj;
lean_object* v___y_2390_ = stack[7].m_obj;
lean_object* v_res_2403_;
v_res_2403_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2383_, v_declHint_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
stack->m_obj
 = v_res_2403_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23___boxed(lean_object* v_msg_2404_, lean_object* v_declHint_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2404_, v_declHint_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
return v_res_2413_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(lean_object* v_ref_2414_, lean_object* v_msg_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_toCold_2423_; lean_object* v_currRecDepth_2424_; lean_object* v_ref_2425_; uint16_t v_optionFlags_2426_; uint8_t v_suppressElabErrors_2427_; uint8_t v_isRecordingDeps_2428_; lean_object* v_ref_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_toCold_2423_ = lean_ctor_get(v___y_2420_, 0);
v_currRecDepth_2424_ = lean_ctor_get(v___y_2420_, 1);
v_ref_2425_ = lean_ctor_get(v___y_2420_, 2);
v_optionFlags_2426_ = lean_ctor_get_uint16(v___y_2420_, sizeof(void*)*3);
v_suppressElabErrors_2427_ = lean_ctor_get_uint8(v___y_2420_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2428_ = lean_ctor_get_uint8(v___y_2420_, sizeof(void*)*3 + 3);
v_ref_2429_ = l_Lean_replaceRef(v_ref_2414_, v_ref_2425_);
lean_inc(v_currRecDepth_2424_);
lean_inc_ref(v_toCold_2423_);
v___x_2430_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2430_, 0, v_toCold_2423_);
lean_ctor_set(v___x_2430_, 1, v_currRecDepth_2424_);
lean_ctor_set(v___x_2430_, 2, v_ref_2429_);
lean_ctor_set_uint16(v___x_2430_, sizeof(void*)*3, v_optionFlags_2426_);
lean_ctor_set_uint8(v___x_2430_, sizeof(void*)*3 + 2, v_suppressElabErrors_2427_);
lean_ctor_set_uint8(v___x_2430_, sizeof(void*)*3 + 3, v_isRecordingDeps_2428_);
v___x_2431_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___x_2430_, v___y_2421_);
lean_dec_ref_known(v___x_2430_, 3);
return v___x_2431_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2414_ = stack[0].m_obj;
lean_object* v_msg_2415_ = stack[1].m_obj;
lean_object* v___y_2416_ = stack[2].m_obj;
lean_object* v___y_2417_ = stack[3].m_obj;
lean_object* v___y_2418_ = stack[4].m_obj;
lean_object* v___y_2419_ = stack[5].m_obj;
lean_object* v___y_2420_ = stack[6].m_obj;
lean_object* v___y_2421_ = stack[7].m_obj;
lean_object* v_res_2432_;
v_res_2432_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2414_, v_msg_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
stack->m_obj
 = v_res_2432_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg___boxed(lean_object* v_ref_2433_, lean_object* v_msg_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2433_, v_msg_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v_ref_2433_);
return v_res_2442_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(lean_object* v_ref_2443_, lean_object* v_msg_2444_, lean_object* v_declHint_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___x_2453_; lean_object* v_a_2454_; lean_object* v___x_2455_; 
v___x_2453_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2444_, v_declHint_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref(v___x_2453_);
v___x_2455_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2443_, v_a_2454_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
return v___x_2455_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2443_ = stack[0].m_obj;
lean_object* v_msg_2444_ = stack[1].m_obj;
lean_object* v_declHint_2445_ = stack[2].m_obj;
lean_object* v___y_2446_ = stack[3].m_obj;
lean_object* v___y_2447_ = stack[4].m_obj;
lean_object* v___y_2448_ = stack[5].m_obj;
lean_object* v___y_2449_ = stack[6].m_obj;
lean_object* v___y_2450_ = stack[7].m_obj;
lean_object* v___y_2451_ = stack[8].m_obj;
lean_object* v_res_2456_;
v_res_2456_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2443_, v_msg_2444_, v_declHint_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
stack->m_obj
 = v_res_2456_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg___boxed(lean_object* v_ref_2457_, lean_object* v_msg_2458_, lean_object* v_declHint_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2457_, v_msg_2458_, v_declHint_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v_ref_2457_);
return v_res_2467_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0));
v___x_2470_ = l_Lean_stringToMessageData(v___x_2469_);
return v___x_2470_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(lean_object* v_ref_2471_, lean_object* v_constName_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v___x_2480_; uint8_t v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2480_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1);
v___x_2481_ = 0;
lean_inc(v_constName_2472_);
v___x_2482_ = l_Lean_MessageData_ofConstName(v_constName_2472_, v___x_2481_);
v___x_2483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2480_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2471_, v___x_2485_, v_constName_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
return v___x_2486_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2471_ = stack[0].m_obj;
lean_object* v_constName_2472_ = stack[1].m_obj;
lean_object* v___y_2473_ = stack[2].m_obj;
lean_object* v___y_2474_ = stack[3].m_obj;
lean_object* v___y_2475_ = stack[4].m_obj;
lean_object* v___y_2476_ = stack[5].m_obj;
lean_object* v___y_2477_ = stack[6].m_obj;
lean_object* v___y_2478_ = stack[7].m_obj;
lean_object* v_res_2487_;
v_res_2487_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2471_, v_constName_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
stack->m_obj
 = v_res_2487_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___boxed(lean_object* v_ref_2488_, lean_object* v_constName_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2488_, v_constName_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v_ref_2488_);
return v_res_2497_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(lean_object* v_constName_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_ref_2506_; lean_object* v___x_2507_; 
v_ref_2506_ = lean_ctor_get(v___y_2503_, 2);
v___x_2507_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2506_, v_constName_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2507_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2498_ = stack[0].m_obj;
lean_object* v___y_2499_ = stack[1].m_obj;
lean_object* v___y_2500_ = stack[2].m_obj;
lean_object* v___y_2501_ = stack[3].m_obj;
lean_object* v___y_2502_ = stack[4].m_obj;
lean_object* v___y_2503_ = stack[5].m_obj;
lean_object* v___y_2504_ = stack[6].m_obj;
lean_object* v_res_2508_;
v_res_2508_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
stack->m_obj
 = v_res_2508_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_constName_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
return v_res_2517_;
}
}
lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(lean_object* v_constName_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v___x_2526_; lean_object* v_env_2527_; uint8_t v___x_2528_; lean_object* v___x_2529_; 
v___x_2526_ = lean_st_ref_get(v___y_2524_);
v_env_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc_ref(v_env_2527_);
lean_dec(v___x_2526_);
v___x_2528_ = 0;
lean_inc(v_constName_2518_);
v___x_2529_ = l_Lean_Environment_findConstVal_x3f(v_env_2527_, v_constName_2518_, v___x_2528_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
return v___x_2530_;
}
else
{
lean_object* v_val_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec(v_constName_2518_);
v_val_2531_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2529_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_val_2531_);
lean_dec(v___x_2529_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set_tag(v___x_2533_, 0);
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_val_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2518_ = stack[0].m_obj;
lean_object* v___y_2519_ = stack[1].m_obj;
lean_object* v___y_2520_ = stack[2].m_obj;
lean_object* v___y_2521_ = stack[3].m_obj;
lean_object* v___y_2522_ = stack[4].m_obj;
lean_object* v___y_2523_ = stack[5].m_obj;
lean_object* v___y_2524_ = stack[6].m_obj;
lean_object* v_res_2539_;
v_res_2539_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
stack->m_obj
 = v_res_2539_;
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14___boxed(lean_object* v_constName_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
return v_res_2548_;
}
}
lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(lean_object* v_constName_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v___x_2557_; 
lean_inc(v_constName_2549_);
v___x_2557_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2569_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2569_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2569_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v_levelParams_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2567_; 
v_levelParams_2562_ = lean_ctor_get(v_a_2558_, 1);
lean_inc(v_levelParams_2562_);
lean_dec(v_a_2558_);
v___x_2563_ = lean_box(0);
v___x_2564_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(v_levelParams_2562_, v___x_2563_);
v___x_2565_ = l_Lean_mkConst(v_constName_2549_, v___x_2564_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v___x_2565_);
v___x_2567_ = v___x_2560_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec(v_constName_2549_);
v_a_2570_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2557_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2557_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2549_ = stack[0].m_obj;
lean_object* v___y_2550_ = stack[1].m_obj;
lean_object* v___y_2551_ = stack[2].m_obj;
lean_object* v___y_2552_ = stack[3].m_obj;
lean_object* v___y_2553_ = stack[4].m_obj;
lean_object* v___y_2554_ = stack[5].m_obj;
lean_object* v___y_2555_ = stack[6].m_obj;
lean_object* v_res_2578_;
v_res_2578_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_constName_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
stack->m_obj
 = v_res_2578_;
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_constName_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_constName_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
return v_res_2587_;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(uint8_t v___x_2588_, lean_object* v_declName_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_ref_2597_; lean_object* v___x_2598_; 
v_ref_2597_ = lean_ctor_get(v___y_2594_, 2);
v___x_2598_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_declName_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2598_, 1);
v___x_2600_ = lean_box(0);
lean_inc(v_ref_2597_);
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v_ref_2597_);
v___x_2602_ = lean_unsigned_to_nat(32u);
v___x_2603_ = lean_mk_empty_array_with_capacity(v___x_2602_);
lean_dec_ref(v___x_2603_);
v___x_2604_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4);
v___x_2605_ = lean_box(0);
v___x_2606_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2606_, 0, v___x_2601_);
lean_ctor_set(v___x_2606_, 1, v___x_2604_);
lean_ctor_set(v___x_2606_, 2, v___x_2605_);
lean_ctor_set(v___x_2606_, 3, v_a_2599_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*4, v___x_2588_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*4 + 1, v___x_2588_);
v___x_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
v___x_2608_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v___x_2607_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
return v___x_2608_;
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
v_a_2609_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2598_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2598_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2588_ = stack[0].m_num;
lean_object* v_declName_2589_ = stack[1].m_obj;
lean_object* v___y_2590_ = stack[2].m_obj;
lean_object* v___y_2591_ = stack[3].m_obj;
lean_object* v___y_2592_ = stack[4].m_obj;
lean_object* v___y_2593_ = stack[5].m_obj;
lean_object* v___y_2594_ = stack[6].m_obj;
lean_object* v___y_2595_ = stack[7].m_obj;
lean_object* v_res_2617_;
v_res_2617_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(v___x_2588_, v_declName_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
stack->m_obj
 = v_res_2617_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v___x_2618_, lean_object* v_declName_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
uint8_t v___x_17938__boxed_2627_; lean_object* v_res_2628_; 
v___x_17938__boxed_2627_ = lean_unbox(v___x_2618_);
v_res_2628_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(v___x_17938__boxed_2627_, v_declName_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
return v_res_2628_;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(lean_object* v___f_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; lean_object* v_env_2638_; lean_object* v___x_2639_; 
v___x_2637_ = lean_st_ref_get(v___y_2635_);
v_env_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc_ref(v_env_2638_);
lean_dec(v___x_2637_);
v___x_2639_ = lean_apply_8(v___f_2629_, v_env_2638_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, lean_box(0));
return v___x_2639_;
}
}
LEAN_EXPORT void l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2629_ = stack[0].m_obj;
lean_object* v___y_2630_ = stack[1].m_obj;
lean_object* v___y_2631_ = stack[2].m_obj;
lean_object* v___y_2632_ = stack[3].m_obj;
lean_object* v___y_2633_ = stack[4].m_obj;
lean_object* v___y_2634_ = stack[5].m_obj;
lean_object* v___y_2635_ = stack[6].m_obj;
lean_object* v_res_2640_;
v_res_2640_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(v___f_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
stack->m_obj
 = v_res_2640_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed(lean_object* v___f_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(v___f_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v_res_2649_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0);
v___x_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
return v___x_2651_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
return v___x_2653_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2655_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
lean_ctor_set(v___x_2655_, 2, v___x_2654_);
lean_ctor_set(v___x_2655_, 3, v___x_2654_);
lean_ctor_set(v___x_2655_, 4, v___x_2654_);
lean_ctor_set(v___x_2655_, 5, v___x_2654_);
return v___x_2655_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(lean_object* v_env_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; lean_object* v_nextMacroScope_2661_; lean_object* v_ngen_2662_; lean_object* v_auxDeclNGen_2663_; lean_object* v_traceState_2664_; lean_object* v_recordedDeps_2665_; lean_object* v_messages_2666_; lean_object* v_infoState_2667_; lean_object* v_snapshotTasks_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2694_; 
v___x_2660_ = lean_st_ref_take(v___y_2658_);
v_nextMacroScope_2661_ = lean_ctor_get(v___x_2660_, 1);
v_ngen_2662_ = lean_ctor_get(v___x_2660_, 2);
v_auxDeclNGen_2663_ = lean_ctor_get(v___x_2660_, 3);
v_traceState_2664_ = lean_ctor_get(v___x_2660_, 4);
v_recordedDeps_2665_ = lean_ctor_get(v___x_2660_, 6);
v_messages_2666_ = lean_ctor_get(v___x_2660_, 7);
v_infoState_2667_ = lean_ctor_get(v___x_2660_, 8);
v_snapshotTasks_2668_ = lean_ctor_get(v___x_2660_, 9);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; lean_object* v_unused_2696_; 
v_unused_2695_ = lean_ctor_get(v___x_2660_, 5);
lean_dec(v_unused_2695_);
v_unused_2696_ = lean_ctor_get(v___x_2660_, 0);
lean_dec(v_unused_2696_);
v___x_2670_ = v___x_2660_;
v_isShared_2671_ = v_isSharedCheck_2694_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_snapshotTasks_2668_);
lean_inc(v_infoState_2667_);
lean_inc(v_messages_2666_);
lean_inc(v_recordedDeps_2665_);
lean_inc(v_traceState_2664_);
lean_inc(v_auxDeclNGen_2663_);
lean_inc(v_ngen_2662_);
lean_inc(v_nextMacroScope_2661_);
lean_dec(v___x_2660_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2694_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v___x_2674_; 
v___x_2672_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 5, v___x_2672_);
lean_ctor_set(v___x_2670_, 0, v_env_2656_);
v___x_2674_ = v___x_2670_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_env_2656_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_nextMacroScope_2661_);
lean_ctor_set(v_reuseFailAlloc_2693_, 2, v_ngen_2662_);
lean_ctor_set(v_reuseFailAlloc_2693_, 3, v_auxDeclNGen_2663_);
lean_ctor_set(v_reuseFailAlloc_2693_, 4, v_traceState_2664_);
lean_ctor_set(v_reuseFailAlloc_2693_, 5, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2693_, 6, v_recordedDeps_2665_);
lean_ctor_set(v_reuseFailAlloc_2693_, 7, v_messages_2666_);
lean_ctor_set(v_reuseFailAlloc_2693_, 8, v_infoState_2667_);
lean_ctor_set(v_reuseFailAlloc_2693_, 9, v_snapshotTasks_2668_);
v___x_2674_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v_mctx_2677_; lean_object* v_zetaDeltaFVarIds_2678_; lean_object* v_postponed_2679_; lean_object* v_diag_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2691_; 
v___x_2675_ = lean_st_ref_put(v___y_2658_, v___x_2674_);
v___x_2676_ = lean_st_ref_take(v___y_2657_);
v_mctx_2677_ = lean_ctor_get(v___x_2676_, 0);
v_zetaDeltaFVarIds_2678_ = lean_ctor_get(v___x_2676_, 2);
v_postponed_2679_ = lean_ctor_get(v___x_2676_, 3);
v_diag_2680_ = lean_ctor_get(v___x_2676_, 4);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2691_ == 0)
{
lean_object* v_unused_2692_; 
v_unused_2692_ = lean_ctor_get(v___x_2676_, 1);
lean_dec(v_unused_2692_);
v___x_2682_ = v___x_2676_;
v_isShared_2683_ = v_isSharedCheck_2691_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_diag_2680_);
lean_inc(v_postponed_2679_);
lean_inc(v_zetaDeltaFVarIds_2678_);
lean_inc(v_mctx_2677_);
lean_dec(v___x_2676_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2691_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2684_ = lean_box(0);
v___x_2685_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 1, v___x_2685_);
v___x_2687_ = v___x_2682_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_mctx_2677_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_zetaDeltaFVarIds_2678_);
lean_ctor_set(v_reuseFailAlloc_2690_, 3, v_postponed_2679_);
lean_ctor_set(v_reuseFailAlloc_2690_, 4, v_diag_2680_);
v___x_2687_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = lean_st_ref_put(v___y_2657_, v___x_2687_);
v___x_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2684_);
return v___x_2689_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2656_ = stack[0].m_obj;
lean_object* v___y_2657_ = stack[1].m_obj;
lean_object* v___y_2658_ = stack[2].m_obj;
lean_object* v_res_2697_;
v_res_2697_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2656_, v___y_2657_, v___y_2658_);
stack->m_obj
 = v_res_2697_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___boxed(lean_object* v_env_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2698_, v___y_2699_, v___y_2700_);
lean_dec(v___y_2700_);
lean_dec(v___y_2699_);
return v_res_2702_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(lean_object* v_env_2703_, lean_object* v_x_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___x_2712_; lean_object* v_env_2713_; lean_object* v_a_2715_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2712_ = lean_st_ref_get(v___y_2710_);
v_env_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc_ref(v_env_2713_);
lean_dec(v___x_2712_);
v___x_2725_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2703_, v___y_2708_, v___y_2710_);
lean_dec_ref(v___x_2725_);
lean_inc(v___y_2710_);
lean_inc_ref(v___y_2709_);
lean_inc(v___y_2708_);
lean_inc_ref(v___y_2707_);
lean_inc(v___y_2706_);
lean_inc_ref(v___y_2705_);
v___x_2726_ = lean_apply_7(v_x_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, lean_box(0));
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2726_, 1);
v___x_2728_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2713_, v___y_2708_, v___y_2710_);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2735_ == 0)
{
lean_object* v_unused_2736_; 
v_unused_2736_ = lean_ctor_get(v___x_2728_, 0);
lean_dec(v_unused_2736_);
v___x_2730_ = v___x_2728_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_dec(v___x_2728_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v_a_2727_);
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2727_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
else
{
lean_object* v_a_2737_; 
v_a_2737_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2726_, 1);
v_a_2715_ = v_a_2737_;
goto v___jp_2714_;
}
v___jp_2714_:
{
lean_object* v___x_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
v___x_2716_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2713_, v___y_2708_, v___y_2710_);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2723_ == 0)
{
lean_object* v_unused_2724_; 
v_unused_2724_ = lean_ctor_get(v___x_2716_, 0);
lean_dec(v_unused_2724_);
v___x_2718_ = v___x_2716_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_dec(v___x_2716_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set_tag(v___x_2718_, 1);
lean_ctor_set(v___x_2718_, 0, v_a_2715_);
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2715_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2703_ = stack[0].m_obj;
lean_object* v_x_2704_ = stack[1].m_obj;
lean_object* v___y_2705_ = stack[2].m_obj;
lean_object* v___y_2706_ = stack[3].m_obj;
lean_object* v___y_2707_ = stack[4].m_obj;
lean_object* v___y_2708_ = stack[5].m_obj;
lean_object* v___y_2709_ = stack[6].m_obj;
lean_object* v___y_2710_ = stack[7].m_obj;
lean_object* v_res_2738_;
v_res_2738_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2703_, v_x_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
stack->m_obj
 = v_res_2738_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_env_2739_, lean_object* v_x_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2739_, v_x_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
return v_res_2748_;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(lean_object* v_declName_2749_, lean_object* v_env_2750_, lean_object* v_addInfo_2751_, lean_object* v_____r_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_privateToUserName_x3f(v_declName_2749_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_dec_ref(v_addInfo_2751_);
lean_dec_ref(v_env_2750_);
v___x_2761_ = lean_box(0);
v___x_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
return v___x_2762_;
}
else
{
lean_object* v_val_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2780_; 
v_val_2763_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2765_ = v___x_2760_;
v_isShared_2766_ = v_isSharedCheck_2780_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_val_2763_);
lean_dec(v___x_2760_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2780_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
uint8_t v___x_2767_; uint8_t v___x_2768_; 
v___x_2767_ = 1;
lean_inc(v_val_2763_);
v___x_2768_ = l_Lean_Environment_contains(v_env_2750_, v_val_2763_, v___x_2767_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2771_; 
lean_dec(v_val_2763_);
lean_dec_ref(v_addInfo_2751_);
v___x_2769_ = lean_box(0);
if (v_isShared_2766_ == 0)
{
lean_ctor_set_tag(v___x_2765_, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2769_);
v___x_2771_ = v___x_2765_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
else
{
lean_object* v___x_2773_; 
lean_del_object(v___x_2765_);
lean_inc(v___y_2758_);
lean_inc_ref(v___y_2757_);
lean_inc(v___y_2756_);
lean_inc_ref(v___y_2755_);
lean_inc(v___y_2754_);
lean_inc_ref(v___y_2753_);
lean_inc(v_val_2763_);
v___x_2773_ = lean_apply_8(v_addInfo_2751_, v_val_2763_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, lean_box(0));
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
lean_dec_ref_known(v___x_2773_, 1);
v___x_2774_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
v___x_2775_ = l_Lean_MessageData_ofConstName(v_val_2763_, v___x_2767_);
v___x_2776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
v___x_2777_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2776_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2778_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
return v___x_2779_;
}
else
{
lean_dec(v_val_2763_);
return v___x_2773_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2749_ = stack[0].m_obj;
lean_object* v_env_2750_ = stack[1].m_obj;
lean_object* v_addInfo_2751_ = stack[2].m_obj;
lean_object* v_____r_2752_ = stack[3].m_obj;
lean_object* v___y_2753_ = stack[4].m_obj;
lean_object* v___y_2754_ = stack[5].m_obj;
lean_object* v___y_2755_ = stack[6].m_obj;
lean_object* v___y_2756_ = stack[7].m_obj;
lean_object* v___y_2757_ = stack[8].m_obj;
lean_object* v___y_2758_ = stack[9].m_obj;
lean_object* v_res_2781_;
v_res_2781_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(v_declName_2749_, v_env_2750_, v_addInfo_2751_, v_____r_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
stack->m_obj
 = v_res_2781_;
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
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(lean_object* v_addInfo_2794_, lean_object* v_declName_2795_, uint8_t v___x_2796_, lean_object* v___f_2797_, uint8_t v___x_2798_, lean_object* v_env_2799_, lean_object* v___f_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
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
LEAN_EXPORT void l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_addInfo_2794_ = stack[0].m_obj;
lean_object* v_declName_2795_ = stack[1].m_obj;
uint8_t v___x_2796_ = stack[2].m_num;
lean_object* v___f_2797_ = stack[3].m_obj;
uint8_t v___x_2798_ = stack[4].m_num;
lean_object* v_env_2799_ = stack[5].m_obj;
lean_object* v___f_2800_ = stack[6].m_obj;
lean_object* v___y_2801_ = stack[7].m_obj;
lean_object* v___y_2802_ = stack[8].m_obj;
lean_object* v___y_2803_ = stack[9].m_obj;
lean_object* v___y_2804_ = stack[10].m_obj;
lean_object* v___y_2805_ = stack[11].m_obj;
lean_object* v___y_2806_ = stack[12].m_obj;
lean_object* v_res_2823_;
v_res_2823_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(v_addInfo_2794_, v_declName_2795_, v___x_2796_, v___f_2797_, v___x_2798_, v_env_2799_, v___f_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
stack->m_obj
 = v_res_2823_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed(lean_object* v_addInfo_2824_, lean_object* v_declName_2825_, lean_object* v___x_2826_, lean_object* v___f_2827_, lean_object* v___x_2828_, lean_object* v_env_2829_, lean_object* v___f_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
uint8_t v___x_18456__boxed_2838_; uint8_t v___x_18458__boxed_2839_; lean_object* v_res_2840_; 
v___x_18456__boxed_2838_ = lean_unbox(v___x_2826_);
v___x_18458__boxed_2839_ = lean_unbox(v___x_2828_);
v_res_2840_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(v_addInfo_2824_, v_declName_2825_, v___x_18456__boxed_2838_, v___f_2827_, v___x_18458__boxed_2839_, v_env_2829_, v___f_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec_ref(v___f_2830_);
lean_dec_ref(v_env_2829_);
lean_dec_ref(v___f_2827_);
return v_res_2840_;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(lean_object* v_declName_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v___x_2852_; lean_object* v_env_2853_; uint8_t v___x_2854_; lean_object* v_addInfo_2855_; lean_object* v_env_2856_; lean_object* v___f_2857_; lean_object* v___f_2858_; lean_object* v___x_2859_; lean_object* v___f_2860_; uint8_t v___x_2861_; uint8_t v___x_2862_; 
v___x_2852_ = lean_st_ref_get(v___y_2850_);
v_env_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc_ref(v_env_2853_);
lean_dec(v___x_2852_);
v___x_2854_ = 0;
v_addInfo_2855_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0));
v_env_2856_ = l_Lean_Environment_setExporting(v_env_2853_, v___x_2854_);
lean_inc_ref_n(v_env_2856_, 4);
lean_inc_n(v_declName_2844_, 4);
v___f_2857_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed), 11, 3);
lean_closure_set(v___f_2857_, 0, v_declName_2844_);
lean_closure_set(v___f_2857_, 1, v_env_2856_);
lean_closure_set(v___f_2857_, 2, v_addInfo_2855_);
v___f_2858_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2858_, 0, v_env_2856_);
lean_closure_set(v___f_2858_, 1, v_declName_2844_);
lean_closure_set(v___f_2858_, 2, v___f_2857_);
lean_closure_set(v___f_2858_, 3, v_addInfo_2855_);
v___x_2859_ = lean_box(v___x_2854_);
lean_inc_ref(v___f_2858_);
v___f_2860_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed), 12, 4);
lean_closure_set(v___f_2860_, 0, v___f_2858_);
lean_closure_set(v___f_2860_, 1, v_declName_2844_);
lean_closure_set(v___f_2860_, 2, v___x_2859_);
lean_closure_set(v___f_2860_, 3, v_env_2856_);
v___x_2861_ = 1;
v___x_2862_ = l_Lean_Environment_contains(v_env_2856_, v_declName_2844_, v___x_2861_);
if (v___x_2862_ == 0)
{
lean_object* v___f_2863_; lean_object* v___x_2864_; 
lean_dec_ref(v___f_2858_);
lean_dec(v_declName_2844_);
v___f_2863_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed), 8, 1);
lean_closure_set(v___f_2863_, 0, v___f_2860_);
v___x_2864_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2856_, v___f_2863_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
return v___x_2864_;
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___f_2867_; lean_object* v___x_2868_; 
v___x_2865_ = lean_box(v___x_2861_);
v___x_2866_ = lean_box(v___x_2854_);
lean_inc_ref(v_env_2856_);
v___f_2867_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed), 14, 7);
lean_closure_set(v___f_2867_, 0, v_addInfo_2855_);
lean_closure_set(v___f_2867_, 1, v_declName_2844_);
lean_closure_set(v___f_2867_, 2, v___x_2865_);
lean_closure_set(v___f_2867_, 3, v___f_2858_);
lean_closure_set(v___f_2867_, 4, v___x_2866_);
lean_closure_set(v___f_2867_, 5, v_env_2856_);
lean_closure_set(v___f_2867_, 6, v___f_2860_);
v___x_2868_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2856_, v___f_2867_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
return v___x_2868_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2844_ = stack[0].m_obj;
lean_object* v___y_2845_ = stack[1].m_obj;
lean_object* v___y_2846_ = stack[2].m_obj;
lean_object* v___y_2847_ = stack[3].m_obj;
lean_object* v___y_2848_ = stack[4].m_obj;
lean_object* v___y_2849_ = stack[5].m_obj;
lean_object* v___y_2850_ = stack[6].m_obj;
lean_object* v_res_2869_;
v_res_2869_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
stack->m_obj
 = v_res_2869_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___boxed(lean_object* v_declName_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
return v_res_2878_;
}
}
lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(lean_object* v_modifiers_2879_, lean_object* v_declName_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_declName_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___x_2953_; lean_object* v_env_2954_; uint8_t v_visibility_2955_; uint8_t v___x_2956_; 
v___x_2953_ = lean_st_ref_get(v___y_2886_);
v_env_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc_ref(v_env_2954_);
lean_dec(v___x_2953_);
v_visibility_2955_ = lean_ctor_get_uint8(v_modifiers_2879_, sizeof(void*)*3);
v___x_2956_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_2954_, v_visibility_2955_);
lean_dec_ref(v_env_2954_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; lean_object* v_env_2958_; lean_object* v_declName_2959_; 
v___x_2957_ = lean_st_ref_get(v___y_2886_);
v_env_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc_ref(v_env_2958_);
lean_dec(v___x_2957_);
v_declName_2959_ = l_Lean_mkPrivateName(v_env_2958_, v_declName_2880_);
lean_dec_ref(v_env_2958_);
v_declName_2889_ = v_declName_2959_;
v___y_2890_ = v___y_2881_;
v___y_2891_ = v___y_2882_;
v___y_2892_ = v___y_2883_;
v___y_2893_ = v___y_2884_;
v___y_2894_ = v___y_2885_;
v___y_2895_ = v___y_2886_;
goto v___jp_2888_;
}
else
{
v_declName_2889_ = v_declName_2880_;
v___y_2890_ = v___y_2881_;
v___y_2891_ = v___y_2882_;
v___y_2892_ = v___y_2883_;
v___y_2893_ = v___y_2884_;
v___y_2894_ = v___y_2885_;
v___y_2895_ = v___y_2886_;
goto v___jp_2888_;
}
v___jp_2888_:
{
lean_object* v___x_2896_; 
lean_inc(v_declName_2889_);
v___x_2896_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2943_; 
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2943_ == 0)
{
lean_object* v_unused_2944_; 
v_unused_2944_ = lean_ctor_get(v___x_2896_, 0);
lean_dec(v_unused_2944_);
v___x_2898_ = v___x_2896_;
v_isShared_2899_ = v_isSharedCheck_2943_;
goto v_resetjp_2897_;
}
else
{
lean_dec(v___x_2896_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2943_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
uint8_t v_isProtected_2900_; 
v_isProtected_2900_ = lean_ctor_get_uint8(v_modifiers_2879_, sizeof(void*)*3 + 1);
if (v_isProtected_2900_ == 0)
{
lean_object* v___x_2902_; 
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v_declName_2889_);
v___x_2902_ = v___x_2898_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_declName_2889_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
else
{
lean_object* v___x_2904_; lean_object* v_env_2905_; lean_object* v_nextMacroScope_2906_; lean_object* v_ngen_2907_; lean_object* v_auxDeclNGen_2908_; lean_object* v_traceState_2909_; lean_object* v_recordedDeps_2910_; lean_object* v_messages_2911_; lean_object* v_infoState_2912_; lean_object* v_snapshotTasks_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2941_; 
v___x_2904_ = lean_st_ref_take(v___y_2895_);
v_env_2905_ = lean_ctor_get(v___x_2904_, 0);
v_nextMacroScope_2906_ = lean_ctor_get(v___x_2904_, 1);
v_ngen_2907_ = lean_ctor_get(v___x_2904_, 2);
v_auxDeclNGen_2908_ = lean_ctor_get(v___x_2904_, 3);
v_traceState_2909_ = lean_ctor_get(v___x_2904_, 4);
v_recordedDeps_2910_ = lean_ctor_get(v___x_2904_, 6);
v_messages_2911_ = lean_ctor_get(v___x_2904_, 7);
v_infoState_2912_ = lean_ctor_get(v___x_2904_, 8);
v_snapshotTasks_2913_ = lean_ctor_get(v___x_2904_, 9);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2941_ == 0)
{
lean_object* v_unused_2942_; 
v_unused_2942_ = lean_ctor_get(v___x_2904_, 5);
lean_dec(v_unused_2942_);
v___x_2915_ = v___x_2904_;
v_isShared_2916_ = v_isSharedCheck_2941_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_snapshotTasks_2913_);
lean_inc(v_infoState_2912_);
lean_inc(v_messages_2911_);
lean_inc(v_recordedDeps_2910_);
lean_inc(v_traceState_2909_);
lean_inc(v_auxDeclNGen_2908_);
lean_inc(v_ngen_2907_);
lean_inc(v_nextMacroScope_2906_);
lean_inc(v_env_2905_);
lean_dec(v___x_2904_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2941_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2920_; 
lean_inc(v_declName_2889_);
v___x_2917_ = l_Lean_addProtected(v_env_2905_, v_declName_2889_);
v___x_2918_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 5, v___x_2918_);
lean_ctor_set(v___x_2915_, 0, v___x_2917_);
v___x_2920_ = v___x_2915_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2917_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_nextMacroScope_2906_);
lean_ctor_set(v_reuseFailAlloc_2940_, 2, v_ngen_2907_);
lean_ctor_set(v_reuseFailAlloc_2940_, 3, v_auxDeclNGen_2908_);
lean_ctor_set(v_reuseFailAlloc_2940_, 4, v_traceState_2909_);
lean_ctor_set(v_reuseFailAlloc_2940_, 5, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_2940_, 6, v_recordedDeps_2910_);
lean_ctor_set(v_reuseFailAlloc_2940_, 7, v_messages_2911_);
lean_ctor_set(v_reuseFailAlloc_2940_, 8, v_infoState_2912_);
lean_ctor_set(v_reuseFailAlloc_2940_, 9, v_snapshotTasks_2913_);
v___x_2920_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v_mctx_2923_; lean_object* v_zetaDeltaFVarIds_2924_; lean_object* v_postponed_2925_; lean_object* v_diag_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2938_; 
v___x_2921_ = lean_st_ref_put(v___y_2895_, v___x_2920_);
v___x_2922_ = lean_st_ref_take(v___y_2893_);
v_mctx_2923_ = lean_ctor_get(v___x_2922_, 0);
v_zetaDeltaFVarIds_2924_ = lean_ctor_get(v___x_2922_, 2);
v_postponed_2925_ = lean_ctor_get(v___x_2922_, 3);
v_diag_2926_ = lean_ctor_get(v___x_2922_, 4);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2938_ == 0)
{
lean_object* v_unused_2939_; 
v_unused_2939_ = lean_ctor_get(v___x_2922_, 1);
lean_dec(v_unused_2939_);
v___x_2928_ = v___x_2922_;
v_isShared_2929_ = v_isSharedCheck_2938_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_diag_2926_);
lean_inc(v_postponed_2925_);
lean_inc(v_zetaDeltaFVarIds_2924_);
lean_inc(v_mctx_2923_);
lean_dec(v___x_2922_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2938_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2930_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 1, v___x_2930_);
v___x_2932_ = v___x_2928_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_mctx_2923_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2937_, 2, v_zetaDeltaFVarIds_2924_);
lean_ctor_set(v_reuseFailAlloc_2937_, 3, v_postponed_2925_);
lean_ctor_set(v_reuseFailAlloc_2937_, 4, v_diag_2926_);
v___x_2932_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2935_; 
v___x_2933_ = lean_st_ref_put(v___y_2893_, v___x_2932_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v_declName_2889_);
v___x_2935_ = v___x_2898_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_declName_2889_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
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
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v_declName_2889_);
v_a_2945_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2896_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2896_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_modifiers_2879_ = stack[0].m_obj;
lean_object* v_declName_2880_ = stack[1].m_obj;
lean_object* v___y_2881_ = stack[2].m_obj;
lean_object* v___y_2882_ = stack[3].m_obj;
lean_object* v___y_2883_ = stack[4].m_obj;
lean_object* v___y_2884_ = stack[5].m_obj;
lean_object* v___y_2885_ = stack[6].m_obj;
lean_object* v___y_2886_ = stack[7].m_obj;
lean_object* v_res_2960_;
v_res_2960_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2879_, v_declName_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
stack->m_obj
 = v_res_2960_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4___boxed(lean_object* v_modifiers_2961_, lean_object* v_declName_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2961_, v_declName_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v_modifiers_2961_);
return v_res_2970_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(lean_object* v_pre_2971_, lean_object* v_declName_2972_, lean_object* v_as_2973_, size_t v_sz_2974_, size_t v_i_2975_, lean_object* v_b_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v_a_2985_; uint8_t v___x_2989_; 
v___x_2989_ = lean_usize_dec_lt(v_i_2975_, v_sz_2974_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; 
lean_dec(v_declName_2972_);
lean_dec(v_pre_2971_);
v___x_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2990_, 0, v_b_2976_);
return v___x_2990_;
}
else
{
lean_object* v___x_2991_; lean_object* v_a_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v___x_2991_ = lean_box(0);
v_a_2992_ = lean_array_uget_borrowed(v_as_2973_, v_i_2975_);
lean_inc(v_a_2992_);
lean_inc(v_pre_2971_);
v___x_2993_ = l_Lean_Name_append(v_pre_2971_, v_a_2992_);
v___x_2994_ = lean_name_eq(v___x_2993_, v_declName_2972_);
lean_dec(v___x_2993_);
if (v___x_2994_ == 0)
{
v_a_2985_ = v___x_2991_;
goto v___jp_2984_;
}
else
{
lean_object* v___x_2995_; uint8_t v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_2995_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_2996_ = 0;
lean_inc(v_declName_2972_);
v___x_2997_ = l_Lean_MessageData_ofConstName(v_declName_2972_, v___x_2996_);
v___x_2998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2995_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_3000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2998_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
lean_inc(v_pre_2971_);
v___x_3001_ = l_Lean_MessageData_ofName(v_pre_2971_);
v___x_3002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3000_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
v___x_3003_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_3004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3002_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
lean_inc(v_a_2992_);
v___x_3005_ = l_Lean_MessageData_ofName(v_a_2992_);
v___x_3006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3004_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
v___x_3007_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_3008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3008_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_dec_ref_known(v___x_3009_, 1);
v_a_2985_ = v___x_2991_;
goto v___jp_2984_;
}
else
{
lean_dec(v_declName_2972_);
lean_dec(v_pre_2971_);
return v___x_3009_;
}
}
}
v___jp_2984_:
{
size_t v___x_2986_; size_t v___x_2987_; 
v___x_2986_ = ((size_t)1ULL);
v___x_2987_ = lean_usize_add(v_i_2975_, v___x_2986_);
v_i_2975_ = v___x_2987_;
v_b_2976_ = v_a_2985_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2971_ = stack[0].m_obj;
lean_object* v_declName_2972_ = stack[1].m_obj;
lean_object* v_as_2973_ = stack[2].m_obj;
size_t v_sz_2974_ = stack[3].m_num;
size_t v_i_2975_ = stack[4].m_num;
lean_object* v_b_2976_ = stack[5].m_obj;
lean_object* v___y_2977_ = stack[6].m_obj;
lean_object* v___y_2978_ = stack[7].m_obj;
lean_object* v___y_2979_ = stack[8].m_obj;
lean_object* v___y_2980_ = stack[9].m_obj;
lean_object* v___y_2981_ = stack[10].m_obj;
lean_object* v___y_2982_ = stack[11].m_obj;
lean_object* v_res_3010_;
v_res_3010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2971_, v_declName_2972_, v_as_2973_, v_sz_2974_, v_i_2975_, v_b_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
stack->m_obj
 = v_res_3010_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6___boxed(lean_object* v_pre_3011_, lean_object* v_declName_3012_, lean_object* v_as_3013_, lean_object* v_sz_3014_, lean_object* v_i_3015_, lean_object* v_b_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
size_t v_sz_boxed_3024_; size_t v_i_boxed_3025_; lean_object* v_res_3026_; 
v_sz_boxed_3024_ = lean_unbox_usize(v_sz_3014_);
lean_dec(v_sz_3014_);
v_i_boxed_3025_ = lean_unbox_usize(v_i_3015_);
lean_dec(v_i_3015_);
v_res_3026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_3011_, v_declName_3012_, v_as_3013_, v_sz_boxed_3024_, v_i_boxed_3025_, v_b_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec_ref(v_as_3013_);
return v_res_3026_;
}
}
lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(lean_object* v_declName_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
if (lean_obj_tag(v_declName_3027_) == 1)
{
lean_object* v_pre_3035_; lean_object* v___x_3036_; lean_object* v_env_3037_; uint8_t v___x_3038_; 
v_pre_3035_ = lean_ctor_get(v_declName_3027_, 0);
lean_inc_n(v_pre_3035_, 2);
v___x_3036_ = lean_st_ref_get(v___y_3033_);
v_env_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc_ref(v_env_3037_);
lean_dec(v___x_3036_);
v___x_3038_ = l_Lean_isStructure(v_env_3037_, v_pre_3035_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
lean_dec_ref_known(v_declName_3027_, 2);
lean_dec(v_pre_3035_);
v___x_3039_ = lean_box(0);
v___x_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
return v___x_3040_;
}
else
{
lean_object* v___x_3041_; lean_object* v_env_3042_; lean_object* v_fieldNames_3043_; lean_object* v___x_3044_; size_t v_sz_3045_; size_t v___x_3046_; lean_object* v___x_3047_; 
v___x_3041_ = lean_st_ref_get(v___y_3033_);
v_env_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc_ref(v_env_3042_);
lean_dec(v___x_3041_);
lean_inc(v_pre_3035_);
v_fieldNames_3043_ = l_Lean_getStructureFieldsFlattened(v_env_3042_, v_pre_3035_, v___x_3038_);
v___x_3044_ = lean_box(0);
v_sz_3045_ = lean_array_size(v_fieldNames_3043_);
v___x_3046_ = ((size_t)0ULL);
v___x_3047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_3035_, v_declName_3027_, v_fieldNames_3043_, v_sz_3045_, v___x_3046_, v___x_3044_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
lean_dec_ref(v_fieldNames_3043_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; 
v_unused_3055_ = lean_ctor_get(v___x_3047_, 0);
lean_dec(v_unused_3055_);
v___x_3049_ = v___x_3047_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_dec(v___x_3047_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v___x_3044_);
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3044_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
else
{
return v___x_3047_;
}
}
}
else
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
lean_dec(v_declName_3027_);
v___x_3056_ = lean_box(0);
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
return v___x_3057_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3027_ = stack[0].m_obj;
lean_object* v___y_3028_ = stack[1].m_obj;
lean_object* v___y_3029_ = stack[2].m_obj;
lean_object* v___y_3030_ = stack[3].m_obj;
lean_object* v___y_3031_ = stack[4].m_obj;
lean_object* v___y_3032_ = stack[5].m_obj;
lean_object* v___y_3033_ = stack[6].m_obj;
lean_object* v_res_3058_;
v_res_3058_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v_declName_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
stack->m_obj
 = v_res_3058_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3___boxed(lean_object* v_declName_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v_declName_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
return v_res_3067_;
}
}
lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(lean_object* v_currNamespace_3068_, lean_object* v_modifiers_3069_, lean_object* v_shortName_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3084_; lean_object* v_shortName_3085_; lean_object* v_currNamespace_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v_view_3146_; lean_object* v_name_3147_; lean_object* v_imported_3148_; lean_object* v_ctx_3149_; lean_object* v_scopes_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3208_; 
lean_inc(v_shortName_3070_);
v_view_3146_ = l_Lean_extractMacroScopes(v_shortName_3070_);
v_name_3147_ = lean_ctor_get(v_view_3146_, 0);
v_imported_3148_ = lean_ctor_get(v_view_3146_, 1);
v_ctx_3149_ = lean_ctor_get(v_view_3146_, 2);
v_scopes_3150_ = lean_ctor_get(v_view_3146_, 3);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_view_3146_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3152_ = v_view_3146_;
v_isShared_3153_ = v_isSharedCheck_3208_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_scopes_3150_);
lean_inc(v_ctx_3149_);
lean_inc(v_imported_3148_);
lean_inc(v_name_3147_);
lean_dec(v_view_3146_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3208_;
goto v_resetjp_3151_;
}
v___jp_3078_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___y_3079_);
lean_ctor_set(v___x_3081_, 1, v___y_3080_);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
return v___x_3082_;
}
v___jp_3083_:
{
lean_object* v___x_3093_; 
lean_inc(v___y_3084_);
v___x_3093_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v___y_3084_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v___x_3094_; 
lean_dec_ref_known(v___x_3093_, 1);
v___x_3094_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_3069_, v___y_3084_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
if (lean_obj_tag(v___x_3094_) == 0)
{
uint8_t v_isProtected_3095_; 
v_isProtected_3095_ = lean_ctor_get_uint8(v_modifiers_3069_, sizeof(void*)*3 + 1);
if (v_isProtected_3095_ == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3104_; 
lean_dec(v_currNamespace_3086_);
v_a_3096_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3098_ = v___x_3094_;
v_isShared_3099_ = v_isSharedCheck_3104_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3094_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3104_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3100_; lean_object* v___x_3102_; 
v___x_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3100_, 0, v_a_3096_);
lean_ctor_set(v___x_3100_, 1, v_shortName_3085_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 0, v___x_3100_);
v___x_3102_ = v___x_3098_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3100_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
else
{
if (lean_obj_tag(v_currNamespace_3086_) == 1)
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3117_; 
v_a_3105_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3107_ = v___x_3094_;
v_isShared_3108_ = v_isSharedCheck_3117_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3094_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3117_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v_str_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
v_str_3109_ = lean_ctor_get(v_currNamespace_3086_, 1);
lean_inc_ref(v_str_3109_);
lean_dec_ref_known(v_currNamespace_3086_, 2);
v___x_3110_ = lean_box(0);
v___x_3111_ = l_Lean_Name_str___override(v___x_3110_, v_str_3109_);
v___x_3112_ = l_Lean_Name_append(v___x_3111_, v_shortName_3085_);
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v_a_3105_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v___x_3113_);
v___x_3115_ = v___x_3107_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
else
{
lean_object* v_a_3118_; uint8_t v___x_3119_; 
lean_dec(v_currNamespace_3086_);
v_a_3118_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3094_, 1);
v___x_3119_ = l_Lean_Name_isAtomic(v_shortName_3085_);
if (v___x_3119_ == 0)
{
v___y_3079_ = v_a_3118_;
v___y_3080_ = v_shortName_3085_;
goto v___jp_3078_;
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec(v_a_3118_);
lean_dec(v_shortName_3085_);
v___x_3120_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_3121_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3120_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3121_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
}
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_dec(v_currNamespace_3086_);
lean_dec(v_shortName_3085_);
v_a_3130_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3094_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3094_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec(v_currNamespace_3086_);
lean_dec(v_shortName_3085_);
lean_dec(v___y_3084_);
v_a_3138_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3093_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3093_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
v_resetjp_3151_:
{
lean_object* v___x_3154_; uint8_t v_isRootName_3155_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; uint8_t v___x_3197_; 
v___x_3154_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_3155_ = l_Lean_Name_isPrefixOf(v___x_3154_, v_name_3147_);
v___x_3197_ = lean_name_eq(v_name_3147_, v___x_3154_);
if (v___x_3197_ == 0)
{
v___y_3184_ = v___y_3071_;
v___y_3185_ = v___y_3072_;
v___y_3186_ = v___y_3073_;
v___y_3187_ = v___y_3074_;
v___y_3188_ = v___y_3075_;
v___y_3189_ = v___y_3076_;
goto v___jp_3183_;
}
else
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_del_object(v___x_3152_);
lean_dec(v_scopes_3150_);
lean_dec(v_ctx_3149_);
lean_dec(v_imported_3148_);
lean_dec(v_name_3147_);
lean_dec(v_shortName_3070_);
lean_dec(v_currNamespace_3068_);
v___x_3198_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_3199_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3198_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
v___jp_3156_:
{
if (v_isRootName_3155_ == 0)
{
lean_dec(v_name_3147_);
v___y_3084_ = v___y_3163_;
v_shortName_3085_ = v_shortName_3070_;
v_currNamespace_3086_ = v_currNamespace_3068_;
v___y_3087_ = v___y_3161_;
v___y_3088_ = v___y_3160_;
v___y_3089_ = v___y_3159_;
v___y_3090_ = v___y_3162_;
v___y_3091_ = v___y_3158_;
v___y_3092_ = v___y_3157_;
goto v___jp_3083_;
}
else
{
lean_dec(v_shortName_3070_);
lean_dec(v_currNamespace_3068_);
if (lean_obj_tag(v_name_3147_) == 1)
{
lean_object* v_pre_3164_; lean_object* v_str_3165_; lean_object* v___x_3166_; lean_object* v_shortName_3167_; lean_object* v_currNamespace_3168_; 
v_pre_3164_ = lean_ctor_get(v_name_3147_, 0);
lean_inc(v_pre_3164_);
v_str_3165_ = lean_ctor_get(v_name_3147_, 1);
lean_inc_ref(v_str_3165_);
lean_dec_ref_known(v_name_3147_, 2);
v___x_3166_ = lean_box(0);
v_shortName_3167_ = l_Lean_Name_str___override(v___x_3166_, v_str_3165_);
v_currNamespace_3168_ = l_Lean_Name_replacePrefix(v_pre_3164_, v___x_3154_, v___x_3166_);
v___y_3084_ = v___y_3163_;
v_shortName_3085_ = v_shortName_3167_;
v_currNamespace_3086_ = v_currNamespace_3168_;
v___y_3087_ = v___y_3161_;
v___y_3088_ = v___y_3160_;
v___y_3089_ = v___y_3159_;
v___y_3090_ = v___y_3162_;
v___y_3091_ = v___y_3158_;
v___y_3092_ = v___y_3157_;
goto v___jp_3083_;
}
else
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_dec(v___y_3163_);
v___x_3169_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_3170_ = l_Lean_MessageData_ofName(v_name_3147_);
v___x_3171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3169_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_3173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3171_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
v___x_3174_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3173_, v___y_3161_, v___y_3160_, v___y_3159_, v___y_3162_, v___y_3158_, v___y_3157_);
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3174_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3174_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
}
v___jp_3183_:
{
if (v_isRootName_3155_ == 0)
{
lean_object* v___x_3190_; 
lean_del_object(v___x_3152_);
lean_dec(v_scopes_3150_);
lean_dec(v_ctx_3149_);
lean_dec(v_imported_3148_);
lean_inc(v_shortName_3070_);
lean_inc(v_currNamespace_3068_);
v___x_3190_ = l_Lean_Name_append(v_currNamespace_3068_, v_shortName_3070_);
v___y_3157_ = v___y_3189_;
v___y_3158_ = v___y_3188_;
v___y_3159_ = v___y_3186_;
v___y_3160_ = v___y_3185_;
v___y_3161_ = v___y_3184_;
v___y_3162_ = v___y_3187_;
v___y_3163_ = v___x_3190_;
goto v___jp_3156_;
}
else
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3194_; 
v___x_3191_ = lean_box(0);
lean_inc(v_name_3147_);
v___x_3192_ = l_Lean_Name_replacePrefix(v_name_3147_, v___x_3154_, v___x_3191_);
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 0, v___x_3192_);
v___x_3194_ = v___x_3152_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3192_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v_imported_3148_);
lean_ctor_set(v_reuseFailAlloc_3196_, 2, v_ctx_3149_);
lean_ctor_set(v_reuseFailAlloc_3196_, 3, v_scopes_3150_);
v___x_3194_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_MacroScopesView_review(v___x_3194_);
v___y_3157_ = v___y_3189_;
v___y_3158_ = v___y_3188_;
v___y_3159_ = v___y_3186_;
v___y_3160_ = v___y_3185_;
v___y_3161_ = v___y_3184_;
v___y_3162_ = v___y_3187_;
v___y_3163_ = v___x_3195_;
goto v___jp_3156_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_currNamespace_3068_ = stack[0].m_obj;
lean_object* v_modifiers_3069_ = stack[1].m_obj;
lean_object* v_shortName_3070_ = stack[2].m_obj;
lean_object* v___y_3071_ = stack[3].m_obj;
lean_object* v___y_3072_ = stack[4].m_obj;
lean_object* v___y_3073_ = stack[5].m_obj;
lean_object* v___y_3074_ = stack[6].m_obj;
lean_object* v___y_3075_ = stack[7].m_obj;
lean_object* v___y_3076_ = stack[8].m_obj;
lean_object* v_res_3209_;
v_res_3209_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3068_, v_modifiers_3069_, v_shortName_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
stack->m_obj
 = v_res_3209_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2___boxed(lean_object* v_currNamespace_3210_, lean_object* v_modifiers_3211_, lean_object* v_shortName_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3210_, v_modifiers_3211_, v_shortName_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec_ref(v_modifiers_3211_);
return v_res_3220_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(uint8_t v___x_3221_, lean_object* v_as_3222_, size_t v_i_3223_, size_t v_stop_3224_, lean_object* v_b_3225_){
_start:
{
lean_object* v___y_3227_; uint8_t v___x_3231_; 
v___x_3231_ = lean_usize_dec_eq(v_i_3223_, v_stop_3224_);
if (v___x_3231_ == 0)
{
lean_object* v_fst_3232_; uint8_t v___x_3233_; 
v_fst_3232_ = lean_ctor_get(v_b_3225_, 0);
v___x_3233_ = lean_unbox(v_fst_3232_);
if (v___x_3233_ == 0)
{
lean_object* v_snd_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3243_; 
v_snd_3234_ = lean_ctor_get(v_b_3225_, 1);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_b_3225_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; 
v_unused_3244_ = lean_ctor_get(v_b_3225_, 0);
lean_dec(v_unused_3244_);
v___x_3236_ = v_b_3225_;
v_isShared_3237_ = v_isSharedCheck_3243_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_snd_3234_);
lean_dec(v_b_3225_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3243_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
uint8_t v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3238_ = 1;
v___x_3239_ = lean_box(v___x_3238_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v___x_3239_);
v___x_3241_ = v___x_3236_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
lean_ctor_set(v_reuseFailAlloc_3242_, 1, v_snd_3234_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
v___y_3227_ = v___x_3241_;
goto v___jp_3226_;
}
}
}
else
{
lean_object* v_snd_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3255_; 
v_snd_3245_ = lean_ctor_get(v_b_3225_, 1);
v_isSharedCheck_3255_ = !lean_is_exclusive(v_b_3225_);
if (v_isSharedCheck_3255_ == 0)
{
lean_object* v_unused_3256_; 
v_unused_3256_ = lean_ctor_get(v_b_3225_, 0);
lean_dec(v_unused_3256_);
v___x_3247_ = v_b_3225_;
v_isShared_3248_ = v_isSharedCheck_3255_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_snd_3245_);
lean_dec(v_b_3225_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3255_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3253_; 
v___x_3249_ = lean_array_uget_borrowed(v_as_3222_, v_i_3223_);
lean_inc(v___x_3249_);
v___x_3250_ = lean_array_push(v_snd_3245_, v___x_3249_);
v___x_3251_ = lean_box(v___x_3221_);
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 1, v___x_3250_);
lean_ctor_set(v___x_3247_, 0, v___x_3251_);
v___x_3253_ = v___x_3247_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v___x_3250_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
v___y_3227_ = v___x_3253_;
goto v___jp_3226_;
}
}
}
}
else
{
return v_b_3225_;
}
v___jp_3226_:
{
size_t v___x_3228_; size_t v___x_3229_; 
v___x_3228_ = ((size_t)1ULL);
v___x_3229_ = lean_usize_add(v_i_3223_, v___x_3228_);
v_i_3223_ = v___x_3229_;
v_b_3225_ = v___y_3227_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3221_ = stack[0].m_num;
lean_object* v_as_3222_ = stack[1].m_obj;
size_t v_i_3223_ = stack[2].m_num;
size_t v_stop_3224_ = stack[3].m_num;
lean_object* v_b_3225_ = stack[4].m_obj;
lean_object* v_res_3257_;
v_res_3257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3221_, v_as_3222_, v_i_3223_, v_stop_3224_, v_b_3225_);
stack->m_obj
 = v_res_3257_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4___boxed(lean_object* v___x_3258_, lean_object* v_as_3259_, lean_object* v_i_3260_, lean_object* v_stop_3261_, lean_object* v_b_3262_){
_start:
{
uint8_t v___x_19507__boxed_3263_; size_t v_i_boxed_3264_; size_t v_stop_boxed_3265_; lean_object* v_res_3266_; 
v___x_19507__boxed_3263_ = lean_unbox(v___x_3258_);
v_i_boxed_3264_ = lean_unbox_usize(v_i_3260_);
lean_dec(v_i_3260_);
v_stop_boxed_3265_ = lean_unbox_usize(v_stop_3261_);
lean_dec(v_stop_3261_);
v_res_3266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_19507__boxed_3263_, v_as_3259_, v_i_boxed_3264_, v_stop_boxed_3265_, v_b_3262_);
lean_dec_ref(v_as_3259_);
return v_res_3266_;
}
}
uint8_t l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(lean_object* v_a_3267_, lean_object* v_x_3268_){
_start:
{
if (lean_obj_tag(v_x_3268_) == 0)
{
uint8_t v___x_3269_; 
v___x_3269_ = 0;
return v___x_3269_;
}
else
{
lean_object* v_head_3270_; lean_object* v_tail_3271_; uint8_t v___x_3272_; 
v_head_3270_ = lean_ctor_get(v_x_3268_, 0);
v_tail_3271_ = lean_ctor_get(v_x_3268_, 1);
v___x_3272_ = lean_name_eq(v_a_3267_, v_head_3270_);
if (v___x_3272_ == 0)
{
v_x_3268_ = v_tail_3271_;
goto _start;
}
else
{
return v___x_3272_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_Elab_expandDeclId_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3267_ = stack[0].m_obj;
lean_object* v_x_3268_ = stack[1].m_obj;
uint8_t v_res_3274_;
v_res_3274_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_a_3267_, v_x_3268_);
stack->m_num = v_res_3274_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_expandDeclId_spec__0___boxed(lean_object* v_a_3275_, lean_object* v_x_3276_){
_start:
{
uint8_t v_res_3277_; lean_object* v_r_3278_; 
v_res_3277_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_a_3275_, v_x_3276_);
lean_dec(v_x_3276_);
lean_dec(v_a_3275_);
v_r_3278_ = lean_box(v_res_3277_);
return v_r_3278_;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = ((lean_object*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0));
v___x_3281_ = l_Lean_stringToMessageData(v___x_3280_);
return v___x_3281_;
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(lean_object* v_u_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3290_ = lean_obj_once(&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1, &l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1);
v___x_3291_ = l_Lean_MessageData_ofName(v_u_3282_);
v___x_3292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3290_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_3294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3292_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3294_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
return v___x_3295_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_3282_ = stack[0].m_obj;
lean_object* v___y_3283_ = stack[1].m_obj;
lean_object* v___y_3284_ = stack[2].m_obj;
lean_object* v___y_3285_ = stack[3].m_obj;
lean_object* v___y_3286_ = stack[4].m_obj;
lean_object* v___y_3287_ = stack[5].m_obj;
lean_object* v___y_3288_ = stack[6].m_obj;
lean_object* v_res_3296_;
v_res_3296_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
stack->m_obj
 = v_res_3296_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___boxed(lean_object* v_u_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
return v_res_3305_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(lean_object* v_as_3306_, size_t v_i_3307_, size_t v_stop_3308_, lean_object* v_b_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_a_3318_; uint8_t v___x_3322_; 
v___x_3322_ = lean_usize_dec_eq(v_i_3307_, v_stop_3308_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v_id_3324_; uint8_t v___x_3325_; 
v___x_3323_ = lean_array_uget_borrowed(v_as_3306_, v_i_3307_);
v_id_3324_ = l_Lean_Syntax_getId(v___x_3323_);
v___x_3325_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_id_3324_, v_b_3309_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; 
v___x_3326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3326_, 0, v_id_3324_);
lean_ctor_set(v___x_3326_, 1, v_b_3309_);
v_a_3318_ = v___x_3326_;
goto v___jp_3317_;
}
else
{
lean_object* v_toCold_3327_; lean_object* v_currRecDepth_3328_; lean_object* v_ref_3329_; uint16_t v_optionFlags_3330_; uint8_t v_suppressElabErrors_3331_; uint8_t v_isRecordingDeps_3332_; lean_object* v_ref_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec(v_b_3309_);
v_toCold_3327_ = lean_ctor_get(v___y_3314_, 0);
v_currRecDepth_3328_ = lean_ctor_get(v___y_3314_, 1);
v_ref_3329_ = lean_ctor_get(v___y_3314_, 2);
v_optionFlags_3330_ = lean_ctor_get_uint16(v___y_3314_, sizeof(void*)*3);
v_suppressElabErrors_3331_ = lean_ctor_get_uint8(v___y_3314_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3332_ = lean_ctor_get_uint8(v___y_3314_, sizeof(void*)*3 + 3);
v_ref_3333_ = l_Lean_replaceRef(v___x_3323_, v_ref_3329_);
lean_inc(v_currRecDepth_3328_);
lean_inc_ref(v_toCold_3327_);
v___x_3334_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3334_, 0, v_toCold_3327_);
lean_ctor_set(v___x_3334_, 1, v_currRecDepth_3328_);
lean_ctor_set(v___x_3334_, 2, v_ref_3333_);
lean_ctor_set_uint16(v___x_3334_, sizeof(void*)*3, v_optionFlags_3330_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*3 + 2, v_suppressElabErrors_3331_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*3 + 3, v_isRecordingDeps_3332_);
v___x_3335_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_id_3324_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___x_3334_, v___y_3315_);
lean_dec_ref_known(v___x_3334_, 3);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3335_, 1);
v_a_3318_ = v_a_3336_;
goto v___jp_3317_;
}
else
{
return v___x_3335_;
}
}
}
else
{
lean_object* v___x_3337_; 
v___x_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3337_, 0, v_b_3309_);
return v___x_3337_;
}
v___jp_3317_:
{
size_t v___x_3319_; size_t v___x_3320_; 
v___x_3319_ = ((size_t)1ULL);
v___x_3320_ = lean_usize_add(v_i_3307_, v___x_3319_);
v_i_3307_ = v___x_3320_;
v_b_3309_ = v_a_3318_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3306_ = stack[0].m_obj;
size_t v_i_3307_ = stack[1].m_num;
size_t v_stop_3308_ = stack[2].m_num;
lean_object* v_b_3309_ = stack[3].m_obj;
lean_object* v___y_3310_ = stack[4].m_obj;
lean_object* v___y_3311_ = stack[5].m_obj;
lean_object* v___y_3312_ = stack[6].m_obj;
lean_object* v___y_3313_ = stack[7].m_obj;
lean_object* v___y_3314_ = stack[8].m_obj;
lean_object* v___y_3315_ = stack[9].m_obj;
lean_object* v_res_3338_;
v_res_3338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v_as_3306_, v_i_3307_, v_stop_3308_, v_b_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
stack->m_obj
 = v_res_3338_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3___boxed(lean_object* v_as_3339_, lean_object* v_i_3340_, lean_object* v_stop_3341_, lean_object* v_b_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
size_t v_i_boxed_3350_; size_t v_stop_boxed_3351_; lean_object* v_res_3352_; 
v_i_boxed_3350_ = lean_unbox_usize(v_i_3340_);
lean_dec(v_i_3340_);
v_stop_boxed_3351_ = lean_unbox_usize(v_stop_3341_);
lean_dec(v_stop_3341_);
v_res_3352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v_as_3339_, v_i_boxed_3350_, v_stop_boxed_3351_, v_b_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec_ref(v_as_3339_);
return v_res_3352_;
}
}
lean_object* l_Lean_Elab_expandDeclId(lean_object* v_currNamespace_3353_, lean_object* v_currLevelNames_3354_, lean_object* v_declId_3355_, lean_object* v_modifiers_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_){
_start:
{
lean_object* v___x_3364_; lean_object* v_fst_3365_; lean_object* v_snd_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3446_; 
v___x_3364_ = l_Lean_Elab_expandDeclIdCore(v_declId_3355_);
v_fst_3365_ = lean_ctor_get(v___x_3364_, 0);
v_snd_3366_ = lean_ctor_get(v___x_3364_, 1);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3368_ = v___x_3364_;
v_isShared_3369_ = v_isSharedCheck_3446_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_snd_3366_);
lean_inc(v_fst_3365_);
lean_dec(v___x_3364_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3446_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v_levelNames_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3408_; lean_object* v___y_3419_; uint8_t v___x_3430_; 
v___x_3430_ = l_Lean_Syntax_isNone(v_snd_3366_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v___x_3431_ = lean_unsigned_to_nat(1u);
v___x_3432_ = l_Lean_Syntax_getArg(v_snd_3366_, v___x_3431_);
lean_dec(v_snd_3366_);
v___x_3433_ = l_Lean_Syntax_getArgs(v___x_3432_);
lean_dec(v___x_3432_);
v___x_3434_ = lean_unsigned_to_nat(0u);
v___x_3435_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__0));
v___x_3436_ = lean_array_get_size(v___x_3433_);
v___x_3437_ = lean_nat_dec_lt(v___x_3434_, v___x_3436_);
if (v___x_3437_ == 0)
{
lean_dec_ref(v___x_3433_);
lean_del_object(v___x_3368_);
v___y_3419_ = v___x_3435_;
goto v___jp_3418_;
}
else
{
lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3438_ = lean_box(v___x_3437_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 1, v___x_3435_);
lean_ctor_set(v___x_3368_, 0, v___x_3438_);
v___x_3440_ = v___x_3368_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3438_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3435_);
v___x_3440_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
size_t v___x_3441_; size_t v___x_3442_; lean_object* v___x_3443_; lean_object* v_snd_3444_; 
v___x_3441_ = ((size_t)0ULL);
v___x_3442_ = lean_usize_of_nat(v___x_3436_);
v___x_3443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3430_, v___x_3433_, v___x_3441_, v___x_3442_, v___x_3440_);
lean_dec_ref(v___x_3433_);
v_snd_3444_ = lean_ctor_get(v___x_3443_, 1);
lean_inc(v_snd_3444_);
lean_dec_ref(v___x_3443_);
v___y_3419_ = v_snd_3444_;
goto v___jp_3418_;
}
}
}
else
{
lean_del_object(v___x_3368_);
lean_dec(v_snd_3366_);
v_levelNames_3371_ = v_currLevelNames_3354_;
v___y_3372_ = v_a_3357_;
v___y_3373_ = v_a_3358_;
v___y_3374_ = v_a_3359_;
v___y_3375_ = v_a_3360_;
v___y_3376_ = v_a_3361_;
v___y_3377_ = v_a_3362_;
goto v___jp_3370_;
}
v___jp_3370_:
{
lean_object* v_toCold_3378_; lean_object* v_currRecDepth_3379_; lean_object* v_ref_3380_; uint16_t v_optionFlags_3381_; uint8_t v_suppressElabErrors_3382_; uint8_t v_isRecordingDeps_3383_; lean_object* v_ref_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v_toCold_3378_ = lean_ctor_get(v___y_3376_, 0);
v_currRecDepth_3379_ = lean_ctor_get(v___y_3376_, 1);
v_ref_3380_ = lean_ctor_get(v___y_3376_, 2);
v_optionFlags_3381_ = lean_ctor_get_uint16(v___y_3376_, sizeof(void*)*3);
v_suppressElabErrors_3382_ = lean_ctor_get_uint8(v___y_3376_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3383_ = lean_ctor_get_uint8(v___y_3376_, sizeof(void*)*3 + 3);
v_ref_3384_ = l_Lean_replaceRef(v_declId_3355_, v_ref_3380_);
lean_inc(v_currRecDepth_3379_);
lean_inc_ref(v_toCold_3378_);
v___x_3385_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3385_, 0, v_toCold_3378_);
lean_ctor_set(v___x_3385_, 1, v_currRecDepth_3379_);
lean_ctor_set(v___x_3385_, 2, v_ref_3384_);
lean_ctor_set_uint16(v___x_3385_, sizeof(void*)*3, v_optionFlags_3381_);
lean_ctor_set_uint8(v___x_3385_, sizeof(void*)*3 + 2, v_suppressElabErrors_3382_);
lean_ctor_set_uint8(v___x_3385_, sizeof(void*)*3 + 3, v_isRecordingDeps_3383_);
v___x_3386_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3353_, v_modifiers_3356_, v_fst_3365_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___x_3385_, v___y_3377_);
lean_dec_ref_known(v___x_3385_, 3);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3398_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3389_ = v___x_3386_;
v_isShared_3390_ = v_isSharedCheck_3398_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3398_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v_fst_3391_; lean_object* v_snd_3392_; lean_object* v_docString_x3f_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
v_fst_3391_ = lean_ctor_get(v_a_3387_, 0);
lean_inc(v_fst_3391_);
v_snd_3392_ = lean_ctor_get(v_a_3387_, 1);
lean_inc(v_snd_3392_);
lean_dec(v_a_3387_);
v_docString_x3f_3393_ = lean_ctor_get(v_modifiers_3356_, 1);
lean_inc(v_docString_x3f_3393_);
v___x_3394_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3394_, 0, v_snd_3392_);
lean_ctor_set(v___x_3394_, 1, v_fst_3391_);
lean_ctor_set(v___x_3394_, 2, v_levelNames_3371_);
lean_ctor_set(v___x_3394_, 3, v_docString_x3f_3393_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v___x_3394_);
v___x_3396_ = v___x_3389_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec(v_levelNames_3371_);
v_a_3399_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3386_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3386_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
v___jp_3407_:
{
if (lean_obj_tag(v___y_3408_) == 0)
{
lean_object* v_a_3409_; 
v_a_3409_ = lean_ctor_get(v___y_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref_known(v___y_3408_, 1);
v_levelNames_3371_ = v_a_3409_;
v___y_3372_ = v_a_3357_;
v___y_3373_ = v_a_3358_;
v___y_3374_ = v_a_3359_;
v___y_3375_ = v_a_3360_;
v___y_3376_ = v_a_3361_;
v___y_3377_ = v_a_3362_;
goto v___jp_3370_;
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec(v_fst_3365_);
lean_dec(v_currNamespace_3353_);
v_a_3410_ = lean_ctor_get(v___y_3408_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___y_3408_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___y_3408_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___y_3408_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
v___jp_3418_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; 
v___x_3420_ = lean_unsigned_to_nat(0u);
v___x_3421_ = lean_array_get_size(v___y_3419_);
v___x_3422_ = lean_nat_dec_lt(v___x_3420_, v___x_3421_);
if (v___x_3422_ == 0)
{
lean_dec_ref(v___y_3419_);
v_levelNames_3371_ = v_currLevelNames_3354_;
v___y_3372_ = v_a_3357_;
v___y_3373_ = v_a_3358_;
v___y_3374_ = v_a_3359_;
v___y_3375_ = v_a_3360_;
v___y_3376_ = v_a_3361_;
v___y_3377_ = v_a_3362_;
goto v___jp_3370_;
}
else
{
uint8_t v___x_3423_; 
v___x_3423_ = lean_nat_dec_le(v___x_3421_, v___x_3421_);
if (v___x_3423_ == 0)
{
if (v___x_3422_ == 0)
{
lean_dec_ref(v___y_3419_);
v_levelNames_3371_ = v_currLevelNames_3354_;
v___y_3372_ = v_a_3357_;
v___y_3373_ = v_a_3358_;
v___y_3374_ = v_a_3359_;
v___y_3375_ = v_a_3360_;
v___y_3376_ = v_a_3361_;
v___y_3377_ = v_a_3362_;
goto v___jp_3370_;
}
else
{
size_t v___x_3424_; size_t v___x_3425_; lean_object* v___x_3426_; 
v___x_3424_ = ((size_t)0ULL);
v___x_3425_ = lean_usize_of_nat(v___x_3421_);
v___x_3426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3419_, v___x_3424_, v___x_3425_, v_currLevelNames_3354_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
lean_dec_ref(v___y_3419_);
v___y_3408_ = v___x_3426_;
goto v___jp_3407_;
}
}
else
{
size_t v___x_3427_; size_t v___x_3428_; lean_object* v___x_3429_; 
v___x_3427_ = ((size_t)0ULL);
v___x_3428_ = lean_usize_of_nat(v___x_3421_);
v___x_3429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3419_, v___x_3427_, v___x_3428_, v_currLevelNames_3354_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
lean_dec_ref(v___y_3419_);
v___y_3408_ = v___x_3429_;
goto v___jp_3407_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_expandDeclId_0interp(lean_interpreter_value* stack)
{
lean_object* v_currNamespace_3353_ = stack[0].m_obj;
lean_object* v_currLevelNames_3354_ = stack[1].m_obj;
lean_object* v_declId_3355_ = stack[2].m_obj;
lean_object* v_modifiers_3356_ = stack[3].m_obj;
lean_object* v_a_3357_ = stack[4].m_obj;
lean_object* v_a_3358_ = stack[5].m_obj;
lean_object* v_a_3359_ = stack[6].m_obj;
lean_object* v_a_3360_ = stack[7].m_obj;
lean_object* v_a_3361_ = stack[8].m_obj;
lean_object* v_a_3362_ = stack[9].m_obj;
lean_object* v_res_3447_;
v_res_3447_ = l_Lean_Elab_expandDeclId(v_currNamespace_3353_, v_currLevelNames_3354_, v_declId_3355_, v_modifiers_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
stack->m_obj
 = v_res_3447_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___boxed(lean_object* v_currNamespace_3448_, lean_object* v_currLevelNames_3449_, lean_object* v_declId_3450_, lean_object* v_modifiers_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_Elab_expandDeclId(v_currNamespace_3448_, v_currLevelNames_3449_, v_declId_3450_, v_modifiers_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
lean_dec(v_a_3457_);
lean_dec_ref(v_a_3456_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
lean_dec(v_a_3453_);
lean_dec_ref(v_a_3452_);
lean_dec_ref(v_modifiers_3451_);
lean_dec(v_declId_3450_);
return v_res_3459_;
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(lean_object* v_00_u03b1_3460_, lean_object* v_u_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v___x_3469_; 
v___x_3469_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
return v___x_3469_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_3461_ = stack[1].m_obj;
lean_object* v___y_3462_ = stack[2].m_obj;
lean_object* v___y_3463_ = stack[3].m_obj;
lean_object* v___y_3464_ = stack[4].m_obj;
lean_object* v___y_3465_ = stack[5].m_obj;
lean_object* v___y_3466_ = stack[6].m_obj;
lean_object* v___y_3467_ = stack[7].m_obj;
lean_object* v_res_3470_;
v_res_3470_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(lean_box(0), v_u_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
stack->m_obj
 = v_res_3470_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___boxed(lean_object* v_00_u03b1_3471_, lean_object* v_u_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(v_00_u03b1_3471_, v_u_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
return v_res_3480_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(lean_object* v_00_u03b1_3481_, lean_object* v_msg_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v___x_3490_; 
v___x_3490_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
return v___x_3490_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3482_ = stack[1].m_obj;
lean_object* v___y_3483_ = stack[2].m_obj;
lean_object* v___y_3484_ = stack[3].m_obj;
lean_object* v___y_3485_ = stack[4].m_obj;
lean_object* v___y_3486_ = stack[5].m_obj;
lean_object* v___y_3487_ = stack[6].m_obj;
lean_object* v___y_3488_ = stack[7].m_obj;
lean_object* v_res_3491_;
v_res_3491_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(lean_box(0), v_msg_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
stack->m_obj
 = v_res_3491_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3492_, lean_object* v_msg_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(v_00_u03b1_3492_, v_msg_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
return v_res_3501_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(lean_object* v_msgData_3502_, lean_object* v_macroStack_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_3502_, v_macroStack_3503_, v___y_3508_);
return v___x_3511_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3502_ = stack[0].m_obj;
lean_object* v_macroStack_3503_ = stack[1].m_obj;
lean_object* v___y_3504_ = stack[2].m_obj;
lean_object* v___y_3505_ = stack[3].m_obj;
lean_object* v___y_3506_ = stack[4].m_obj;
lean_object* v___y_3507_ = stack[5].m_obj;
lean_object* v___y_3508_ = stack[6].m_obj;
lean_object* v___y_3509_ = stack[7].m_obj;
lean_object* v_res_3512_;
v_res_3512_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(v_msgData_3502_, v_macroStack_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
stack->m_obj
 = v_res_3512_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_3513_, lean_object* v_macroStack_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(v_msgData_3513_, v_macroStack_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
return v_res_3522_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(lean_object* v_t_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_3523_, v___y_3529_);
return v___x_3531_;
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3523_ = stack[0].m_obj;
lean_object* v___y_3524_ = stack[1].m_obj;
lean_object* v___y_3525_ = stack[2].m_obj;
lean_object* v___y_3526_ = stack[3].m_obj;
lean_object* v___y_3527_ = stack[4].m_obj;
lean_object* v___y_3528_ = stack[5].m_obj;
lean_object* v___y_3529_ = stack[6].m_obj;
lean_object* v_res_3532_;
v_res_3532_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(v_t_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
stack->m_obj
 = v_res_3532_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___boxed(lean_object* v_t_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(v_t_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
return v_res_3541_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(lean_object* v_env_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_3542_, v___y_3546_, v___y_3548_);
return v___x_3550_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3542_ = stack[0].m_obj;
lean_object* v___y_3543_ = stack[1].m_obj;
lean_object* v___y_3544_ = stack[2].m_obj;
lean_object* v___y_3545_ = stack[3].m_obj;
lean_object* v___y_3546_ = stack[4].m_obj;
lean_object* v___y_3547_ = stack[5].m_obj;
lean_object* v___y_3548_ = stack[6].m_obj;
lean_object* v_res_3551_;
v_res_3551_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(v_env_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
stack->m_obj
 = v_res_3551_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___boxed(lean_object* v_env_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(v_env_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
return v_res_3560_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(lean_object* v_00_u03b1_3561_, lean_object* v_env_3562_, lean_object* v_x_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_3562_, v_x_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
return v___x_3571_;
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3562_ = stack[1].m_obj;
lean_object* v_x_3563_ = stack[2].m_obj;
lean_object* v___y_3564_ = stack[3].m_obj;
lean_object* v___y_3565_ = stack[4].m_obj;
lean_object* v___y_3566_ = stack[5].m_obj;
lean_object* v___y_3567_ = stack[6].m_obj;
lean_object* v___y_3568_ = stack[7].m_obj;
lean_object* v___y_3569_ = stack[8].m_obj;
lean_object* v_res_3572_;
v_res_3572_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(lean_box(0), v_env_3562_, v_x_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
stack->m_obj
 = v_res_3572_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3573_, lean_object* v_env_3574_, lean_object* v_x_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(v_00_u03b1_3573_, v_env_3574_, v_x_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
return v_res_3583_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(lean_object* v_00_u03b1_3584_, lean_object* v_constName_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
return v___x_3593_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3585_ = stack[1].m_obj;
lean_object* v___y_3586_ = stack[2].m_obj;
lean_object* v___y_3587_ = stack[3].m_obj;
lean_object* v___y_3588_ = stack[4].m_obj;
lean_object* v___y_3589_ = stack[5].m_obj;
lean_object* v___y_3590_ = stack[6].m_obj;
lean_object* v___y_3591_ = stack[7].m_obj;
lean_object* v_res_3594_;
v_res_3594_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(lean_box(0), v_constName_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
stack->m_obj
 = v_res_3594_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___boxed(lean_object* v_00_u03b1_3595_, lean_object* v_constName_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(v_00_u03b1_3595_, v_constName_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
return v_res_3604_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(lean_object* v_00_u03b1_3605_, lean_object* v_ref_3606_, lean_object* v_constName_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_3606_, v_constName_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
return v___x_3615_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3606_ = stack[1].m_obj;
lean_object* v_constName_3607_ = stack[2].m_obj;
lean_object* v___y_3608_ = stack[3].m_obj;
lean_object* v___y_3609_ = stack[4].m_obj;
lean_object* v___y_3610_ = stack[5].m_obj;
lean_object* v___y_3611_ = stack[6].m_obj;
lean_object* v___y_3612_ = stack[7].m_obj;
lean_object* v___y_3613_ = stack[8].m_obj;
lean_object* v_res_3616_;
v_res_3616_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(lean_box(0), v_ref_3606_, v_constName_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
stack->m_obj
 = v_res_3616_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___boxed(lean_object* v_00_u03b1_3617_, lean_object* v_ref_3618_, lean_object* v_constName_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(v_00_u03b1_3617_, v_ref_3618_, v_constName_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v_ref_3618_);
return v_res_3627_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(lean_object* v_00_u03b1_3628_, lean_object* v_ref_3629_, lean_object* v_msg_3630_, lean_object* v_declHint_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v___x_3639_; 
v___x_3639_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_3629_, v_msg_3630_, v_declHint_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
return v___x_3639_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3629_ = stack[1].m_obj;
lean_object* v_msg_3630_ = stack[2].m_obj;
lean_object* v_declHint_3631_ = stack[3].m_obj;
lean_object* v___y_3632_ = stack[4].m_obj;
lean_object* v___y_3633_ = stack[5].m_obj;
lean_object* v___y_3634_ = stack[6].m_obj;
lean_object* v___y_3635_ = stack[7].m_obj;
lean_object* v___y_3636_ = stack[8].m_obj;
lean_object* v___y_3637_ = stack[9].m_obj;
lean_object* v_res_3640_;
v_res_3640_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(lean_box(0), v_ref_3629_, v_msg_3630_, v_declHint_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
stack->m_obj
 = v_res_3640_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___boxed(lean_object* v_00_u03b1_3641_, lean_object* v_ref_3642_, lean_object* v_msg_3643_, lean_object* v_declHint_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(v_00_u03b1_3641_, v_ref_3642_, v_msg_3643_, v_declHint_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v_ref_3642_);
return v_res_3652_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(lean_object* v_msg_3653_, lean_object* v_declHint_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_3653_, v_declHint_3654_, v___y_3660_);
return v___x_3662_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3653_ = stack[0].m_obj;
lean_object* v_declHint_3654_ = stack[1].m_obj;
lean_object* v___y_3655_ = stack[2].m_obj;
lean_object* v___y_3656_ = stack[3].m_obj;
lean_object* v___y_3657_ = stack[4].m_obj;
lean_object* v___y_3658_ = stack[5].m_obj;
lean_object* v___y_3659_ = stack[6].m_obj;
lean_object* v___y_3660_ = stack[7].m_obj;
lean_object* v_res_3663_;
v_res_3663_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(v_msg_3653_, v_declHint_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
stack->m_obj
 = v_res_3663_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___boxed(lean_object* v_msg_3664_, lean_object* v_declHint_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(v_msg_3664_, v_declHint_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
return v_res_3673_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(lean_object* v_00_u03b1_3674_, lean_object* v_ref_3675_, lean_object* v_msg_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v___x_3684_; 
v___x_3684_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_3675_, v_msg_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
return v___x_3684_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3675_ = stack[1].m_obj;
lean_object* v_msg_3676_ = stack[2].m_obj;
lean_object* v___y_3677_ = stack[3].m_obj;
lean_object* v___y_3678_ = stack[4].m_obj;
lean_object* v___y_3679_ = stack[5].m_obj;
lean_object* v___y_3680_ = stack[6].m_obj;
lean_object* v___y_3681_ = stack[7].m_obj;
lean_object* v___y_3682_ = stack[8].m_obj;
lean_object* v_res_3685_;
v_res_3685_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(lean_box(0), v_ref_3675_, v_msg_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
stack->m_obj
 = v_res_3685_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___boxed(lean_object* v_00_u03b1_3686_, lean_object* v_ref_3687_, lean_object* v_msg_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(v_00_u03b1_3686_, v_ref_3687_, v_msg_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v_ref_3687_);
return v_res_3696_;
}
}
uint8_t l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(lean_object* v_x_3700_){
_start:
{
lean_object* v_name_3701_; lean_object* v___x_3702_; uint8_t v___x_3703_; 
v_name_3701_ = lean_ctor_get(v_x_3700_, 0);
v___x_3702_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__1));
v___x_3703_ = lean_name_eq(v_name_3701_, v___x_3702_);
return v___x_3703_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3700_ = stack[0].m_obj;
uint8_t v_res_3704_;
v_res_3704_ = l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(v_x_3700_);
stack->m_num = v_res_3704_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___boxed(lean_object* v_x_3705_){
_start:
{
uint8_t v_res_3706_; lean_object* v_r_3707_; 
v_res_3706_ = l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(v_x_3705_);
lean_dec_ref(v_x_3705_);
v_r_3707_ = lean_box(v_res_3706_);
return v_r_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__1(lean_object* v_ctx_3708_){
_start:
{
lean_object* v_declName_x3f_3709_; lean_object* v_macroStack_3710_; uint8_t v_mayPostpone_3711_; uint8_t v_errToSorry_3712_; lean_object* v_autoBoundImplicitContext_3713_; lean_object* v_autoBoundImplicitForbidden_3714_; lean_object* v_sectionVars_3715_; lean_object* v_sectionFVars_3716_; uint8_t v_implicitLambda_3717_; uint8_t v_heedElabAsElim_3718_; uint8_t v_isNoncomputableSection_3719_; uint8_t v_isMetaSection_3720_; uint8_t v_ignoreTCFailures_3721_; uint8_t v_inPattern_3722_; lean_object* v_tacSnap_x3f_3723_; uint8_t v_saveRecAppSyntax_3724_; uint8_t v_holesAsSyntheticOpaque_3725_; lean_object* v_fixedTermElabs_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3734_; 
v_declName_x3f_3709_ = lean_ctor_get(v_ctx_3708_, 0);
v_macroStack_3710_ = lean_ctor_get(v_ctx_3708_, 1);
v_mayPostpone_3711_ = lean_ctor_get_uint8(v_ctx_3708_, sizeof(void*)*8);
v_errToSorry_3712_ = lean_ctor_get_uint8(v_ctx_3708_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_3713_ = lean_ctor_get(v_ctx_3708_, 2);
v_autoBoundImplicitForbidden_3714_ = lean_ctor_get(v_ctx_3708_, 3);
v_sectionVars_3715_ = lean_ctor_get(v_ctx_3708_, 4);
v_sectionFVars_3716_ = lean_ctor_get(v_ctx_3708_, 5);
v_implicitLambda_3717_ = lean_ctor_get_uint8(v_ctx_3708_, sizeof(void*)*8 + 2);
v_heedElabAsElim_3718_ = lean_ctor_get_uint8(v_ctx_3708_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_3719_ = lean_ctor_get_uint8(v_ctx_3708_, sizeof(void*)*8 + 4);
v_isMetaSection_3720_ = lean_ctor_get_uint8(v_ctx_3708_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_3721_ = lean_ctor_get_uint8(v_ctx_3708_, sizeof(void*)*8 + 6);
v_inPattern_3722_ = lean_ctor_get_uint8(v_ctx_3708_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_3723_ = lean_ctor_get(v_ctx_3708_, 6);
v_saveRecAppSyntax_3724_ = lean_ctor_get_uint8(v_ctx_3708_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_3725_ = lean_ctor_get_uint8(v_ctx_3708_, sizeof(void*)*8 + 9);
v_fixedTermElabs_3726_ = lean_ctor_get(v_ctx_3708_, 7);
v_isSharedCheck_3734_ = !lean_is_exclusive(v_ctx_3708_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3728_ = v_ctx_3708_;
v_isShared_3729_ = v_isSharedCheck_3734_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_fixedTermElabs_3726_);
lean_inc(v_tacSnap_x3f_3723_);
lean_inc(v_sectionFVars_3716_);
lean_inc(v_sectionVars_3715_);
lean_inc(v_autoBoundImplicitForbidden_3714_);
lean_inc(v_autoBoundImplicitContext_3713_);
lean_inc(v_macroStack_3710_);
lean_inc(v_declName_x3f_3709_);
lean_dec(v_ctx_3708_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3734_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
uint8_t v___x_3730_; lean_object* v___x_3732_; 
v___x_3730_ = 0;
if (v_isShared_3729_ == 0)
{
v___x_3732_ = v___x_3728_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_declName_x3f_3709_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_macroStack_3710_);
lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_autoBoundImplicitContext_3713_);
lean_ctor_set(v_reuseFailAlloc_3733_, 3, v_autoBoundImplicitForbidden_3714_);
lean_ctor_set(v_reuseFailAlloc_3733_, 4, v_sectionVars_3715_);
lean_ctor_set(v_reuseFailAlloc_3733_, 5, v_sectionFVars_3716_);
lean_ctor_set(v_reuseFailAlloc_3733_, 6, v_tacSnap_x3f_3723_);
lean_ctor_set(v_reuseFailAlloc_3733_, 7, v_fixedTermElabs_3726_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*8, v_mayPostpone_3711_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*8 + 1, v_errToSorry_3712_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*8 + 2, v_implicitLambda_3717_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*8 + 3, v_heedElabAsElim_3718_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*8 + 4, v_isNoncomputableSection_3719_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*8 + 5, v_isMetaSection_3720_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*8 + 6, v_ignoreTCFailures_3721_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*8 + 7, v_inPattern_3722_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_3724_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_3725_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
lean_ctor_set_uint8(v___x_3732_, sizeof(void*)*8 + 10, v___x_3730_);
return v___x_3732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg(lean_object* v_inst_3756_, lean_object* v_attrs_3757_, lean_object* v_a_3758_){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; 
v___x_3759_ = lean_unsigned_to_nat(0u);
v___x_3760_ = lean_array_get_size(v_attrs_3757_);
v___x_3761_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9));
v___x_3762_ = lean_nat_dec_lt(v___x_3759_, v___x_3760_);
if (v___x_3762_ == 0)
{
lean_dec_ref(v_attrs_3757_);
lean_dec(v_inst_3756_);
return v_a_3758_;
}
else
{
if (v___x_3762_ == 0)
{
lean_dec_ref(v_attrs_3757_);
lean_dec(v_inst_3756_);
return v_a_3758_;
}
else
{
lean_object* v___f_3763_; size_t v___x_3764_; size_t v___x_3765_; lean_object* v___x_3766_; uint8_t v___x_3767_; 
v___f_3763_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10));
v___x_3764_ = ((size_t)0ULL);
v___x_3765_ = lean_usize_of_nat(v___x_3760_);
v___x_3766_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_3761_, v___f_3763_, v_attrs_3757_, v___x_3764_, v___x_3765_);
v___x_3767_ = lean_unbox(v___x_3766_);
lean_dec(v___x_3766_);
if (v___x_3767_ == 0)
{
lean_dec(v_inst_3756_);
return v_a_3758_;
}
else
{
lean_object* v___f_3768_; lean_object* v___x_3769_; 
v___f_3768_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11));
v___x_3769_ = lean_apply_3(v_inst_3756_, lean_box(0), v___f_3768_, v_a_3758_);
return v___x_3769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs(lean_object* v_m_3770_, lean_object* v_00_u03b1_3771_, lean_object* v_inst_3772_, lean_object* v_attrs_3773_, lean_object* v_a_3774_){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; 
v___x_3775_ = lean_unsigned_to_nat(0u);
v___x_3776_ = lean_array_get_size(v_attrs_3773_);
v___x_3777_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9));
v___x_3778_ = lean_nat_dec_lt(v___x_3775_, v___x_3776_);
if (v___x_3778_ == 0)
{
lean_dec_ref(v_attrs_3773_);
lean_dec(v_inst_3772_);
return v_a_3774_;
}
else
{
if (v___x_3778_ == 0)
{
lean_dec_ref(v_attrs_3773_);
lean_dec(v_inst_3772_);
return v_a_3774_;
}
else
{
lean_object* v___f_3779_; size_t v___x_3780_; size_t v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v___f_3779_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10));
v___x_3780_ = ((size_t)0ULL);
v___x_3781_ = lean_usize_of_nat(v___x_3776_);
v___x_3782_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_3777_, v___f_3779_, v_attrs_3773_, v___x_3780_, v___x_3781_);
v___x_3783_ = lean_unbox(v___x_3782_);
lean_dec(v___x_3782_);
if (v___x_3783_ == 0)
{
lean_dec(v_inst_3772_);
return v_a_3774_;
}
else
{
lean_object* v___f_3784_; lean_object* v___x_3785_; 
v___f_3784_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11));
v___x_3785_ = lean_apply_3(v_inst_3772_, lean_box(0), v___f_3784_, v_a_3774_);
return v___x_3785_;
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
