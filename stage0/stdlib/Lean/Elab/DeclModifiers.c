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
lean_inc_ref(v___y_524_);
v___x_528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_528_, 0, v___y_524_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1, &l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
lean_inc_ref(v___y_525_);
v___x_531_ = l_Lean_Linter_logLintIf___redArg(v_inst_503_, v_inst_505_, v_inst_506_, v_inst_507_, v_inst_508_, v___y_525_, v_val_522_, v___x_530_);
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
v___y_524_ = v___x_537_;
v___y_525_ = v___x_536_;
v___y_526_ = v___x_538_;
goto v___jp_523_;
}
else
{
lean_object* v___x_539_; 
v___x_539_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__5));
v___y_524_ = v___x_537_;
v___y_525_ = v___x_536_;
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
lean_dec_ref_known(v_pre_1231_, 2);
lean_dec(v_pre_1232_);
lean_dec_ref_known(v_pre_1230_, 2);
lean_dec_ref_known(v_kind_1229_, 2);
lean_dec_ref_known(v___x_1228_, 3);
lean_del_object(v___x_1217_);
goto v___jp_1219_;
}
}
else
{
lean_dec(v_pre_1231_);
lean_dec_ref_known(v_pre_1230_, 2);
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
lean_dec(v_kind_1229_);
lean_dec_ref_known(v___x_1228_, 3);
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
uint8_t v___x_16491__boxed_2155_; lean_object* v_res_2156_; 
v___x_16491__boxed_2155_ = lean_unbox(v___x_2144_);
v_res_2156_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(v_declName_2143_, v___x_16491__boxed_2155_, v___f_2145_, v_env_2146_, v_____do__lift_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
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
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2252_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2253_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0);
v___x_2254_ = lean_unsigned_to_nat(0u);
v___x_2255_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
lean_ctor_set(v___x_2255_, 2, v___x_2254_);
lean_ctor_set(v___x_2255_, 3, v___x_2254_);
lean_ctor_set(v___x_2255_, 4, v___x_2253_);
lean_ctor_set(v___x_2255_, 5, v___x_2253_);
lean_ctor_set(v___x_2255_, 6, v___x_2253_);
lean_ctor_set(v___x_2255_, 7, v___x_2253_);
lean_ctor_set(v___x_2255_, 8, v___x_2253_);
lean_ctor_set(v___x_2255_, 9, v___x_2253_);
lean_ctor_set(v___x_2255_, 10, v___x_2253_);
lean_ctor_set(v___x_2255_, 11, v___x_2252_);
return v___x_2255_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__2(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2256_ = lean_box(1);
v___x_2257_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3);
v___x_2258_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__0);
v___x_2259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
lean_ctor_set(v___x_2259_, 1, v___x_2257_);
lean_ctor_set(v___x_2259_, 2, v___x_2256_);
return v___x_2259_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__3));
v___x_2262_ = l_Lean_stringToMessageData(v___x_2261_);
return v___x_2262_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__6(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__5));
v___x_2265_ = l_Lean_stringToMessageData(v___x_2264_);
return v___x_2265_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__8(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__7));
v___x_2268_ = l_Lean_stringToMessageData(v___x_2267_);
return v___x_2268_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__10(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__9));
v___x_2271_ = l_Lean_stringToMessageData(v___x_2270_);
return v___x_2271_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__12(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__11));
v___x_2274_ = l_Lean_stringToMessageData(v___x_2273_);
return v___x_2274_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__14(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__13));
v___x_2277_ = l_Lean_stringToMessageData(v___x_2276_);
return v___x_2277_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__16(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__15));
v___x_2280_ = l_Lean_stringToMessageData(v___x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg(lean_object* v_msg_2281_, lean_object* v_declHint_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v_env_2287_; uint8_t v___x_2288_; 
v___x_2285_ = lean_box(0);
v___x_2286_ = lean_st_ref_get(v___y_2283_);
v_env_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc_ref(v_env_2287_);
lean_dec(v___x_2286_);
v___x_2288_ = l_Lean_Name_isAnonymous(v_declHint_2282_);
if (v___x_2288_ == 0)
{
uint8_t v_isExporting_2289_; 
v_isExporting_2289_ = lean_ctor_get_uint8(v_env_2287_, sizeof(void*)*13);
if (v_isExporting_2289_ == 0)
{
lean_object* v___x_2290_; 
lean_dec_ref(v_env_2287_);
lean_dec(v_declHint_2282_);
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v_msg_2281_);
return v___x_2290_;
}
else
{
lean_object* v___x_2291_; uint8_t v___x_2292_; 
lean_inc_ref(v_env_2287_);
v___x_2291_ = l_Lean_Environment_setExporting(v_env_2287_, v___x_2288_);
lean_inc(v_declHint_2282_);
lean_inc_ref(v___x_2291_);
v___x_2292_ = l_Lean_Environment_contains(v___x_2291_, v_declHint_2282_, v_isExporting_2289_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; 
lean_dec_ref(v___x_2291_);
lean_dec_ref(v_env_2287_);
lean_dec(v_declHint_2282_);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v_msg_2281_);
return v___x_2293_;
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v_c_2299_; lean_object* v___x_2300_; 
v___x_2294_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__1);
v___x_2295_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__2);
v___x_2296_ = l_Lean_Options_empty;
lean_inc_ref(v___x_2291_);
v___x_2297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2291_);
lean_ctor_set(v___x_2297_, 1, v___x_2294_);
lean_ctor_set(v___x_2297_, 2, v___x_2295_);
lean_ctor_set(v___x_2297_, 3, v___x_2296_);
lean_inc(v_declHint_2282_);
v___x_2298_ = l_Lean_MessageData_ofConstName(v_declHint_2282_, v___x_2288_);
v_c_2299_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2299_, 0, v___x_2297_);
lean_ctor_set(v_c_2299_, 1, v___x_2298_);
v___x_2300_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_2291_, v_declHint_2282_);
lean_dec_ref(v___x_2291_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
lean_dec_ref(v_env_2287_);
lean_dec(v_declHint_2282_);
v___x_2301_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4);
v___x_2302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
lean_ctor_set(v___x_2302_, 1, v_c_2299_);
v___x_2303_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__6);
v___x_2304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2302_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = l_Lean_MessageData_note(v___x_2304_);
v___x_2306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2306_, 0, v_msg_2281_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
else
{
lean_object* v_val_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2342_; 
v_val_2308_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2310_ = v___x_2300_;
v_isShared_2311_ = v_isSharedCheck_2342_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_val_2308_);
lean_dec(v___x_2300_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2342_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2312_; lean_object* v_moduleNames_2313_; lean_object* v_mod_2314_; uint8_t v___x_2315_; 
v___x_2312_ = l_Lean_Environment_header(v_env_2287_);
lean_dec_ref(v_env_2287_);
v_moduleNames_2313_ = lean_ctor_get(v___x_2312_, 4);
lean_inc_ref(v_moduleNames_2313_);
lean_dec_ref(v___x_2312_);
v_mod_2314_ = lean_array_get(v___x_2285_, v_moduleNames_2313_, v_val_2308_);
lean_dec(v_val_2308_);
lean_dec_ref(v_moduleNames_2313_);
v___x_2315_ = l_Lean_isPrivateName(v_declHint_2282_);
lean_dec(v_declHint_2282_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2316_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__8);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
lean_ctor_set(v___x_2317_, 1, v_c_2299_);
v___x_2318_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__10);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = l_Lean_MessageData_ofName(v_mod_2314_);
v___x_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__12);
v___x_2323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2321_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = l_Lean_MessageData_note(v___x_2323_);
v___x_2325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2325_, 0, v_msg_2281_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set_tag(v___x_2310_, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2325_);
v___x_2327_ = v___x_2310_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2329_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__4);
v___x_2330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
lean_ctor_set(v___x_2330_, 1, v_c_2299_);
v___x_2331_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__14);
v___x_2332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = l_Lean_MessageData_ofName(v_mod_2314_);
v___x_2334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___closed__16);
v___x_2336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = l_Lean_MessageData_note(v___x_2336_);
v___x_2338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2338_, 0, v_msg_2281_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set_tag(v___x_2310_, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2338_);
v___x_2340_ = v___x_2310_;
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
}
}
}
}
}
else
{
lean_object* v___x_2343_; 
lean_dec_ref(v_env_2287_);
lean_dec(v_declHint_2282_);
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v_msg_2281_);
return v___x_2343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg___boxed(lean_object* v_msg_2344_, lean_object* v_declHint_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg(v_msg_2344_, v_declHint_2345_, v___y_2346_);
lean_dec(v___y_2346_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25(lean_object* v_msg_2349_, lean_object* v_declHint_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2368_; 
v___x_2358_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg(v_msg_2349_, v_declHint_2350_, v___y_2356_);
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2368_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2368_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2363_ = l_Lean_unknownIdentifierMessageTag;
v___x_2364_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
lean_ctor_set(v___x_2364_, 1, v_a_2359_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2364_);
v___x_2366_ = v___x_2361_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25___boxed(lean_object* v_msg_2369_, lean_object* v_declHint_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25(v_msg_2369_, v_declHint_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___redArg(lean_object* v_ref_2379_, lean_object* v_msg_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_toCold_2388_; lean_object* v_currRecDepth_2389_; lean_object* v_ref_2390_; uint16_t v_optionFlags_2391_; uint8_t v_suppressElabErrors_2392_; uint8_t v_checkDeprecated_2393_; uint8_t v_isRecordingDeps_2394_; lean_object* v_ref_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_toCold_2388_ = lean_ctor_get(v___y_2385_, 0);
v_currRecDepth_2389_ = lean_ctor_get(v___y_2385_, 1);
v_ref_2390_ = lean_ctor_get(v___y_2385_, 2);
v_optionFlags_2391_ = lean_ctor_get_uint16(v___y_2385_, sizeof(void*)*3);
v_suppressElabErrors_2392_ = lean_ctor_get_uint8(v___y_2385_, sizeof(void*)*3 + 2);
v_checkDeprecated_2393_ = lean_ctor_get_uint8(v___y_2385_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2394_ = lean_ctor_get_uint8(v___y_2385_, sizeof(void*)*3 + 4);
v_ref_2395_ = l_Lean_replaceRef(v_ref_2379_, v_ref_2390_);
lean_inc(v_currRecDepth_2389_);
lean_inc_ref(v_toCold_2388_);
v___x_2396_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2396_, 0, v_toCold_2388_);
lean_ctor_set(v___x_2396_, 1, v_currRecDepth_2389_);
lean_ctor_set(v___x_2396_, 2, v_ref_2395_);
lean_ctor_set_uint16(v___x_2396_, sizeof(void*)*3, v_optionFlags_2391_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*3 + 2, v_suppressElabErrors_2392_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*3 + 3, v_checkDeprecated_2393_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*3 + 4, v_isRecordingDeps_2394_);
v___x_2397_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___x_2396_, v___y_2386_);
lean_dec_ref_known(v___x_2396_, 3);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___redArg___boxed(lean_object* v_ref_2398_, lean_object* v_msg_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___redArg(v_ref_2398_, v_msg_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v_ref_2398_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___redArg(lean_object* v_ref_2408_, lean_object* v_msg_2409_, lean_object* v_declHint_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; lean_object* v_a_2419_; lean_object* v___x_2420_; 
v___x_2418_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25(v_msg_2409_, v_declHint_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref(v___x_2418_);
v___x_2420_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___redArg(v_ref_2408_, v_a_2419_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___redArg___boxed(lean_object* v_ref_2421_, lean_object* v_msg_2422_, lean_object* v_declHint_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___redArg(v_ref_2421_, v_msg_2422_, v_declHint_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v_ref_2421_);
return v_res_2431_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__1(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__0));
v___x_2434_ = l_Lean_stringToMessageData(v___x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg(lean_object* v_ref_2435_, lean_object* v_constName_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2444_; uint8_t v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2444_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___closed__1);
v___x_2445_ = 0;
lean_inc(v_constName_2436_);
v___x_2446_ = l_Lean_MessageData_ofConstName(v_constName_2436_, v___x_2445_);
v___x_2447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2444_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
v___x_2448_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2447_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___redArg(v_ref_2435_, v___x_2449_, v_constName_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg___boxed(lean_object* v_ref_2451_, lean_object* v_constName_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg(v_ref_2451_, v_constName_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v_ref_2451_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___redArg(lean_object* v_constName_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_ref_2469_; lean_object* v___x_2470_; 
v_ref_2469_ = lean_ctor_get(v___y_2466_, 2);
v___x_2470_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg(v_ref_2469_, v_constName_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___redArg___boxed(lean_object* v_constName_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___redArg(v_constName_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(lean_object* v_constName_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v___x_2488_; lean_object* v_env_2489_; uint8_t v___x_2490_; lean_object* v___x_2491_; 
v___x_2488_ = lean_st_ref_get(v___y_2486_);
v_env_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc_ref(v_env_2489_);
lean_dec(v___x_2488_);
v___x_2490_ = 0;
lean_inc(v_constName_2480_);
v___x_2491_ = l_Lean_Environment_findConstVal_x3f(v_env_2489_, v_constName_2480_, v___x_2490_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___redArg(v_constName_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2492_;
}
else
{
lean_object* v_val_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec(v_constName_2480_);
v_val_2493_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2491_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_val_2493_);
lean_dec(v___x_2491_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set_tag(v___x_2495_, 0);
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_val_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14___boxed(lean_object* v_constName_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(lean_object* v_constName_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; 
lean_inc(v_constName_2510_);
v___x_2518_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2530_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2521_ = v___x_2518_;
v_isShared_2522_ = v_isSharedCheck_2530_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2530_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v_levelParams_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
v_levelParams_2523_ = lean_ctor_get(v_a_2519_, 1);
lean_inc(v_levelParams_2523_);
lean_dec(v_a_2519_);
v___x_2524_ = lean_box(0);
v___x_2525_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(v_levelParams_2523_, v___x_2524_);
v___x_2526_ = l_Lean_mkConst(v_constName_2510_, v___x_2525_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2526_);
v___x_2528_ = v___x_2521_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec(v_constName_2510_);
v_a_2531_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2518_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2518_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
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
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_constName_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_constName_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(uint8_t v___x_2548_, lean_object* v_declName_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_ref_2557_; lean_object* v___x_2558_; 
v_ref_2557_ = lean_ctor_get(v___y_2554_, 2);
v___x_2558_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_declName_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = lean_box(0);
lean_inc(v_ref_2557_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
lean_ctor_set(v___x_2561_, 1, v_ref_2557_);
v___x_2562_ = lean_unsigned_to_nat(32u);
v___x_2563_ = lean_mk_empty_array_with_capacity(v___x_2562_);
lean_dec_ref(v___x_2563_);
v___x_2564_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4);
v___x_2565_ = lean_box(0);
v___x_2566_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2566_, 0, v___x_2561_);
lean_ctor_set(v___x_2566_, 1, v___x_2564_);
lean_ctor_set(v___x_2566_, 2, v___x_2565_);
lean_ctor_set(v___x_2566_, 3, v_a_2559_);
lean_ctor_set_uint8(v___x_2566_, sizeof(void*)*4, v___x_2548_);
lean_ctor_set_uint8(v___x_2566_, sizeof(void*)*4 + 1, v___x_2548_);
v___x_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
v___x_2568_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v___x_2567_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
return v___x_2568_;
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
v_a_2569_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2558_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2558_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v___x_2577_, lean_object* v_declName_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
uint8_t v___x_17220__boxed_2586_; lean_object* v_res_2587_; 
v___x_17220__boxed_2586_ = lean_unbox(v___x_2577_);
v_res_2587_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(v___x_17220__boxed_2586_, v_declName_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(lean_object* v___f_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v___x_2596_; lean_object* v_env_2597_; lean_object* v___x_2598_; 
v___x_2596_ = lean_st_ref_get(v___y_2594_);
v_env_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc_ref(v_env_2597_);
lean_dec(v___x_2596_);
v___x_2598_ = lean_apply_8(v___f_2588_, v_env_2597_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, lean_box(0));
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed(lean_object* v___f_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(v___f_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
return v_res_2607_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0);
v___x_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
return v___x_2609_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
return v___x_2611_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17___redArg();
return v___x_2612_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2613_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2614_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
v___x_2615_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
lean_ctor_set(v___x_2615_, 1, v___x_2613_);
lean_ctor_set(v___x_2615_, 2, v___x_2613_);
lean_ctor_set(v___x_2615_, 3, v___x_2613_);
lean_ctor_set(v___x_2615_, 4, v___x_2613_);
lean_ctor_set(v___x_2615_, 5, v___x_2613_);
lean_ctor_set(v___x_2615_, 6, v___x_2613_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(lean_object* v_env_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; lean_object* v_nextMacroScope_2621_; lean_object* v_ngen_2622_; lean_object* v_auxDeclNGen_2623_; lean_object* v_traceState_2624_; lean_object* v_recordedDeps_2625_; lean_object* v_messages_2626_; lean_object* v_infoState_2627_; lean_object* v_snapshotTasks_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2654_; 
v___x_2620_ = lean_st_ref_take(v___y_2618_);
v_nextMacroScope_2621_ = lean_ctor_get(v___x_2620_, 1);
v_ngen_2622_ = lean_ctor_get(v___x_2620_, 2);
v_auxDeclNGen_2623_ = lean_ctor_get(v___x_2620_, 3);
v_traceState_2624_ = lean_ctor_get(v___x_2620_, 4);
v_recordedDeps_2625_ = lean_ctor_get(v___x_2620_, 6);
v_messages_2626_ = lean_ctor_get(v___x_2620_, 7);
v_infoState_2627_ = lean_ctor_get(v___x_2620_, 8);
v_snapshotTasks_2628_ = lean_ctor_get(v___x_2620_, 9);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; lean_object* v_unused_2656_; 
v_unused_2655_ = lean_ctor_get(v___x_2620_, 5);
lean_dec(v_unused_2655_);
v_unused_2656_ = lean_ctor_get(v___x_2620_, 0);
lean_dec(v_unused_2656_);
v___x_2630_ = v___x_2620_;
v_isShared_2631_ = v_isSharedCheck_2654_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_snapshotTasks_2628_);
lean_inc(v_infoState_2627_);
lean_inc(v_messages_2626_);
lean_inc(v_recordedDeps_2625_);
lean_inc(v_traceState_2624_);
lean_inc(v_auxDeclNGen_2623_);
lean_inc(v_ngen_2622_);
lean_inc(v_nextMacroScope_2621_);
lean_dec(v___x_2620_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2654_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2632_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 5, v___x_2632_);
lean_ctor_set(v___x_2630_, 0, v_env_2616_);
v___x_2634_ = v___x_2630_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_env_2616_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_nextMacroScope_2621_);
lean_ctor_set(v_reuseFailAlloc_2653_, 2, v_ngen_2622_);
lean_ctor_set(v_reuseFailAlloc_2653_, 3, v_auxDeclNGen_2623_);
lean_ctor_set(v_reuseFailAlloc_2653_, 4, v_traceState_2624_);
lean_ctor_set(v_reuseFailAlloc_2653_, 5, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2653_, 6, v_recordedDeps_2625_);
lean_ctor_set(v_reuseFailAlloc_2653_, 7, v_messages_2626_);
lean_ctor_set(v_reuseFailAlloc_2653_, 8, v_infoState_2627_);
lean_ctor_set(v_reuseFailAlloc_2653_, 9, v_snapshotTasks_2628_);
v___x_2634_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v_mctx_2637_; lean_object* v_zetaDeltaFVarIds_2638_; lean_object* v_postponed_2639_; lean_object* v_diag_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2651_; 
v___x_2635_ = lean_st_ref_put(v___y_2618_, v___x_2634_);
v___x_2636_ = lean_st_ref_take(v___y_2617_);
v_mctx_2637_ = lean_ctor_get(v___x_2636_, 0);
v_zetaDeltaFVarIds_2638_ = lean_ctor_get(v___x_2636_, 2);
v_postponed_2639_ = lean_ctor_get(v___x_2636_, 3);
v_diag_2640_ = lean_ctor_get(v___x_2636_, 4);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2651_ == 0)
{
lean_object* v_unused_2652_; 
v_unused_2652_ = lean_ctor_get(v___x_2636_, 1);
lean_dec(v_unused_2652_);
v___x_2642_ = v___x_2636_;
v_isShared_2643_ = v_isSharedCheck_2651_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_diag_2640_);
lean_inc(v_postponed_2639_);
lean_inc(v_zetaDeltaFVarIds_2638_);
lean_inc(v_mctx_2637_);
lean_dec(v___x_2636_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2651_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2644_ = lean_box(0);
v___x_2645_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 1, v___x_2645_);
v___x_2647_ = v___x_2642_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_mctx_2637_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2650_, 2, v_zetaDeltaFVarIds_2638_);
lean_ctor_set(v_reuseFailAlloc_2650_, 3, v_postponed_2639_);
lean_ctor_set(v_reuseFailAlloc_2650_, 4, v_diag_2640_);
v___x_2647_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = lean_st_ref_put(v___y_2617_, v___x_2647_);
v___x_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2644_);
return v___x_2649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___boxed(lean_object* v_env_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec(v___y_2658_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(lean_object* v_env_2662_, lean_object* v_x_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; lean_object* v_env_2672_; lean_object* v_a_2674_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2671_ = lean_st_ref_get(v___y_2669_);
v_env_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc_ref(v_env_2672_);
lean_dec(v___x_2671_);
v___x_2684_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2662_, v___y_2667_, v___y_2669_);
lean_dec_ref(v___x_2684_);
lean_inc(v___y_2669_);
lean_inc_ref(v___y_2668_);
lean_inc(v___y_2667_);
lean_inc_ref(v___y_2666_);
lean_inc(v___y_2665_);
lean_inc_ref(v___y_2664_);
v___x_2685_ = lean_apply_7(v_x_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, lean_box(0));
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2685_, 1);
v___x_2687_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2672_, v___y_2667_, v___y_2669_);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; 
v_unused_2695_ = lean_ctor_get(v___x_2687_, 0);
lean_dec(v_unused_2695_);
v___x_2689_ = v___x_2687_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_dec(v___x_2687_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v_a_2686_);
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2686_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
else
{
lean_object* v_a_2696_; 
v_a_2696_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2685_, 1);
v_a_2674_ = v_a_2696_;
goto v___jp_2673_;
}
v___jp_2673_:
{
lean_object* v___x_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
v___x_2675_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2672_, v___y_2667_, v___y_2669_);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2682_ == 0)
{
lean_object* v_unused_2683_; 
v_unused_2683_ = lean_ctor_get(v___x_2675_, 0);
lean_dec(v_unused_2683_);
v___x_2677_ = v___x_2675_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_dec(v___x_2675_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
lean_ctor_set_tag(v___x_2677_, 1);
lean_ctor_set(v___x_2677_, 0, v_a_2674_);
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2674_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_env_2697_, lean_object* v_x_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2697_, v_x_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(lean_object* v_declName_2707_, lean_object* v_env_2708_, lean_object* v_addInfo_2709_, lean_object* v_____r_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_privateToUserName_x3f(v_declName_2707_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_dec_ref(v_addInfo_2709_);
lean_dec_ref(v_env_2708_);
v___x_2719_ = lean_box(0);
v___x_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
return v___x_2720_;
}
else
{
lean_object* v_val_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2738_; 
v_val_2721_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2723_ = v___x_2718_;
v_isShared_2724_ = v_isSharedCheck_2738_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_val_2721_);
lean_dec(v___x_2718_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2738_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
uint8_t v___x_2725_; uint8_t v___x_2726_; 
v___x_2725_ = 1;
lean_inc(v_val_2721_);
v___x_2726_ = l_Lean_Environment_contains(v_env_2708_, v_val_2721_, v___x_2725_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2729_; 
lean_dec(v_val_2721_);
lean_dec_ref(v_addInfo_2709_);
v___x_2727_ = lean_box(0);
if (v_isShared_2724_ == 0)
{
lean_ctor_set_tag(v___x_2723_, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2727_);
v___x_2729_ = v___x_2723_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
else
{
lean_object* v___x_2731_; 
lean_del_object(v___x_2723_);
lean_inc(v___y_2716_);
lean_inc_ref(v___y_2715_);
lean_inc(v___y_2714_);
lean_inc_ref(v___y_2713_);
lean_inc(v___y_2712_);
lean_inc_ref(v___y_2711_);
lean_inc(v_val_2721_);
v___x_2731_ = lean_apply_8(v_addInfo_2709_, v_val_2721_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, lean_box(0));
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_dec_ref_known(v___x_2731_, 1);
v___x_2732_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
v___x_2733_ = l_Lean_MessageData_ofConstName(v_val_2721_, v___x_2725_);
v___x_2734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2732_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
v___x_2735_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2734_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2736_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
return v___x_2737_;
}
else
{
lean_dec(v_val_2721_);
return v___x_2731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed(lean_object* v_declName_2739_, lean_object* v_env_2740_, lean_object* v_addInfo_2741_, lean_object* v_____r_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(v_declName_2739_, v_env_2740_, v_addInfo_2741_, v_____r_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(lean_object* v_addInfo_2751_, lean_object* v_declName_2752_, uint8_t v___x_2753_, uint8_t v___x_2754_, lean_object* v___f_2755_, lean_object* v_env_2756_, lean_object* v___f_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v___x_2765_; 
lean_inc(v___y_2763_);
lean_inc_ref(v___y_2762_);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v_declName_2752_);
v___x_2765_ = lean_apply_8(v_addInfo_2751_, v_declName_2752_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, lean_box(0));
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v___x_2766_; 
lean_dec_ref_known(v___x_2765_, 1);
lean_inc(v_declName_2752_);
v___x_2766_ = l_Lean_privateToUserName_x3f(v_declName_2752_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2767_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2768_ = l_Lean_MessageData_ofConstName(v_declName_2752_, v___x_2753_);
v___x_2769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2767_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2769_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2771_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
return v___x_2772_;
}
else
{
lean_object* v_val_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
lean_dec(v_declName_2752_);
v_val_2773_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_val_2773_);
lean_dec_ref_known(v___x_2766_, 1);
v___x_2774_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1);
v___x_2775_ = l_Lean_MessageData_ofConstName(v_val_2773_, v___x_2753_);
v___x_2776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
v___x_2777_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2776_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2778_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
return v___x_2779_;
}
}
else
{
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v_declName_2752_);
return v___x_2765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed(lean_object* v_addInfo_2780_, lean_object* v_declName_2781_, lean_object* v___x_2782_, lean_object* v___x_2783_, lean_object* v___f_2784_, lean_object* v_env_2785_, lean_object* v___f_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
uint8_t v___x_17578__boxed_2794_; uint8_t v___x_17579__boxed_2795_; lean_object* v_res_2796_; 
v___x_17578__boxed_2794_ = lean_unbox(v___x_2782_);
v___x_17579__boxed_2795_ = lean_unbox(v___x_2783_);
v_res_2796_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(v_addInfo_2780_, v_declName_2781_, v___x_17578__boxed_2794_, v___x_17579__boxed_2795_, v___f_2784_, v_env_2785_, v___f_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
lean_dec_ref(v___f_2786_);
lean_dec_ref(v_env_2785_);
lean_dec_ref(v___f_2784_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(lean_object* v_declName_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; lean_object* v_env_2809_; uint8_t v___x_2810_; lean_object* v_addInfo_2811_; lean_object* v_env_2812_; lean_object* v___f_2813_; lean_object* v___f_2814_; lean_object* v___x_2815_; lean_object* v___f_2816_; uint8_t v___x_2817_; uint8_t v___x_2818_; 
v___x_2808_ = lean_st_ref_get(v___y_2806_);
v_env_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc_ref(v_env_2809_);
lean_dec(v___x_2808_);
v___x_2810_ = 0;
v_addInfo_2811_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0));
v_env_2812_ = l_Lean_Environment_setExporting(v_env_2809_, v___x_2810_);
lean_inc_ref_n(v_env_2812_, 4);
lean_inc_n(v_declName_2800_, 4);
v___f_2813_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed), 11, 3);
lean_closure_set(v___f_2813_, 0, v_declName_2800_);
lean_closure_set(v___f_2813_, 1, v_env_2812_);
lean_closure_set(v___f_2813_, 2, v_addInfo_2811_);
v___f_2814_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2814_, 0, v_env_2812_);
lean_closure_set(v___f_2814_, 1, v_declName_2800_);
lean_closure_set(v___f_2814_, 2, v___f_2813_);
lean_closure_set(v___f_2814_, 3, v_addInfo_2811_);
v___x_2815_ = lean_box(v___x_2810_);
lean_inc_ref(v___f_2814_);
v___f_2816_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed), 12, 4);
lean_closure_set(v___f_2816_, 0, v_declName_2800_);
lean_closure_set(v___f_2816_, 1, v___x_2815_);
lean_closure_set(v___f_2816_, 2, v___f_2814_);
lean_closure_set(v___f_2816_, 3, v_env_2812_);
v___x_2817_ = 1;
v___x_2818_ = l_Lean_Environment_contains(v_env_2812_, v_declName_2800_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___f_2819_; lean_object* v___x_2820_; 
lean_dec_ref(v___f_2814_);
lean_dec(v_declName_2800_);
v___f_2819_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed), 8, 1);
lean_closure_set(v___f_2819_, 0, v___f_2816_);
v___x_2820_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2812_, v___f_2819_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
return v___x_2820_;
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___f_2823_; lean_object* v___x_2824_; 
v___x_2821_ = lean_box(v___x_2817_);
v___x_2822_ = lean_box(v___x_2810_);
lean_inc_ref(v_env_2812_);
v___f_2823_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed), 14, 7);
lean_closure_set(v___f_2823_, 0, v_addInfo_2811_);
lean_closure_set(v___f_2823_, 1, v_declName_2800_);
lean_closure_set(v___f_2823_, 2, v___x_2821_);
lean_closure_set(v___f_2823_, 3, v___x_2822_);
lean_closure_set(v___f_2823_, 4, v___f_2814_);
lean_closure_set(v___f_2823_, 5, v_env_2812_);
lean_closure_set(v___f_2823_, 6, v___f_2816_);
v___x_2824_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2812_, v___f_2823_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
return v___x_2824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___boxed(lean_object* v_declName_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(lean_object* v_modifiers_2834_, lean_object* v_declName_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v_declName_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___x_2908_; lean_object* v_env_2909_; uint8_t v_visibility_2910_; uint8_t v___x_2911_; 
v___x_2908_ = lean_st_ref_get(v___y_2841_);
v_env_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc_ref(v_env_2909_);
lean_dec(v___x_2908_);
v_visibility_2910_ = lean_ctor_get_uint8(v_modifiers_2834_, sizeof(void*)*3);
v___x_2911_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_2909_, v_visibility_2910_);
lean_dec_ref(v_env_2909_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; lean_object* v_env_2913_; lean_object* v_declName_2914_; 
v___x_2912_ = lean_st_ref_get(v___y_2841_);
v_env_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc_ref(v_env_2913_);
lean_dec(v___x_2912_);
v_declName_2914_ = l_Lean_mkPrivateName(v_env_2913_, v_declName_2835_);
lean_dec_ref(v_env_2913_);
v_declName_2844_ = v_declName_2914_;
v___y_2845_ = v___y_2836_;
v___y_2846_ = v___y_2837_;
v___y_2847_ = v___y_2838_;
v___y_2848_ = v___y_2839_;
v___y_2849_ = v___y_2840_;
v___y_2850_ = v___y_2841_;
goto v___jp_2843_;
}
else
{
v_declName_2844_ = v_declName_2835_;
v___y_2845_ = v___y_2836_;
v___y_2846_ = v___y_2837_;
v___y_2847_ = v___y_2838_;
v___y_2848_ = v___y_2839_;
v___y_2849_ = v___y_2840_;
v___y_2850_ = v___y_2841_;
goto v___jp_2843_;
}
v___jp_2843_:
{
lean_object* v___x_2851_; 
lean_inc(v_declName_2844_);
v___x_2851_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2898_; 
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; 
v_unused_2899_ = lean_ctor_get(v___x_2851_, 0);
lean_dec(v_unused_2899_);
v___x_2853_ = v___x_2851_;
v_isShared_2854_ = v_isSharedCheck_2898_;
goto v_resetjp_2852_;
}
else
{
lean_dec(v___x_2851_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2898_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
uint8_t v_isProtected_2855_; 
v_isProtected_2855_ = lean_ctor_get_uint8(v_modifiers_2834_, sizeof(void*)*3 + 1);
if (v_isProtected_2855_ == 0)
{
lean_object* v___x_2857_; 
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v_declName_2844_);
v___x_2857_ = v___x_2853_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_declName_2844_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
else
{
lean_object* v___x_2859_; lean_object* v_env_2860_; lean_object* v_nextMacroScope_2861_; lean_object* v_ngen_2862_; lean_object* v_auxDeclNGen_2863_; lean_object* v_traceState_2864_; lean_object* v_recordedDeps_2865_; lean_object* v_messages_2866_; lean_object* v_infoState_2867_; lean_object* v_snapshotTasks_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2896_; 
v___x_2859_ = lean_st_ref_take(v___y_2850_);
v_env_2860_ = lean_ctor_get(v___x_2859_, 0);
v_nextMacroScope_2861_ = lean_ctor_get(v___x_2859_, 1);
v_ngen_2862_ = lean_ctor_get(v___x_2859_, 2);
v_auxDeclNGen_2863_ = lean_ctor_get(v___x_2859_, 3);
v_traceState_2864_ = lean_ctor_get(v___x_2859_, 4);
v_recordedDeps_2865_ = lean_ctor_get(v___x_2859_, 6);
v_messages_2866_ = lean_ctor_get(v___x_2859_, 7);
v_infoState_2867_ = lean_ctor_get(v___x_2859_, 8);
v_snapshotTasks_2868_ = lean_ctor_get(v___x_2859_, 9);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2896_ == 0)
{
lean_object* v_unused_2897_; 
v_unused_2897_ = lean_ctor_get(v___x_2859_, 5);
lean_dec(v_unused_2897_);
v___x_2870_ = v___x_2859_;
v_isShared_2871_ = v_isSharedCheck_2896_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_snapshotTasks_2868_);
lean_inc(v_infoState_2867_);
lean_inc(v_messages_2866_);
lean_inc(v_recordedDeps_2865_);
lean_inc(v_traceState_2864_);
lean_inc(v_auxDeclNGen_2863_);
lean_inc(v_ngen_2862_);
lean_inc(v_nextMacroScope_2861_);
lean_inc(v_env_2860_);
lean_dec(v___x_2859_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2896_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2875_; 
lean_inc(v_declName_2844_);
v___x_2872_ = l_Lean_addProtected(v_env_2860_, v_declName_2844_);
v___x_2873_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 5, v___x_2873_);
lean_ctor_set(v___x_2870_, 0, v___x_2872_);
v___x_2875_ = v___x_2870_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_nextMacroScope_2861_);
lean_ctor_set(v_reuseFailAlloc_2895_, 2, v_ngen_2862_);
lean_ctor_set(v_reuseFailAlloc_2895_, 3, v_auxDeclNGen_2863_);
lean_ctor_set(v_reuseFailAlloc_2895_, 4, v_traceState_2864_);
lean_ctor_set(v_reuseFailAlloc_2895_, 5, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2895_, 6, v_recordedDeps_2865_);
lean_ctor_set(v_reuseFailAlloc_2895_, 7, v_messages_2866_);
lean_ctor_set(v_reuseFailAlloc_2895_, 8, v_infoState_2867_);
lean_ctor_set(v_reuseFailAlloc_2895_, 9, v_snapshotTasks_2868_);
v___x_2875_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v_mctx_2878_; lean_object* v_zetaDeltaFVarIds_2879_; lean_object* v_postponed_2880_; lean_object* v_diag_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2893_; 
v___x_2876_ = lean_st_ref_put(v___y_2850_, v___x_2875_);
v___x_2877_ = lean_st_ref_take(v___y_2848_);
v_mctx_2878_ = lean_ctor_get(v___x_2877_, 0);
v_zetaDeltaFVarIds_2879_ = lean_ctor_get(v___x_2877_, 2);
v_postponed_2880_ = lean_ctor_get(v___x_2877_, 3);
v_diag_2881_ = lean_ctor_get(v___x_2877_, 4);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2893_ == 0)
{
lean_object* v_unused_2894_; 
v_unused_2894_ = lean_ctor_get(v___x_2877_, 1);
lean_dec(v_unused_2894_);
v___x_2883_ = v___x_2877_;
v_isShared_2884_ = v_isSharedCheck_2893_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_diag_2881_);
lean_inc(v_postponed_2880_);
lean_inc(v_zetaDeltaFVarIds_2879_);
lean_inc(v_mctx_2878_);
lean_dec(v___x_2877_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2893_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2885_; lean_object* v___x_2887_; 
v___x_2885_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 1, v___x_2885_);
v___x_2887_ = v___x_2883_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_mctx_2878_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2892_, 2, v_zetaDeltaFVarIds_2879_);
lean_ctor_set(v_reuseFailAlloc_2892_, 3, v_postponed_2880_);
lean_ctor_set(v_reuseFailAlloc_2892_, 4, v_diag_2881_);
v___x_2887_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2888_ = lean_st_ref_put(v___y_2848_, v___x_2887_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v_declName_2844_);
v___x_2890_ = v___x_2853_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_declName_2844_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
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
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v_declName_2844_);
v_a_2900_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2851_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2851_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4___boxed(lean_object* v_modifiers_2915_, lean_object* v_declName_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2915_, v_declName_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec_ref(v_modifiers_2915_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(lean_object* v_pre_2925_, lean_object* v_declName_2926_, lean_object* v_as_2927_, size_t v_sz_2928_, size_t v_i_2929_, lean_object* v_b_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_a_2939_; uint8_t v___x_2943_; 
v___x_2943_ = lean_usize_dec_lt(v_i_2929_, v_sz_2928_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; 
lean_dec(v_declName_2926_);
lean_dec(v_pre_2925_);
v___x_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2944_, 0, v_b_2930_);
return v___x_2944_;
}
else
{
lean_object* v___x_2945_; lean_object* v_a_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v___x_2945_ = lean_box(0);
v_a_2946_ = lean_array_uget_borrowed(v_as_2927_, v_i_2929_);
lean_inc(v_a_2946_);
lean_inc(v_pre_2925_);
v___x_2947_ = l_Lean_Name_append(v_pre_2925_, v_a_2946_);
v___x_2948_ = lean_name_eq(v___x_2947_, v_declName_2926_);
lean_dec(v___x_2947_);
if (v___x_2948_ == 0)
{
v_a_2939_ = v___x_2945_;
goto v___jp_2938_;
}
else
{
lean_object* v___x_2949_; uint8_t v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2949_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_2950_ = 0;
lean_inc(v_declName_2926_);
v___x_2951_ = l_Lean_MessageData_ofConstName(v_declName_2926_, v___x_2950_);
v___x_2952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2949_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v___x_2953_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_2954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2952_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
lean_inc(v_pre_2925_);
v___x_2955_ = l_Lean_MessageData_ofName(v_pre_2925_);
v___x_2956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2954_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
v___x_2957_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_2958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2956_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
lean_inc(v_a_2946_);
v___x_2959_ = l_Lean_MessageData_ofName(v_a_2946_);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2958_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2960_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2962_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_dec_ref_known(v___x_2963_, 1);
v_a_2939_ = v___x_2945_;
goto v___jp_2938_;
}
else
{
lean_dec(v_declName_2926_);
lean_dec(v_pre_2925_);
return v___x_2963_;
}
}
}
v___jp_2938_:
{
size_t v___x_2940_; size_t v___x_2941_; 
v___x_2940_ = ((size_t)1ULL);
v___x_2941_ = lean_usize_add(v_i_2929_, v___x_2940_);
v_i_2929_ = v___x_2941_;
v_b_2930_ = v_a_2939_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6___boxed(lean_object* v_pre_2964_, lean_object* v_declName_2965_, lean_object* v_as_2966_, lean_object* v_sz_2967_, lean_object* v_i_2968_, lean_object* v_b_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
size_t v_sz_boxed_2977_; size_t v_i_boxed_2978_; lean_object* v_res_2979_; 
v_sz_boxed_2977_ = lean_unbox_usize(v_sz_2967_);
lean_dec(v_sz_2967_);
v_i_boxed_2978_ = lean_unbox_usize(v_i_2968_);
lean_dec(v_i_2968_);
v_res_2979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2964_, v_declName_2965_, v_as_2966_, v_sz_boxed_2977_, v_i_boxed_2978_, v_b_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec_ref(v_as_2966_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(lean_object* v_declName_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
if (lean_obj_tag(v_declName_2980_) == 1)
{
lean_object* v_pre_2988_; lean_object* v___x_2989_; lean_object* v_env_2990_; uint8_t v___x_2991_; 
v_pre_2988_ = lean_ctor_get(v_declName_2980_, 0);
lean_inc_n(v_pre_2988_, 2);
v___x_2989_ = lean_st_ref_get(v___y_2986_);
v_env_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc_ref(v_env_2990_);
lean_dec(v___x_2989_);
v___x_2991_ = l_Lean_isStructure(v_env_2990_, v_pre_2988_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
lean_dec_ref_known(v_declName_2980_, 2);
lean_dec(v_pre_2988_);
v___x_2992_ = lean_box(0);
v___x_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
return v___x_2993_;
}
else
{
lean_object* v___x_2994_; lean_object* v_env_2995_; lean_object* v_fieldNames_2996_; lean_object* v___x_2997_; size_t v_sz_2998_; size_t v___x_2999_; lean_object* v___x_3000_; 
v___x_2994_ = lean_st_ref_get(v___y_2986_);
v_env_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc_ref(v_env_2995_);
lean_dec(v___x_2994_);
lean_inc(v_pre_2988_);
v_fieldNames_2996_ = l_Lean_getStructureFieldsFlattened(v_env_2995_, v_pre_2988_, v___x_2991_);
v___x_2997_ = lean_box(0);
v_sz_2998_ = lean_array_size(v_fieldNames_2996_);
v___x_2999_ = ((size_t)0ULL);
v___x_3000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2988_, v_declName_2980_, v_fieldNames_2996_, v_sz_2998_, v___x_2999_, v___x_2997_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
lean_dec_ref(v_fieldNames_2996_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3007_ == 0)
{
lean_object* v_unused_3008_; 
v_unused_3008_ = lean_ctor_get(v___x_3000_, 0);
lean_dec(v_unused_3008_);
v___x_3002_ = v___x_3000_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_dec(v___x_3000_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v___x_2997_);
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_2997_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
else
{
return v___x_3000_;
}
}
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_dec(v_declName_2980_);
v___x_3009_ = lean_box(0);
v___x_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
return v___x_3010_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3___boxed(lean_object* v_declName_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v_declName_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(lean_object* v_currNamespace_3020_, lean_object* v_modifiers_3021_, lean_object* v_shortName_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3036_; lean_object* v_shortName_3037_; lean_object* v_currNamespace_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v_view_3098_; lean_object* v_name_3099_; lean_object* v_imported_3100_; lean_object* v_ctx_3101_; lean_object* v_scopes_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3160_; 
lean_inc(v_shortName_3022_);
v_view_3098_ = l_Lean_extractMacroScopes(v_shortName_3022_);
v_name_3099_ = lean_ctor_get(v_view_3098_, 0);
v_imported_3100_ = lean_ctor_get(v_view_3098_, 1);
v_ctx_3101_ = lean_ctor_get(v_view_3098_, 2);
v_scopes_3102_ = lean_ctor_get(v_view_3098_, 3);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_view_3098_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3104_ = v_view_3098_;
v_isShared_3105_ = v_isSharedCheck_3160_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_scopes_3102_);
lean_inc(v_ctx_3101_);
lean_inc(v_imported_3100_);
lean_inc(v_name_3099_);
lean_dec(v_view_3098_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3160_;
goto v_resetjp_3103_;
}
v___jp_3030_:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___y_3031_);
lean_ctor_set(v___x_3033_, 1, v___y_3032_);
v___x_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
return v___x_3034_;
}
v___jp_3035_:
{
lean_object* v___x_3045_; 
lean_inc(v___y_3036_);
v___x_3045_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v___y_3036_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v___x_3046_; 
lean_dec_ref_known(v___x_3045_, 1);
v___x_3046_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_3021_, v___y_3036_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3046_) == 0)
{
uint8_t v_isProtected_3047_; 
v_isProtected_3047_ = lean_ctor_get_uint8(v_modifiers_3021_, sizeof(void*)*3 + 1);
if (v_isProtected_3047_ == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3056_; 
lean_dec(v_currNamespace_3038_);
v_a_3048_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3050_ = v___x_3046_;
v_isShared_3051_ = v_isSharedCheck_3056_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3046_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3056_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3052_; lean_object* v___x_3054_; 
v___x_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3052_, 0, v_a_3048_);
lean_ctor_set(v___x_3052_, 1, v_shortName_3037_);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v___x_3052_);
v___x_3054_ = v___x_3050_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
else
{
if (lean_obj_tag(v_currNamespace_3038_) == 1)
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3069_; 
v_a_3057_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3059_ = v___x_3046_;
v_isShared_3060_ = v_isSharedCheck_3069_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3046_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3069_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v_str_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3067_; 
v_str_3061_ = lean_ctor_get(v_currNamespace_3038_, 1);
lean_inc_ref(v_str_3061_);
lean_dec_ref_known(v_currNamespace_3038_, 2);
v___x_3062_ = lean_box(0);
v___x_3063_ = l_Lean_Name_str___override(v___x_3062_, v_str_3061_);
v___x_3064_ = l_Lean_Name_append(v___x_3063_, v_shortName_3037_);
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_a_3057_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3065_);
v___x_3067_ = v___x_3059_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3065_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
else
{
lean_object* v_a_3070_; uint8_t v___x_3071_; 
lean_dec(v_currNamespace_3038_);
v_a_3070_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3070_);
lean_dec_ref_known(v___x_3046_, 1);
v___x_3071_ = l_Lean_Name_isAtomic(v_shortName_3037_);
if (v___x_3071_ == 0)
{
v___y_3031_ = v_a_3070_;
v___y_3032_ = v_shortName_3037_;
goto v___jp_3030_;
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v_a_3070_);
lean_dec(v_shortName_3037_);
v___x_3072_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_3073_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3072_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3073_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3073_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec(v_currNamespace_3038_);
lean_dec(v_shortName_3037_);
v_a_3082_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3046_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3046_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec(v_currNamespace_3038_);
lean_dec(v_shortName_3037_);
lean_dec(v___y_3036_);
v_a_3090_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3045_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3045_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
v_resetjp_3103_:
{
lean_object* v___x_3106_; uint8_t v_isRootName_3107_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; uint8_t v___x_3149_; 
v___x_3106_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_3107_ = l_Lean_Name_isPrefixOf(v___x_3106_, v_name_3099_);
v___x_3149_ = lean_name_eq(v_name_3099_, v___x_3106_);
if (v___x_3149_ == 0)
{
v___y_3136_ = v___y_3023_;
v___y_3137_ = v___y_3024_;
v___y_3138_ = v___y_3025_;
v___y_3139_ = v___y_3026_;
v___y_3140_ = v___y_3027_;
v___y_3141_ = v___y_3028_;
goto v___jp_3135_;
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_del_object(v___x_3104_);
lean_dec(v_scopes_3102_);
lean_dec(v_ctx_3101_);
lean_dec(v_imported_3100_);
lean_dec(v_name_3099_);
lean_dec(v_shortName_3022_);
lean_dec(v_currNamespace_3020_);
v___x_3150_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_3151_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3150_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
v___jp_3108_:
{
if (v_isRootName_3107_ == 0)
{
lean_dec(v_name_3099_);
v___y_3036_ = v___y_3115_;
v_shortName_3037_ = v_shortName_3022_;
v_currNamespace_3038_ = v_currNamespace_3020_;
v___y_3039_ = v___y_3110_;
v___y_3040_ = v___y_3113_;
v___y_3041_ = v___y_3112_;
v___y_3042_ = v___y_3114_;
v___y_3043_ = v___y_3111_;
v___y_3044_ = v___y_3109_;
goto v___jp_3035_;
}
else
{
lean_dec(v_shortName_3022_);
lean_dec(v_currNamespace_3020_);
if (lean_obj_tag(v_name_3099_) == 1)
{
lean_object* v_pre_3116_; lean_object* v_str_3117_; lean_object* v___x_3118_; lean_object* v_shortName_3119_; lean_object* v_currNamespace_3120_; 
v_pre_3116_ = lean_ctor_get(v_name_3099_, 0);
lean_inc(v_pre_3116_);
v_str_3117_ = lean_ctor_get(v_name_3099_, 1);
lean_inc_ref(v_str_3117_);
lean_dec_ref_known(v_name_3099_, 2);
v___x_3118_ = lean_box(0);
v_shortName_3119_ = l_Lean_Name_str___override(v___x_3118_, v_str_3117_);
v_currNamespace_3120_ = l_Lean_Name_replacePrefix(v_pre_3116_, v___x_3106_, v___x_3118_);
v___y_3036_ = v___y_3115_;
v_shortName_3037_ = v_shortName_3119_;
v_currNamespace_3038_ = v_currNamespace_3120_;
v___y_3039_ = v___y_3110_;
v___y_3040_ = v___y_3113_;
v___y_3041_ = v___y_3112_;
v___y_3042_ = v___y_3114_;
v___y_3043_ = v___y_3111_;
v___y_3044_ = v___y_3109_;
goto v___jp_3035_;
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec(v___y_3115_);
v___x_3121_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_3122_ = l_Lean_MessageData_ofName(v_name_3099_);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_3125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3123_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3125_, v___y_3110_, v___y_3113_, v___y_3112_, v___y_3114_, v___y_3111_, v___y_3109_);
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3126_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3126_);
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
}
v___jp_3135_:
{
if (v_isRootName_3107_ == 0)
{
lean_object* v___x_3142_; 
lean_del_object(v___x_3104_);
lean_dec(v_scopes_3102_);
lean_dec(v_ctx_3101_);
lean_dec(v_imported_3100_);
lean_inc(v_shortName_3022_);
lean_inc(v_currNamespace_3020_);
v___x_3142_ = l_Lean_Name_append(v_currNamespace_3020_, v_shortName_3022_);
v___y_3109_ = v___y_3141_;
v___y_3110_ = v___y_3136_;
v___y_3111_ = v___y_3140_;
v___y_3112_ = v___y_3138_;
v___y_3113_ = v___y_3137_;
v___y_3114_ = v___y_3139_;
v___y_3115_ = v___x_3142_;
goto v___jp_3108_;
}
else
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3146_; 
v___x_3143_ = lean_box(0);
lean_inc(v_name_3099_);
v___x_3144_ = l_Lean_Name_replacePrefix(v_name_3099_, v___x_3106_, v___x_3143_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 0, v___x_3144_);
v___x_3146_ = v___x_3104_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3144_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_imported_3100_);
lean_ctor_set(v_reuseFailAlloc_3148_, 2, v_ctx_3101_);
lean_ctor_set(v_reuseFailAlloc_3148_, 3, v_scopes_3102_);
v___x_3146_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
lean_object* v___x_3147_; 
v___x_3147_ = l_Lean_MacroScopesView_review(v___x_3146_);
v___y_3109_ = v___y_3141_;
v___y_3110_ = v___y_3136_;
v___y_3111_ = v___y_3140_;
v___y_3112_ = v___y_3138_;
v___y_3113_ = v___y_3137_;
v___y_3114_ = v___y_3139_;
v___y_3115_ = v___x_3147_;
goto v___jp_3108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2___boxed(lean_object* v_currNamespace_3161_, lean_object* v_modifiers_3162_, lean_object* v_shortName_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3161_, v_modifiers_3162_, v_shortName_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec_ref(v_modifiers_3162_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(uint8_t v___x_3172_, lean_object* v_as_3173_, size_t v_i_3174_, size_t v_stop_3175_, lean_object* v_b_3176_){
_start:
{
lean_object* v___y_3178_; uint8_t v___x_3182_; 
v___x_3182_ = lean_usize_dec_eq(v_i_3174_, v_stop_3175_);
if (v___x_3182_ == 0)
{
lean_object* v_fst_3183_; uint8_t v___x_3184_; 
v_fst_3183_ = lean_ctor_get(v_b_3176_, 0);
v___x_3184_ = lean_unbox(v_fst_3183_);
if (v___x_3184_ == 0)
{
lean_object* v_snd_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3194_; 
v_snd_3185_ = lean_ctor_get(v_b_3176_, 1);
v_isSharedCheck_3194_ = !lean_is_exclusive(v_b_3176_);
if (v_isSharedCheck_3194_ == 0)
{
lean_object* v_unused_3195_; 
v_unused_3195_ = lean_ctor_get(v_b_3176_, 0);
lean_dec(v_unused_3195_);
v___x_3187_ = v_b_3176_;
v_isShared_3188_ = v_isSharedCheck_3194_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_snd_3185_);
lean_dec(v_b_3176_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3194_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
uint8_t v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3189_ = 1;
v___x_3190_ = lean_box(v___x_3189_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v___x_3190_);
v___x_3192_ = v___x_3187_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3190_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_snd_3185_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
v___y_3178_ = v___x_3192_;
goto v___jp_3177_;
}
}
}
else
{
lean_object* v_snd_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3206_; 
v_snd_3196_ = lean_ctor_get(v_b_3176_, 1);
v_isSharedCheck_3206_ = !lean_is_exclusive(v_b_3176_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; 
v_unused_3207_ = lean_ctor_get(v_b_3176_, 0);
lean_dec(v_unused_3207_);
v___x_3198_ = v_b_3176_;
v_isShared_3199_ = v_isSharedCheck_3206_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_snd_3196_);
lean_dec(v_b_3176_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3206_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
v___x_3200_ = lean_array_uget_borrowed(v_as_3173_, v_i_3174_);
lean_inc(v___x_3200_);
v___x_3201_ = lean_array_push(v_snd_3196_, v___x_3200_);
v___x_3202_ = lean_box(v___x_3172_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 1, v___x_3201_);
lean_ctor_set(v___x_3198_, 0, v___x_3202_);
v___x_3204_ = v___x_3198_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v___x_3201_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
v___y_3178_ = v___x_3204_;
goto v___jp_3177_;
}
}
}
}
else
{
return v_b_3176_;
}
v___jp_3177_:
{
size_t v___x_3179_; size_t v___x_3180_; 
v___x_3179_ = ((size_t)1ULL);
v___x_3180_ = lean_usize_add(v_i_3174_, v___x_3179_);
v_i_3174_ = v___x_3180_;
v_b_3176_ = v___y_3178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4___boxed(lean_object* v___x_3208_, lean_object* v_as_3209_, lean_object* v_i_3210_, lean_object* v_stop_3211_, lean_object* v_b_3212_){
_start:
{
uint8_t v___x_18290__boxed_3213_; size_t v_i_boxed_3214_; size_t v_stop_boxed_3215_; lean_object* v_res_3216_; 
v___x_18290__boxed_3213_ = lean_unbox(v___x_3208_);
v_i_boxed_3214_ = lean_unbox_usize(v_i_3210_);
lean_dec(v_i_3210_);
v_stop_boxed_3215_ = lean_unbox_usize(v_stop_3211_);
lean_dec(v_stop_3211_);
v_res_3216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_18290__boxed_3213_, v_as_3209_, v_i_boxed_3214_, v_stop_boxed_3215_, v_b_3212_);
lean_dec_ref(v_as_3209_);
return v_res_3216_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(lean_object* v_a_3217_, lean_object* v_x_3218_){
_start:
{
if (lean_obj_tag(v_x_3218_) == 0)
{
uint8_t v___x_3219_; 
v___x_3219_ = 0;
return v___x_3219_;
}
else
{
lean_object* v_head_3220_; lean_object* v_tail_3221_; uint8_t v___x_3222_; 
v_head_3220_ = lean_ctor_get(v_x_3218_, 0);
v_tail_3221_ = lean_ctor_get(v_x_3218_, 1);
v___x_3222_ = lean_name_eq(v_a_3217_, v_head_3220_);
if (v___x_3222_ == 0)
{
v_x_3218_ = v_tail_3221_;
goto _start;
}
else
{
return v___x_3222_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_expandDeclId_spec__0___boxed(lean_object* v_a_3224_, lean_object* v_x_3225_){
_start:
{
uint8_t v_res_3226_; lean_object* v_r_3227_; 
v_res_3226_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_a_3224_, v_x_3225_);
lean_dec(v_x_3225_);
lean_dec(v_a_3224_);
v_r_3227_ = lean_box(v_res_3226_);
return v_r_3227_;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = ((lean_object*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0));
v___x_3230_ = l_Lean_stringToMessageData(v___x_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(lean_object* v_u_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3239_ = lean_obj_once(&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1, &l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1);
v___x_3240_ = l_Lean_MessageData_ofName(v_u_3231_);
v___x_3241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3239_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
v___x_3242_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3243_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___boxed(lean_object* v_u_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(lean_object* v_as_3254_, size_t v_i_3255_, size_t v_stop_3256_, lean_object* v_b_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v_a_3266_; uint8_t v___x_3270_; 
v___x_3270_ = lean_usize_dec_eq(v_i_3255_, v_stop_3256_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; lean_object* v_id_3272_; uint8_t v___x_3273_; 
v___x_3271_ = lean_array_uget_borrowed(v_as_3254_, v_i_3255_);
v_id_3272_ = l_Lean_Syntax_getId(v___x_3271_);
v___x_3273_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_id_3272_, v_b_3257_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; 
v___x_3274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3274_, 0, v_id_3272_);
lean_ctor_set(v___x_3274_, 1, v_b_3257_);
v_a_3266_ = v___x_3274_;
goto v___jp_3265_;
}
else
{
lean_object* v_toCold_3275_; lean_object* v_currRecDepth_3276_; lean_object* v_ref_3277_; uint16_t v_optionFlags_3278_; uint8_t v_suppressElabErrors_3279_; uint8_t v_checkDeprecated_3280_; uint8_t v_isRecordingDeps_3281_; lean_object* v_ref_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
lean_dec(v_b_3257_);
v_toCold_3275_ = lean_ctor_get(v___y_3262_, 0);
v_currRecDepth_3276_ = lean_ctor_get(v___y_3262_, 1);
v_ref_3277_ = lean_ctor_get(v___y_3262_, 2);
v_optionFlags_3278_ = lean_ctor_get_uint16(v___y_3262_, sizeof(void*)*3);
v_suppressElabErrors_3279_ = lean_ctor_get_uint8(v___y_3262_, sizeof(void*)*3 + 2);
v_checkDeprecated_3280_ = lean_ctor_get_uint8(v___y_3262_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3281_ = lean_ctor_get_uint8(v___y_3262_, sizeof(void*)*3 + 4);
v_ref_3282_ = l_Lean_replaceRef(v___x_3271_, v_ref_3277_);
lean_inc(v_currRecDepth_3276_);
lean_inc_ref(v_toCold_3275_);
v___x_3283_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3283_, 0, v_toCold_3275_);
lean_ctor_set(v___x_3283_, 1, v_currRecDepth_3276_);
lean_ctor_set(v___x_3283_, 2, v_ref_3282_);
lean_ctor_set_uint16(v___x_3283_, sizeof(void*)*3, v_optionFlags_3278_);
lean_ctor_set_uint8(v___x_3283_, sizeof(void*)*3 + 2, v_suppressElabErrors_3279_);
lean_ctor_set_uint8(v___x_3283_, sizeof(void*)*3 + 3, v_checkDeprecated_3280_);
lean_ctor_set_uint8(v___x_3283_, sizeof(void*)*3 + 4, v_isRecordingDeps_3281_);
v___x_3284_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_id_3272_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___x_3283_, v___y_3263_);
lean_dec_ref_known(v___x_3283_, 3);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v_a_3266_ = v_a_3285_;
goto v___jp_3265_;
}
else
{
return v___x_3284_;
}
}
}
else
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_b_3257_);
return v___x_3286_;
}
v___jp_3265_:
{
size_t v___x_3267_; size_t v___x_3268_; 
v___x_3267_ = ((size_t)1ULL);
v___x_3268_ = lean_usize_add(v_i_3255_, v___x_3267_);
v_i_3255_ = v___x_3268_;
v_b_3257_ = v_a_3266_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3___boxed(lean_object* v_as_3287_, lean_object* v_i_3288_, lean_object* v_stop_3289_, lean_object* v_b_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
size_t v_i_boxed_3298_; size_t v_stop_boxed_3299_; lean_object* v_res_3300_; 
v_i_boxed_3298_ = lean_unbox_usize(v_i_3288_);
lean_dec(v_i_3288_);
v_stop_boxed_3299_ = lean_unbox_usize(v_stop_3289_);
lean_dec(v_stop_3289_);
v_res_3300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v_as_3287_, v_i_boxed_3298_, v_stop_boxed_3299_, v_b_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec_ref(v_as_3287_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId(lean_object* v_currNamespace_3301_, lean_object* v_currLevelNames_3302_, lean_object* v_declId_3303_, lean_object* v_modifiers_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v___x_3312_; lean_object* v_fst_3313_; lean_object* v_snd_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3389_; 
v___x_3312_ = l_Lean_Elab_expandDeclIdCore(v_declId_3303_);
v_fst_3313_ = lean_ctor_get(v___x_3312_, 0);
v_snd_3314_ = lean_ctor_get(v___x_3312_, 1);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3316_ = v___x_3312_;
v_isShared_3317_ = v_isSharedCheck_3389_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_snd_3314_);
lean_inc(v_fst_3313_);
lean_dec(v___x_3312_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3389_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v_levelNames_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3357_; uint8_t v___x_3373_; 
v___x_3373_ = l_Lean_Syntax_isNone(v_snd_3314_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
v___x_3374_ = lean_unsigned_to_nat(1u);
v___x_3375_ = l_Lean_Syntax_getArg(v_snd_3314_, v___x_3374_);
lean_dec(v_snd_3314_);
v___x_3376_ = l_Lean_Syntax_getArgs(v___x_3375_);
lean_dec(v___x_3375_);
v___x_3377_ = lean_unsigned_to_nat(0u);
v___x_3378_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__0));
v___x_3379_ = lean_array_get_size(v___x_3376_);
v___x_3380_ = lean_nat_dec_lt(v___x_3377_, v___x_3379_);
if (v___x_3380_ == 0)
{
lean_dec_ref(v___x_3376_);
lean_del_object(v___x_3316_);
v___y_3357_ = v___x_3378_;
goto v___jp_3356_;
}
else
{
lean_object* v___x_3381_; lean_object* v___x_3383_; 
v___x_3381_ = lean_box(v___x_3380_);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 1, v___x_3378_);
lean_ctor_set(v___x_3316_, 0, v___x_3381_);
v___x_3383_ = v___x_3316_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v___x_3378_);
v___x_3383_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
size_t v___x_3384_; size_t v___x_3385_; lean_object* v___x_3386_; lean_object* v_snd_3387_; 
v___x_3384_ = ((size_t)0ULL);
v___x_3385_ = lean_usize_of_nat(v___x_3379_);
v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3373_, v___x_3376_, v___x_3384_, v___x_3385_, v___x_3383_);
lean_dec_ref(v___x_3376_);
v_snd_3387_ = lean_ctor_get(v___x_3386_, 1);
lean_inc(v_snd_3387_);
lean_dec_ref(v___x_3386_);
v___y_3357_ = v_snd_3387_;
goto v___jp_3356_;
}
}
}
else
{
lean_del_object(v___x_3316_);
lean_dec(v_snd_3314_);
v_levelNames_3319_ = v_currLevelNames_3302_;
v___y_3320_ = v_a_3305_;
v___y_3321_ = v_a_3306_;
v___y_3322_ = v_a_3307_;
v___y_3323_ = v_a_3308_;
v___y_3324_ = v_a_3309_;
v___y_3325_ = v_a_3310_;
goto v___jp_3318_;
}
v___jp_3318_:
{
lean_object* v_toCold_3326_; lean_object* v_currRecDepth_3327_; lean_object* v_ref_3328_; uint16_t v_optionFlags_3329_; uint8_t v_suppressElabErrors_3330_; uint8_t v_checkDeprecated_3331_; uint8_t v_isRecordingDeps_3332_; lean_object* v_ref_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_toCold_3326_ = lean_ctor_get(v___y_3324_, 0);
v_currRecDepth_3327_ = lean_ctor_get(v___y_3324_, 1);
v_ref_3328_ = lean_ctor_get(v___y_3324_, 2);
v_optionFlags_3329_ = lean_ctor_get_uint16(v___y_3324_, sizeof(void*)*3);
v_suppressElabErrors_3330_ = lean_ctor_get_uint8(v___y_3324_, sizeof(void*)*3 + 2);
v_checkDeprecated_3331_ = lean_ctor_get_uint8(v___y_3324_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3332_ = lean_ctor_get_uint8(v___y_3324_, sizeof(void*)*3 + 4);
v_ref_3333_ = l_Lean_replaceRef(v_declId_3303_, v_ref_3328_);
lean_inc(v_currRecDepth_3327_);
lean_inc_ref(v_toCold_3326_);
v___x_3334_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3334_, 0, v_toCold_3326_);
lean_ctor_set(v___x_3334_, 1, v_currRecDepth_3327_);
lean_ctor_set(v___x_3334_, 2, v_ref_3333_);
lean_ctor_set_uint16(v___x_3334_, sizeof(void*)*3, v_optionFlags_3329_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*3 + 2, v_suppressElabErrors_3330_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*3 + 3, v_checkDeprecated_3331_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*3 + 4, v_isRecordingDeps_3332_);
v___x_3335_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3301_, v_modifiers_3304_, v_fst_3313_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___x_3334_, v___y_3325_);
lean_dec_ref_known(v___x_3334_, 3);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3347_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3338_ = v___x_3335_;
v_isShared_3339_ = v_isSharedCheck_3347_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3335_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3347_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v_fst_3340_; lean_object* v_snd_3341_; lean_object* v_docString_x3f_3342_; lean_object* v___x_3343_; lean_object* v___x_3345_; 
v_fst_3340_ = lean_ctor_get(v_a_3336_, 0);
lean_inc(v_fst_3340_);
v_snd_3341_ = lean_ctor_get(v_a_3336_, 1);
lean_inc(v_snd_3341_);
lean_dec(v_a_3336_);
v_docString_x3f_3342_ = lean_ctor_get(v_modifiers_3304_, 1);
lean_inc(v_docString_x3f_3342_);
v___x_3343_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3343_, 0, v_snd_3341_);
lean_ctor_set(v___x_3343_, 1, v_fst_3340_);
lean_ctor_set(v___x_3343_, 2, v_levelNames_3319_);
lean_ctor_set(v___x_3343_, 3, v_docString_x3f_3342_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v___x_3343_);
v___x_3345_ = v___x_3338_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec(v_levelNames_3319_);
v_a_3348_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3335_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3335_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
v___jp_3356_:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3358_ = lean_unsigned_to_nat(0u);
v___x_3359_ = lean_array_get_size(v___y_3357_);
v___x_3360_ = lean_nat_dec_lt(v___x_3358_, v___x_3359_);
if (v___x_3360_ == 0)
{
lean_dec_ref(v___y_3357_);
v_levelNames_3319_ = v_currLevelNames_3302_;
v___y_3320_ = v_a_3305_;
v___y_3321_ = v_a_3306_;
v___y_3322_ = v_a_3307_;
v___y_3323_ = v_a_3308_;
v___y_3324_ = v_a_3309_;
v___y_3325_ = v_a_3310_;
goto v___jp_3318_;
}
else
{
size_t v___x_3361_; size_t v___x_3362_; lean_object* v___x_3363_; 
v___x_3361_ = ((size_t)0ULL);
v___x_3362_ = lean_usize_of_nat(v___x_3359_);
v___x_3363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3357_, v___x_3361_, v___x_3362_, v_currLevelNames_3302_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
lean_dec_ref(v___y_3357_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3363_, 1);
v_levelNames_3319_ = v_a_3364_;
v___y_3320_ = v_a_3305_;
v___y_3321_ = v_a_3306_;
v___y_3322_ = v_a_3307_;
v___y_3323_ = v_a_3308_;
v___y_3324_ = v_a_3309_;
v___y_3325_ = v_a_3310_;
goto v___jp_3318_;
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec(v_fst_3313_);
lean_dec(v_currNamespace_3301_);
v_a_3365_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3363_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3363_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___boxed(lean_object* v_currNamespace_3390_, lean_object* v_currLevelNames_3391_, lean_object* v_declId_3392_, lean_object* v_modifiers_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Lean_Elab_expandDeclId(v_currNamespace_3390_, v_currLevelNames_3391_, v_declId_3392_, v_modifiers_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
lean_dec_ref(v_modifiers_3393_);
lean_dec(v_declId_3392_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(lean_object* v_00_u03b1_3402_, lean_object* v_u_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___boxed(lean_object* v_00_u03b1_3412_, lean_object* v_u_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(v_00_u03b1_3412_, v_u_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(lean_object* v_00_u03b1_3422_, lean_object* v_msg_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v___x_3431_; 
v___x_3431_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3432_, lean_object* v_msg_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(v_00_u03b1_3432_, v_msg_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(lean_object* v_msgData_3442_, lean_object* v_macroStack_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v___x_3451_; 
v___x_3451_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_3442_, v_macroStack_3443_, v___y_3448_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_3452_, lean_object* v_macroStack_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(v_msgData_3452_, v_macroStack_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9_spec__17(lean_object* v_00_u03b2_3462_){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9___redArg(){
_start:
{
lean_object* v___x_3465_; 
v___x_3465_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v___dummy_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9___redArg();
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__9(lean_object* v_00_u03b2_3468_){
_start:
{
lean_object* v___x_3469_; 
v___x_3469_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(lean_object* v_t_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_3470_, v___y_3476_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___boxed(lean_object* v_t_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(v_t_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(lean_object* v_00_u03b1_3488_, lean_object* v_env_3489_, lean_object* v_x_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_3489_, v_x_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3499_, lean_object* v_env_3500_, lean_object* v_x_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(v_00_u03b1_3499_, v_env_3500_, v_x_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(lean_object* v_env_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_3510_, v___y_3514_, v___y_3516_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___boxed(lean_object* v_env_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(v_env_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17(lean_object* v_00_u03b1_3528_, lean_object* v_constName_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___redArg(v_constName_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3538_, lean_object* v_constName_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17(v_00_u03b1_3538_, v_constName_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21(lean_object* v_00_u03b1_3548_, lean_object* v_ref_3549_, lean_object* v_constName_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___redArg(v_ref_3549_, v_constName_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21___boxed(lean_object* v_00_u03b1_3559_, lean_object* v_ref_3560_, lean_object* v_constName_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21(v_00_u03b1_3559_, v_ref_3560_, v_constName_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v_ref_3560_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24(lean_object* v_00_u03b1_3570_, lean_object* v_ref_3571_, lean_object* v_msg_3572_, lean_object* v_declHint_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___redArg(v_ref_3571_, v_msg_3572_, v_declHint_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24___boxed(lean_object* v_00_u03b1_3582_, lean_object* v_ref_3583_, lean_object* v_msg_3584_, lean_object* v_declHint_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24(v_00_u03b1_3582_, v_ref_3583_, v_msg_3584_, v_declHint_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v_ref_3583_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26(lean_object* v_msg_3594_, lean_object* v_declHint_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___redArg(v_msg_3594_, v_declHint_3595_, v___y_3601_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26___boxed(lean_object* v_msg_3604_, lean_object* v_declHint_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__25_spec__26(v_msg_3604_, v_declHint_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26(lean_object* v_00_u03b1_3614_, lean_object* v_ref_3615_, lean_object* v_msg_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___redArg(v_ref_3615_, v_msg_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26___boxed(lean_object* v_00_u03b1_3625_, lean_object* v_ref_3626_, lean_object* v_msg_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__17_spec__21_spec__24_spec__26(v_00_u03b1_3625_, v_ref_3626_, v_msg_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
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
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(lean_object* v_x_3639_){
_start:
{
lean_object* v_name_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; 
v_name_3640_ = lean_ctor_get(v_x_3639_, 0);
v___x_3641_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__1));
v___x_3642_ = lean_name_eq(v_name_3640_, v___x_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___boxed(lean_object* v_x_3643_){
_start:
{
uint8_t v_res_3644_; lean_object* v_r_3645_; 
v_res_3644_ = l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(v_x_3643_);
lean_dec_ref(v_x_3643_);
v_r_3645_ = lean_box(v_res_3644_);
return v_r_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__1(lean_object* v_ctx_3646_){
_start:
{
lean_object* v_toCold_3647_; lean_object* v_currRecDepth_3648_; lean_object* v_ref_3649_; uint16_t v_optionFlags_3650_; uint8_t v_suppressElabErrors_3651_; uint8_t v_isRecordingDeps_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3660_; 
v_toCold_3647_ = lean_ctor_get(v_ctx_3646_, 0);
v_currRecDepth_3648_ = lean_ctor_get(v_ctx_3646_, 1);
v_ref_3649_ = lean_ctor_get(v_ctx_3646_, 2);
v_optionFlags_3650_ = lean_ctor_get_uint16(v_ctx_3646_, sizeof(void*)*3);
v_suppressElabErrors_3651_ = lean_ctor_get_uint8(v_ctx_3646_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3652_ = lean_ctor_get_uint8(v_ctx_3646_, sizeof(void*)*3 + 4);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_ctx_3646_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3654_ = v_ctx_3646_;
v_isShared_3655_ = v_isSharedCheck_3660_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_ref_3649_);
lean_inc(v_currRecDepth_3648_);
lean_inc(v_toCold_3647_);
lean_dec(v_ctx_3646_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3660_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
uint8_t v___x_3656_; lean_object* v___x_3658_; 
v___x_3656_ = 2;
if (v_isShared_3655_ == 0)
{
v___x_3658_ = v___x_3654_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_toCold_3647_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_currRecDepth_3648_);
lean_ctor_set(v_reuseFailAlloc_3659_, 2, v_ref_3649_);
lean_ctor_set_uint16(v_reuseFailAlloc_3659_, sizeof(void*)*3, v_optionFlags_3650_);
lean_ctor_set_uint8(v_reuseFailAlloc_3659_, sizeof(void*)*3 + 2, v_suppressElabErrors_3651_);
lean_ctor_set_uint8(v_reuseFailAlloc_3659_, sizeof(void*)*3 + 4, v_isRecordingDeps_3652_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_ctor_set_uint8(v___x_3658_, sizeof(void*)*3 + 3, v___x_3656_);
return v___x_3658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg(lean_object* v_inst_3682_, lean_object* v_attrs_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; 
v___x_3685_ = lean_unsigned_to_nat(0u);
v___x_3686_ = lean_array_get_size(v_attrs_3683_);
v___x_3687_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9));
v___x_3688_ = lean_nat_dec_lt(v___x_3685_, v___x_3686_);
if (v___x_3688_ == 0)
{
lean_dec_ref(v_attrs_3683_);
lean_dec(v_inst_3682_);
return v_a_3684_;
}
else
{
if (v___x_3688_ == 0)
{
lean_dec_ref(v_attrs_3683_);
lean_dec(v_inst_3682_);
return v_a_3684_;
}
else
{
lean_object* v___f_3689_; size_t v___x_3690_; size_t v___x_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; 
v___f_3689_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10));
v___x_3690_ = ((size_t)0ULL);
v___x_3691_ = lean_usize_of_nat(v___x_3686_);
v___x_3692_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_3687_, v___f_3689_, v_attrs_3683_, v___x_3690_, v___x_3691_);
v___x_3693_ = lean_unbox(v___x_3692_);
lean_dec(v___x_3692_);
if (v___x_3693_ == 0)
{
lean_dec(v_inst_3682_);
return v_a_3684_;
}
else
{
lean_object* v___f_3694_; lean_object* v___x_3695_; 
v___f_3694_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11));
v___x_3695_ = lean_apply_3(v_inst_3682_, lean_box(0), v___f_3694_, v_a_3684_);
return v___x_3695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withDeprecationContextFromAttrs(lean_object* v_m_3696_, lean_object* v_00_u03b1_3697_, lean_object* v_inst_3698_, lean_object* v_attrs_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; 
v___x_3701_ = lean_unsigned_to_nat(0u);
v___x_3702_ = lean_array_get_size(v_attrs_3699_);
v___x_3703_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9));
v___x_3704_ = lean_nat_dec_lt(v___x_3701_, v___x_3702_);
if (v___x_3704_ == 0)
{
lean_dec_ref(v_attrs_3699_);
lean_dec(v_inst_3698_);
return v_a_3700_;
}
else
{
if (v___x_3704_ == 0)
{
lean_dec_ref(v_attrs_3699_);
lean_dec(v_inst_3698_);
return v_a_3700_;
}
else
{
lean_object* v___f_3705_; size_t v___x_3706_; size_t v___x_3707_; lean_object* v___x_3708_; uint8_t v___x_3709_; 
v___f_3705_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10));
v___x_3706_ = ((size_t)0ULL);
v___x_3707_ = lean_usize_of_nat(v___x_3702_);
v___x_3708_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_3703_, v___f_3705_, v_attrs_3699_, v___x_3706_, v___x_3707_);
v___x_3709_ = lean_unbox(v___x_3708_);
lean_dec(v___x_3708_);
if (v___x_3709_ == 0)
{
lean_dec(v_inst_3698_);
return v_a_3700_;
}
else
{
lean_object* v___f_3710_; lean_object* v___x_3711_; 
v___f_3710_ = ((lean_object*)(l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11));
v___x_3711_ = lean_apply_3(v_inst_3698_, lean_box(0), v___f_3710_, v_a_3700_);
return v___x_3711_;
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
