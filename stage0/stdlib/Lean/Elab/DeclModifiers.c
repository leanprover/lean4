// Lean compiler output
// Module: Lean.Elab.DeclModifiers
// Imports: public import Lean.DocString.Add meta import Lean.Parser.Command
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_elabVisibility___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_elabVisibility___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_elabVisibility___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_instToStringVisibility___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(213, 248, 16, 228, 25, 227, 72, 143)}};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_elabVisibility___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_instToStringVisibility___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 134, 241, 204, 211, 206, 124, 144)}};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__4_value;
static const lean_string_object l_Lean_Elab_elabVisibility___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unexpected visibility modifier"};
static const lean_object* l_Lean_Elab_elabVisibility___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Elab_elabVisibility___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabVisibility___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__0___closed__6_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "local "};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_instToFormatModifiers___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "scoped "};
static const lean_object* l_Lean_Elab_instToFormatModifiers___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__0___closed__8_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2___boxed(lean_object**);
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l_Lean_Elab_elabModifiers___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_elabVisibility___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(32u);
v___x_5_ = lean_mk_empty_array_with_capacity(v___x_4_);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3(void){
_start:
{
size_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_7_ = ((size_t)5ULL);
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = lean_unsigned_to_nat(32u);
v___x_10_ = lean_mk_empty_array_with_capacity(v___x_9_);
v___x_11_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2);
v___x_12_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
lean_ctor_set(v___x_12_, 2, v___x_8_);
lean_ctor_set(v___x_12_, 3, v___x_8_);
lean_ctor_set_usize(v___x_12_, 4, v___x_7_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_13_ = lean_box(1);
v___x_14_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3);
v___x_15_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1);
v___x_16_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
lean_ctor_set(v___x_16_, 2, v___x_13_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(lean_object* v_____do__lift_17_, uint8_t v___x_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_____do__lift_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_22_ = lean_box(0);
v___x_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
lean_ctor_set(v___x_23_, 1, v_____do__lift_17_);
v___x_24_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4);
v___x_25_ = lean_box(0);
v___x_26_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_26_, 0, v___x_23_);
lean_ctor_set(v___x_26_, 1, v___x_24_);
lean_ctor_set(v___x_26_, 2, v___x_25_);
lean_ctor_set(v___x_26_, 3, v_____do__lift_21_);
lean_ctor_set_uint8(v___x_26_, sizeof(void*)*4, v___x_18_);
lean_ctor_set_uint8(v___x_26_, sizeof(void*)*4 + 1, v___x_18_);
v___x_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
v___x_28_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_19_, v_inst_20_, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___boxed(lean_object* v_____do__lift_29_, lean_object* v___x_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_____do__lift_33_){
_start:
{
uint8_t v___x_876__boxed_34_; lean_object* v_res_35_; 
v___x_876__boxed_34_ = lean_unbox(v___x_30_);
v_res_35_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(v_____do__lift_29_, v___x_876__boxed_34_, v_inst_31_, v_inst_32_, v_____do__lift_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(uint8_t v___x_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_declName_41_, lean_object* v_toBind_42_, lean_object* v_____do__lift_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___f_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_44_ = lean_box(v___x_36_);
lean_inc_ref(v_inst_37_);
v___f_45_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_45_, 0, v_____do__lift_43_);
lean_closure_set(v___f_45_, 1, v___x_44_);
lean_closure_set(v___f_45_, 2, v_inst_37_);
lean_closure_set(v___f_45_, 3, v_inst_38_);
v___x_46_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_37_, v_inst_39_, v_inst_40_, v_declName_41_);
v___x_47_ = lean_apply_4(v_toBind_42_, lean_box(0), lean_box(0), v___x_46_, v___f_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1___boxed(lean_object* v___x_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_declName_53_, lean_object* v_toBind_54_, lean_object* v_____do__lift_55_){
_start:
{
uint8_t v___x_920__boxed_56_; lean_object* v_res_57_; 
v___x_920__boxed_56_ = lean_unbox(v___x_48_);
v_res_57_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(v___x_920__boxed_56_, v_inst_49_, v_inst_50_, v_inst_51_, v_inst_52_, v_declName_53_, v_toBind_54_, v_____do__lift_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(lean_object* v_toMonadRef_58_, uint8_t v___x_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_toBind_64_, lean_object* v_declName_65_){
_start:
{
lean_object* v_getRef_66_; lean_object* v___x_67_; lean_object* v___f_68_; lean_object* v___x_69_; 
v_getRef_66_ = lean_ctor_get(v_toMonadRef_58_, 0);
lean_inc(v_getRef_66_);
lean_dec_ref(v_toMonadRef_58_);
v___x_67_ = lean_box(v___x_59_);
lean_inc(v_toBind_64_);
v___f_68_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_68_, 0, v___x_67_);
lean_closure_set(v___f_68_, 1, v_inst_60_);
lean_closure_set(v___f_68_, 2, v_inst_61_);
lean_closure_set(v___f_68_, 3, v_inst_62_);
lean_closure_set(v___f_68_, 4, v_inst_63_);
lean_closure_set(v___f_68_, 5, v_declName_65_);
lean_closure_set(v___f_68_, 6, v_toBind_64_);
v___x_69_ = lean_apply_4(v_toBind_64_, lean_box(0), lean_box(0), v_getRef_66_, v___f_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2___boxed(lean_object* v_toMonadRef_70_, lean_object* v___x_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_toBind_76_, lean_object* v_declName_77_){
_start:
{
uint8_t v___x_946__boxed_78_; lean_object* v_res_79_; 
v___x_946__boxed_78_ = lean_unbox(v___x_71_);
v_res_79_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(v_toMonadRef_70_, v___x_946__boxed_78_, v_inst_72_, v_inst_73_, v_inst_74_, v_inst_75_, v_toBind_76_, v_declName_77_);
return v_res_79_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0));
v___x_82_ = l_Lean_stringToMessageData(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2));
v___x_85_ = l_Lean_stringToMessageData(v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(lean_object* v_val_86_, uint8_t v___x_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_____r_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_91_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
v___x_92_ = l_Lean_MessageData_ofConstName(v_val_86_, v___x_87_);
v___x_93_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_95_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = l_Lean_throwError___redArg(v_inst_88_, v_inst_89_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___boxed(lean_object* v_val_97_, lean_object* v___x_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_____r_101_){
_start:
{
uint8_t v___x_980__boxed_102_; lean_object* v_res_103_; 
v___x_980__boxed_102_ = lean_unbox(v___x_98_);
v_res_103_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(v_val_97_, v___x_980__boxed_102_, v_inst_99_, v_inst_100_, v_____r_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__4(lean_object* v_declName_104_, lean_object* v_toPure_105_, lean_object* v_env_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_addInfo_109_, lean_object* v_toBind_110_, lean_object* v_____r_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_private_to_user_name(v_declName_104_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v_toBind_110_);
lean_dec(v_addInfo_109_);
lean_dec_ref(v_inst_108_);
lean_dec_ref(v_inst_107_);
lean_dec_ref(v_env_106_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_apply_2(v_toPure_105_, lean_box(0), v___x_113_);
return v___x_114_;
}
else
{
lean_object* v_val_115_; uint8_t v___x_116_; uint8_t v___x_117_; 
v_val_115_ = lean_ctor_get(v___x_112_, 0);
lean_inc_n(v_val_115_, 2);
lean_dec_ref(v___x_112_);
v___x_116_ = 1;
v___x_117_ = l_Lean_Environment_contains(v_env_106_, v_val_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec(v_val_115_);
lean_dec(v_toBind_110_);
lean_dec(v_addInfo_109_);
lean_dec_ref(v_inst_108_);
lean_dec_ref(v_inst_107_);
v___x_118_ = lean_box(0);
v___x_119_ = lean_apply_2(v_toPure_105_, lean_box(0), v___x_118_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_toPure_105_);
v___x_120_ = lean_box(v___x_116_);
lean_inc(v_val_115_);
v___f_121_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_121_, 0, v_val_115_);
lean_closure_set(v___f_121_, 1, v___x_120_);
lean_closure_set(v___f_121_, 2, v_inst_107_);
lean_closure_set(v___f_121_, 3, v_inst_108_);
v___x_122_ = lean_apply_1(v_addInfo_109_, v_val_115_);
v___x_123_ = lean_apply_4(v_toBind_110_, lean_box(0), lean_box(0), v___x_122_, v___f_121_);
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5(lean_object* v___f_124_, lean_object* v_____r_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_apply_1(v___f_124_, v_____r_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__0));
v___x_129_ = l_Lean_stringToMessageData(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(lean_object* v_declName_130_, uint8_t v___x_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_toBind_134_, lean_object* v___f_135_, lean_object* v_____r_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_137_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1);
v___x_138_ = l_Lean_MessageData_ofConstName(v_declName_130_, v___x_131_);
v___x_139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_137_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
v___x_140_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_139_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = l_Lean_throwError___redArg(v_inst_132_, v_inst_133_, v___x_141_);
v___x_143_ = lean_apply_4(v_toBind_134_, lean_box(0), lean_box(0), v___x_142_, v___f_135_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___boxed(lean_object* v_declName_144_, lean_object* v___x_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_toBind_148_, lean_object* v___f_149_, lean_object* v_____r_150_){
_start:
{
uint8_t v___x_1057__boxed_151_; lean_object* v_res_152_; 
v___x_1057__boxed_151_ = lean_unbox(v___x_145_);
v_res_152_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(v_declName_144_, v___x_1057__boxed_151_, v_inst_146_, v_inst_147_, v_toBind_148_, v___f_149_, v_____r_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7(lean_object* v_env_153_, lean_object* v_declName_154_, lean_object* v___f_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_toBind_158_, lean_object* v___f_159_, lean_object* v_addInfo_160_, lean_object* v_____r_161_){
_start:
{
lean_object* v___x_162_; uint8_t v___x_163_; uint8_t v___x_164_; 
lean_inc(v_declName_154_);
v___x_162_ = l_Lean_mkPrivateName(v_env_153_, v_declName_154_);
v___x_163_ = 1;
lean_inc(v___x_162_);
v___x_164_ = l_Lean_Environment_contains(v_env_153_, v___x_162_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v___x_162_);
lean_dec(v_addInfo_160_);
lean_dec(v___f_159_);
lean_dec(v_toBind_158_);
lean_dec_ref(v_inst_157_);
lean_dec_ref(v_inst_156_);
lean_dec(v_declName_154_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_apply_1(v___f_155_, v___x_165_);
return v___x_166_;
}
else
{
lean_object* v___x_167_; lean_object* v___f_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec(v___f_155_);
v___x_167_ = lean_box(v___x_163_);
lean_inc(v_toBind_158_);
v___f_168_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___boxed), 7, 6);
lean_closure_set(v___f_168_, 0, v_declName_154_);
lean_closure_set(v___f_168_, 1, v___x_167_);
lean_closure_set(v___f_168_, 2, v_inst_156_);
lean_closure_set(v___f_168_, 3, v_inst_157_);
lean_closure_set(v___f_168_, 4, v_toBind_158_);
lean_closure_set(v___f_168_, 5, v___f_159_);
v___x_169_ = lean_apply_1(v_addInfo_160_, v___x_162_);
v___x_170_ = lean_apply_4(v_toBind_158_, lean_box(0), lean_box(0), v___x_169_, v___f_168_);
return v___x_170_;
}
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__0));
v___x_173_ = l_Lean_stringToMessageData(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__2));
v___x_176_ = l_Lean_stringToMessageData(v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(lean_object* v___f_177_, lean_object* v_declName_178_, uint8_t v___x_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_toBind_182_, lean_object* v___f_183_, lean_object* v_env_184_, lean_object* v_____do__lift_185_){
_start:
{
uint8_t v___y_187_; lean_object* v___x_197_; uint8_t v___x_198_; 
lean_inc(v_declName_178_);
v___x_197_ = l_Lean_privateToUserName(v_declName_178_);
lean_inc_ref(v_env_184_);
v___x_198_ = lean_is_reserved_name(v_env_184_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; uint8_t v___x_200_; 
lean_inc(v_declName_178_);
v___x_199_ = l_Lean_mkPrivateName(v_____do__lift_185_, v_declName_178_);
v___x_200_ = lean_is_reserved_name(v_env_184_, v___x_199_);
v___y_187_ = v___x_200_;
goto v___jp_186_;
}
else
{
lean_dec_ref(v_env_184_);
v___y_187_ = v___x_198_;
goto v___jp_186_;
}
v___jp_186_:
{
if (v___y_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v___f_183_);
lean_dec(v_toBind_182_);
lean_dec_ref(v_inst_181_);
lean_dec_ref(v_inst_180_);
lean_dec(v_declName_178_);
v___x_188_ = lean_box(0);
v___x_189_ = lean_apply_1(v___f_177_, v___x_188_);
return v___x_189_;
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v___f_177_);
v___x_190_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_191_ = l_Lean_MessageData_ofConstName(v_declName_178_, v___x_179_);
v___x_192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3);
v___x_194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_192_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = l_Lean_throwError___redArg(v_inst_180_, v_inst_181_, v___x_194_);
v___x_196_ = lean_apply_4(v_toBind_182_, lean_box(0), lean_box(0), v___x_195_, v___f_183_);
return v___x_196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___boxed(lean_object* v___f_201_, lean_object* v_declName_202_, lean_object* v___x_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_toBind_206_, lean_object* v___f_207_, lean_object* v_env_208_, lean_object* v_____do__lift_209_){
_start:
{
uint8_t v___x_1130__boxed_210_; lean_object* v_res_211_; 
v___x_1130__boxed_210_ = lean_unbox(v___x_203_);
v_res_211_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(v___f_201_, v_declName_202_, v___x_1130__boxed_210_, v_inst_204_, v_inst_205_, v_toBind_206_, v___f_207_, v_env_208_, v_____do__lift_209_);
lean_dec_ref(v_____do__lift_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8(lean_object* v_toBind_212_, lean_object* v_getEnv_213_, lean_object* v___f_214_, lean_object* v_____r_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_apply_4(v_toBind_212_, lean_box(0), lean_box(0), v_getEnv_213_, v___f_214_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__0));
v___x_219_ = l_Lean_stringToMessageData(v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(lean_object* v_declName_220_, uint8_t v___x_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_toBind_224_, lean_object* v___f_225_, lean_object* v___f_226_, lean_object* v_____r_227_){
_start:
{
lean_object* v___x_228_; 
lean_inc(v_declName_220_);
v___x_228_ = lean_private_to_user_name(v_declName_220_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec(v___f_226_);
v___x_229_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_230_ = l_Lean_MessageData_ofConstName(v_declName_220_, v___x_221_);
v___x_231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = l_Lean_throwError___redArg(v_inst_222_, v_inst_223_, v___x_233_);
v___x_235_ = lean_apply_4(v_toBind_224_, lean_box(0), lean_box(0), v___x_234_, v___f_225_);
return v___x_235_;
}
else
{
lean_object* v_val_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v___f_225_);
lean_dec(v_declName_220_);
v_val_236_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_236_);
lean_dec_ref(v___x_228_);
v___x_237_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1);
v___x_238_ = l_Lean_MessageData_ofConstName(v_val_236_, v___x_221_);
v___x_239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_239_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = l_Lean_throwError___redArg(v_inst_222_, v_inst_223_, v___x_241_);
v___x_243_ = lean_apply_4(v_toBind_224_, lean_box(0), lean_box(0), v___x_242_, v___f_226_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___boxed(lean_object* v_declName_244_, lean_object* v___x_245_, lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_toBind_248_, lean_object* v___f_249_, lean_object* v___f_250_, lean_object* v_____r_251_){
_start:
{
uint8_t v___x_1204__boxed_252_; lean_object* v_res_253_; 
v___x_1204__boxed_252_ = lean_unbox(v___x_245_);
v_res_253_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(v_declName_244_, v___x_1204__boxed_252_, v_inst_246_, v_inst_247_, v_toBind_248_, v___f_249_, v___f_250_, v_____r_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10(lean_object* v_toMonadRef_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_toBind_259_, lean_object* v_declName_260_, lean_object* v_toPure_261_, lean_object* v_getEnv_262_, lean_object* v_inst_263_, lean_object* v_env_264_){
_start:
{
uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v_addInfo_267_; lean_object* v_env_268_; lean_object* v___f_269_; lean_object* v___f_270_; lean_object* v___f_271_; lean_object* v___f_272_; lean_object* v___x_273_; lean_object* v___f_274_; uint8_t v___x_275_; uint8_t v___x_276_; 
v___x_265_ = 0;
v___x_266_ = lean_box(v___x_265_);
lean_inc_n(v_toBind_259_, 4);
lean_inc_ref_n(v_inst_258_, 4);
lean_inc_ref(v_inst_257_);
lean_inc_ref(v_inst_256_);
lean_inc_ref_n(v_inst_255_, 4);
lean_inc_ref(v_toMonadRef_254_);
v_addInfo_267_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v_addInfo_267_, 0, v_toMonadRef_254_);
lean_closure_set(v_addInfo_267_, 1, v___x_266_);
lean_closure_set(v_addInfo_267_, 2, v_inst_255_);
lean_closure_set(v_addInfo_267_, 3, v_inst_256_);
lean_closure_set(v_addInfo_267_, 4, v_inst_257_);
lean_closure_set(v_addInfo_267_, 5, v_inst_258_);
lean_closure_set(v_addInfo_267_, 6, v_toBind_259_);
v_env_268_ = l_Lean_Environment_setExporting(v_env_264_, v___x_265_);
lean_inc_ref(v_addInfo_267_);
lean_inc_ref_n(v_env_268_, 4);
lean_inc_n(v_declName_260_, 4);
v___f_269_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__4), 8, 7);
lean_closure_set(v___f_269_, 0, v_declName_260_);
lean_closure_set(v___f_269_, 1, v_toPure_261_);
lean_closure_set(v___f_269_, 2, v_env_268_);
lean_closure_set(v___f_269_, 3, v_inst_255_);
lean_closure_set(v___f_269_, 4, v_inst_258_);
lean_closure_set(v___f_269_, 5, v_addInfo_267_);
lean_closure_set(v___f_269_, 6, v_toBind_259_);
lean_inc_ref(v___f_269_);
v___f_270_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_270_, 0, v___f_269_);
v___f_271_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7), 9, 8);
lean_closure_set(v___f_271_, 0, v_env_268_);
lean_closure_set(v___f_271_, 1, v_declName_260_);
lean_closure_set(v___f_271_, 2, v___f_269_);
lean_closure_set(v___f_271_, 3, v_inst_255_);
lean_closure_set(v___f_271_, 4, v_inst_258_);
lean_closure_set(v___f_271_, 5, v_toBind_259_);
lean_closure_set(v___f_271_, 6, v___f_270_);
lean_closure_set(v___f_271_, 7, v_addInfo_267_);
lean_inc_ref(v___f_271_);
v___f_272_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_272_, 0, v___f_271_);
v___x_273_ = lean_box(v___x_265_);
v___f_274_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___boxed), 9, 8);
lean_closure_set(v___f_274_, 0, v___f_271_);
lean_closure_set(v___f_274_, 1, v_declName_260_);
lean_closure_set(v___f_274_, 2, v___x_273_);
lean_closure_set(v___f_274_, 3, v_inst_255_);
lean_closure_set(v___f_274_, 4, v_inst_258_);
lean_closure_set(v___f_274_, 5, v_toBind_259_);
lean_closure_set(v___f_274_, 6, v___f_272_);
lean_closure_set(v___f_274_, 7, v_env_268_);
v___x_275_ = 1;
v___x_276_ = l_Lean_Environment_contains(v_env_268_, v_declName_260_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec(v_declName_260_);
lean_dec_ref(v_inst_258_);
lean_dec_ref(v_inst_256_);
lean_dec_ref(v_toMonadRef_254_);
v___x_277_ = lean_apply_4(v_toBind_259_, lean_box(0), lean_box(0), v_getEnv_262_, v___f_274_);
v___x_278_ = l_Lean_withEnv___redArg(v_inst_255_, v_inst_263_, v_inst_257_, v_env_268_, v___x_277_);
return v___x_278_;
}
else
{
lean_object* v___f_279_; lean_object* v___x_280_; lean_object* v___f_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_inc_n(v_toBind_259_, 3);
v___f_279_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8), 4, 3);
lean_closure_set(v___f_279_, 0, v_toBind_259_);
lean_closure_set(v___f_279_, 1, v_getEnv_262_);
lean_closure_set(v___f_279_, 2, v___f_274_);
v___x_280_ = lean_box(v___x_275_);
lean_inc_ref(v___f_279_);
lean_inc_ref(v_inst_258_);
lean_inc_ref_n(v_inst_255_, 2);
lean_inc(v_declName_260_);
v___f_281_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_281_, 0, v_declName_260_);
lean_closure_set(v___f_281_, 1, v___x_280_);
lean_closure_set(v___f_281_, 2, v_inst_255_);
lean_closure_set(v___f_281_, 3, v_inst_258_);
lean_closure_set(v___f_281_, 4, v_toBind_259_);
lean_closure_set(v___f_281_, 5, v___f_279_);
lean_closure_set(v___f_281_, 6, v___f_279_);
lean_inc_ref(v_inst_257_);
v___x_282_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(v_toMonadRef_254_, v___x_265_, v_inst_255_, v_inst_256_, v_inst_257_, v_inst_258_, v_toBind_259_, v_declName_260_);
v___x_283_ = lean_apply_4(v_toBind_259_, lean_box(0), lean_box(0), v___x_282_, v___f_281_);
v___x_284_ = l_Lean_withEnv___redArg(v_inst_255_, v_inst_263_, v_inst_257_, v_env_268_, v___x_283_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg(lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_declName_290_){
_start:
{
lean_object* v_toApplicative_291_; lean_object* v_toBind_292_; lean_object* v_getEnv_293_; lean_object* v_toMonadRef_294_; lean_object* v_toPure_295_; lean_object* v___f_296_; lean_object* v___x_297_; 
v_toApplicative_291_ = lean_ctor_get(v_inst_285_, 0);
v_toBind_292_ = lean_ctor_get(v_inst_285_, 1);
lean_inc_n(v_toBind_292_, 2);
v_getEnv_293_ = lean_ctor_get(v_inst_286_, 0);
lean_inc_n(v_getEnv_293_, 2);
v_toMonadRef_294_ = lean_ctor_get(v_inst_287_, 1);
lean_inc_ref(v_toMonadRef_294_);
v_toPure_295_ = lean_ctor_get(v_toApplicative_291_, 1);
lean_inc(v_toPure_295_);
v___f_296_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10), 11, 10);
lean_closure_set(v___f_296_, 0, v_toMonadRef_294_);
lean_closure_set(v___f_296_, 1, v_inst_285_);
lean_closure_set(v___f_296_, 2, v_inst_289_);
lean_closure_set(v___f_296_, 3, v_inst_286_);
lean_closure_set(v___f_296_, 4, v_inst_287_);
lean_closure_set(v___f_296_, 5, v_toBind_292_);
lean_closure_set(v___f_296_, 6, v_declName_290_);
lean_closure_set(v___f_296_, 7, v_toPure_295_);
lean_closure_set(v___f_296_, 8, v_getEnv_293_);
lean_closure_set(v___f_296_, 9, v_inst_288_);
v___x_297_ = lean_apply_4(v_toBind_292_, lean_box(0), lean_box(0), v_getEnv_293_, v___f_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared(lean_object* v_m_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_declName_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(v_inst_299_, v_inst_300_, v_inst_301_, v_inst_302_, v_inst_303_, v_declName_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx(uint8_t v_x_306_){
_start:
{
switch(v_x_306_)
{
case 0:
{
lean_object* v___x_307_; 
v___x_307_ = lean_unsigned_to_nat(0u);
return v___x_307_;
}
case 1:
{
lean_object* v___x_308_; 
v___x_308_ = lean_unsigned_to_nat(1u);
return v___x_308_;
}
default: 
{
lean_object* v___x_309_; 
v___x_309_ = lean_unsigned_to_nat(2u);
return v___x_309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorIdx___boxed(lean_object* v_x_310_){
_start:
{
uint8_t v_x_boxed_311_; lean_object* v_res_312_; 
v_x_boxed_311_ = lean_unbox(v_x_310_);
v_res_312_ = l_Lean_Elab_Visibility_ctorIdx(v_x_boxed_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_toCtorIdx(uint8_t v_x_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Elab_Visibility_ctorIdx(v_x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_toCtorIdx___boxed(lean_object* v_x_315_){
_start:
{
uint8_t v_x_4__boxed_316_; lean_object* v_res_317_; 
v_x_4__boxed_316_ = lean_unbox(v_x_315_);
v_res_317_ = l_Lean_Elab_Visibility_toCtorIdx(v_x_4__boxed_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___redArg(lean_object* v_k_318_){
_start:
{
lean_inc(v_k_318_);
return v_k_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___redArg___boxed(lean_object* v_k_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Elab_Visibility_ctorElim___redArg(v_k_319_);
lean_dec(v_k_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim(lean_object* v_motive_321_, lean_object* v_ctorIdx_322_, uint8_t v_t_323_, lean_object* v_h_324_, lean_object* v_k_325_){
_start:
{
lean_inc(v_k_325_);
return v_k_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_ctorElim___boxed(lean_object* v_motive_326_, lean_object* v_ctorIdx_327_, lean_object* v_t_328_, lean_object* v_h_329_, lean_object* v_k_330_){
_start:
{
uint8_t v_t_boxed_331_; lean_object* v_res_332_; 
v_t_boxed_331_ = lean_unbox(v_t_328_);
v_res_332_ = l_Lean_Elab_Visibility_ctorElim(v_motive_326_, v_ctorIdx_327_, v_t_boxed_331_, v_h_329_, v_k_330_);
lean_dec(v_k_330_);
lean_dec(v_ctorIdx_327_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___redArg(lean_object* v_regular_333_){
_start:
{
lean_inc(v_regular_333_);
return v_regular_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___redArg___boxed(lean_object* v_regular_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Elab_Visibility_regular_elim___redArg(v_regular_334_);
lean_dec(v_regular_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim(lean_object* v_motive_336_, uint8_t v_t_337_, lean_object* v_h_338_, lean_object* v_regular_339_){
_start:
{
lean_inc(v_regular_339_);
return v_regular_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_regular_elim___boxed(lean_object* v_motive_340_, lean_object* v_t_341_, lean_object* v_h_342_, lean_object* v_regular_343_){
_start:
{
uint8_t v_t_boxed_344_; lean_object* v_res_345_; 
v_t_boxed_344_ = lean_unbox(v_t_341_);
v_res_345_ = l_Lean_Elab_Visibility_regular_elim(v_motive_340_, v_t_boxed_344_, v_h_342_, v_regular_343_);
lean_dec(v_regular_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___redArg(lean_object* v_private_346_){
_start:
{
lean_inc(v_private_346_);
return v_private_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___redArg___boxed(lean_object* v_private_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Elab_Visibility_private_elim___redArg(v_private_347_);
lean_dec(v_private_347_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim(lean_object* v_motive_349_, uint8_t v_t_350_, lean_object* v_h_351_, lean_object* v_private_352_){
_start:
{
lean_inc(v_private_352_);
return v_private_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_private_elim___boxed(lean_object* v_motive_353_, lean_object* v_t_354_, lean_object* v_h_355_, lean_object* v_private_356_){
_start:
{
uint8_t v_t_boxed_357_; lean_object* v_res_358_; 
v_t_boxed_357_ = lean_unbox(v_t_354_);
v_res_358_ = l_Lean_Elab_Visibility_private_elim(v_motive_353_, v_t_boxed_357_, v_h_355_, v_private_356_);
lean_dec(v_private_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___redArg(lean_object* v_public_359_){
_start:
{
lean_inc(v_public_359_);
return v_public_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___redArg___boxed(lean_object* v_public_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Elab_Visibility_public_elim___redArg(v_public_360_);
lean_dec(v_public_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim(lean_object* v_motive_362_, uint8_t v_t_363_, lean_object* v_h_364_, lean_object* v_public_365_){
_start:
{
lean_inc(v_public_365_);
return v_public_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_public_elim___boxed(lean_object* v_motive_366_, lean_object* v_t_367_, lean_object* v_h_368_, lean_object* v_public_369_){
_start:
{
uint8_t v_t_boxed_370_; lean_object* v_res_371_; 
v_t_boxed_370_ = lean_unbox(v_t_367_);
v_res_371_ = l_Lean_Elab_Visibility_public_elim(v_motive_366_, v_t_boxed_370_, v_h_368_, v_public_369_);
lean_dec(v_public_369_);
return v_res_371_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedVisibility_default(void){
_start:
{
uint8_t v___x_372_; 
v___x_372_ = 0;
return v___x_372_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedVisibility(void){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = 0;
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0(uint8_t v_x_377_){
_start:
{
switch(v_x_377_)
{
case 0:
{
lean_object* v___x_378_; 
v___x_378_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__0));
return v___x_378_;
}
case 1:
{
lean_object* v___x_379_; 
v___x_379_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__1));
return v___x_379_;
}
default: 
{
lean_object* v___x_380_; 
v___x_380_ = ((lean_object*)(l_Lean_Elab_instToStringVisibility___lam__0___closed__2));
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringVisibility___lam__0___boxed(lean_object* v_x_381_){
_start:
{
uint8_t v_x_36__boxed_382_; lean_object* v_res_383_; 
v_x_36__boxed_382_ = lean_unbox(v_x_381_);
v_res_383_ = l_Lean_Elab_instToStringVisibility___lam__0(v_x_36__boxed_382_);
return v_res_383_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPrivate(uint8_t v_x_386_){
_start:
{
if (v_x_386_ == 1)
{
uint8_t v___x_387_; 
v___x_387_ = 1;
return v___x_387_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = 0;
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPrivate___boxed(lean_object* v_x_389_){
_start:
{
uint8_t v_x_21__boxed_390_; uint8_t v_res_391_; lean_object* v_r_392_; 
v_x_21__boxed_390_ = lean_unbox(v_x_389_);
v_res_391_ = l_Lean_Elab_Visibility_isPrivate(v_x_21__boxed_390_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isPublic(uint8_t v_x_393_){
_start:
{
if (v_x_393_ == 2)
{
uint8_t v___x_394_; 
v___x_394_ = 1;
return v___x_394_;
}
else
{
uint8_t v___x_395_; 
v___x_395_ = 0;
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isPublic___boxed(lean_object* v_x_396_){
_start:
{
uint8_t v_x_21__boxed_397_; uint8_t v_res_398_; lean_object* v_r_399_; 
v_x_21__boxed_397_ = lean_unbox(v_x_396_);
v_res_398_ = l_Lean_Elab_Visibility_isPublic(v_x_21__boxed_397_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Visibility_isInferredPublic(lean_object* v_env_400_, uint8_t v_v_401_){
_start:
{
uint8_t v___y_403_; uint8_t v_isExporting_406_; 
v_isExporting_406_ = lean_ctor_get_uint8(v_env_400_, sizeof(void*)*8);
if (v_isExporting_406_ == 0)
{
lean_object* v___x_407_; uint8_t v_isModule_408_; 
v___x_407_ = l_Lean_Environment_header(v_env_400_);
v_isModule_408_ = lean_ctor_get_uint8(v___x_407_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_407_);
if (v_isModule_408_ == 0)
{
uint8_t v___x_409_; 
v___x_409_ = 1;
v___y_403_ = v___x_409_;
goto v___jp_402_;
}
else
{
uint8_t v___x_410_; 
v___x_410_ = l_Lean_Elab_Visibility_isPublic(v_v_401_);
return v___x_410_;
}
}
else
{
v___y_403_ = v_isExporting_406_;
goto v___jp_402_;
}
v___jp_402_:
{
uint8_t v___x_404_; 
v___x_404_ = l_Lean_Elab_Visibility_isPrivate(v_v_401_);
if (v___x_404_ == 0)
{
return v___y_403_;
}
else
{
uint8_t v___x_405_; 
v___x_405_ = 0;
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Visibility_isInferredPublic___boxed(lean_object* v_env_411_, lean_object* v_v_412_){
_start:
{
uint8_t v_v_boxed_413_; uint8_t v_res_414_; lean_object* v_r_415_; 
v_v_boxed_413_ = lean_unbox(v_v_412_);
v_res_414_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_411_, v_v_boxed_413_);
lean_dec_ref(v_env_411_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
static lean_object* _init_l_Lean_Elab_elabVisibility___redArg___closed__6(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___closed__5));
v___x_431_ = l_Lean_stringToMessageData(v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility___redArg(lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_vis_x3f_434_){
_start:
{
if (lean_obj_tag(v_vis_x3f_434_) == 0)
{
lean_object* v_toApplicative_435_; lean_object* v_toPure_436_; uint8_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_toApplicative_435_ = lean_ctor_get(v_inst_432_, 0);
lean_inc_ref(v_toApplicative_435_);
lean_dec_ref(v_inst_433_);
lean_dec_ref(v_inst_432_);
v_toPure_436_ = lean_ctor_get(v_toApplicative_435_, 1);
lean_inc(v_toPure_436_);
lean_dec_ref(v_toApplicative_435_);
v___x_437_ = 0;
v___x_438_ = lean_box(v___x_437_);
v___x_439_ = lean_apply_2(v_toPure_436_, lean_box(0), v___x_438_);
return v___x_439_;
}
else
{
lean_object* v_toApplicative_440_; lean_object* v_toPure_441_; lean_object* v_val_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_toApplicative_440_ = lean_ctor_get(v_inst_432_, 0);
v_toPure_441_ = lean_ctor_get(v_toApplicative_440_, 1);
v_val_442_ = lean_ctor_get(v_vis_x3f_434_, 0);
lean_inc_n(v_val_442_, 2);
lean_dec_ref(v_vis_x3f_434_);
v___x_443_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___closed__3));
v___x_444_ = l_Lean_Syntax_isOfKind(v_val_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = ((lean_object*)(l_Lean_Elab_elabVisibility___redArg___closed__4));
lean_inc(v_val_442_);
v___x_446_ = l_Lean_Syntax_isOfKind(v_val_442_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_obj_once(&l_Lean_Elab_elabVisibility___redArg___closed__6, &l_Lean_Elab_elabVisibility___redArg___closed__6_once, _init_l_Lean_Elab_elabVisibility___redArg___closed__6);
v___x_448_ = l_Lean_throwErrorAt___redArg(v_inst_432_, v_inst_433_, v_val_442_, v___x_447_);
return v___x_448_;
}
else
{
uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
lean_inc(v_toPure_441_);
lean_dec(v_val_442_);
lean_dec_ref(v_inst_433_);
lean_dec_ref(v_inst_432_);
v___x_449_ = 2;
v___x_450_ = lean_box(v___x_449_);
v___x_451_ = lean_apply_2(v_toPure_441_, lean_box(0), v___x_450_);
return v___x_451_;
}
}
else
{
uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc(v_toPure_441_);
lean_dec(v_val_442_);
lean_dec_ref(v_inst_433_);
lean_dec_ref(v_inst_432_);
v___x_452_ = 1;
v___x_453_ = lean_box(v___x_452_);
v___x_454_ = lean_apply_2(v_toPure_441_, lean_box(0), v___x_453_);
return v___x_454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabVisibility(lean_object* v_m_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_vis_x3f_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Elab_elabVisibility___redArg(v_inst_456_, v_inst_457_, v_vis_x3f_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx(uint8_t v_x_460_){
_start:
{
switch(v_x_460_)
{
case 0:
{
lean_object* v___x_461_; 
v___x_461_ = lean_unsigned_to_nat(0u);
return v___x_461_;
}
case 1:
{
lean_object* v___x_462_; 
v___x_462_ = lean_unsigned_to_nat(1u);
return v___x_462_;
}
default: 
{
lean_object* v___x_463_; 
v___x_463_ = lean_unsigned_to_nat(2u);
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___boxed(lean_object* v_x_464_){
_start:
{
uint8_t v_x_boxed_465_; lean_object* v_res_466_; 
v_x_boxed_465_ = lean_unbox(v_x_464_);
v_res_466_ = l_Lean_Elab_RecKind_ctorIdx(v_x_boxed_465_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx(uint8_t v_x_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Elab_RecKind_ctorIdx(v_x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx___boxed(lean_object* v_x_469_){
_start:
{
uint8_t v_x_4__boxed_470_; lean_object* v_res_471_; 
v_x_4__boxed_470_ = lean_unbox(v_x_469_);
v_res_471_ = l_Lean_Elab_RecKind_toCtorIdx(v_x_4__boxed_470_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg(lean_object* v_k_472_){
_start:
{
lean_inc(v_k_472_);
return v_k_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg___boxed(lean_object* v_k_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Elab_RecKind_ctorElim___redArg(v_k_473_);
lean_dec(v_k_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim(lean_object* v_motive_475_, lean_object* v_ctorIdx_476_, uint8_t v_t_477_, lean_object* v_h_478_, lean_object* v_k_479_){
_start:
{
lean_inc(v_k_479_);
return v_k_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___boxed(lean_object* v_motive_480_, lean_object* v_ctorIdx_481_, lean_object* v_t_482_, lean_object* v_h_483_, lean_object* v_k_484_){
_start:
{
uint8_t v_t_boxed_485_; lean_object* v_res_486_; 
v_t_boxed_485_ = lean_unbox(v_t_482_);
v_res_486_ = l_Lean_Elab_RecKind_ctorElim(v_motive_480_, v_ctorIdx_481_, v_t_boxed_485_, v_h_483_, v_k_484_);
lean_dec(v_k_484_);
lean_dec(v_ctorIdx_481_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg(lean_object* v_partial_487_){
_start:
{
lean_inc(v_partial_487_);
return v_partial_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg___boxed(lean_object* v_partial_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Elab_RecKind_partial_elim___redArg(v_partial_488_);
lean_dec(v_partial_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim(lean_object* v_motive_490_, uint8_t v_t_491_, lean_object* v_h_492_, lean_object* v_partial_493_){
_start:
{
lean_inc(v_partial_493_);
return v_partial_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___boxed(lean_object* v_motive_494_, lean_object* v_t_495_, lean_object* v_h_496_, lean_object* v_partial_497_){
_start:
{
uint8_t v_t_boxed_498_; lean_object* v_res_499_; 
v_t_boxed_498_ = lean_unbox(v_t_495_);
v_res_499_ = l_Lean_Elab_RecKind_partial_elim(v_motive_494_, v_t_boxed_498_, v_h_496_, v_partial_497_);
lean_dec(v_partial_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg(lean_object* v_nonrec_500_){
_start:
{
lean_inc(v_nonrec_500_);
return v_nonrec_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg___boxed(lean_object* v_nonrec_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Elab_RecKind_nonrec_elim___redArg(v_nonrec_501_);
lean_dec(v_nonrec_501_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim(lean_object* v_motive_503_, uint8_t v_t_504_, lean_object* v_h_505_, lean_object* v_nonrec_506_){
_start:
{
lean_inc(v_nonrec_506_);
return v_nonrec_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___boxed(lean_object* v_motive_507_, lean_object* v_t_508_, lean_object* v_h_509_, lean_object* v_nonrec_510_){
_start:
{
uint8_t v_t_boxed_511_; lean_object* v_res_512_; 
v_t_boxed_511_ = lean_unbox(v_t_508_);
v_res_512_ = l_Lean_Elab_RecKind_nonrec_elim(v_motive_507_, v_t_boxed_511_, v_h_509_, v_nonrec_510_);
lean_dec(v_nonrec_510_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg(lean_object* v_default_513_){
_start:
{
lean_inc(v_default_513_);
return v_default_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg___boxed(lean_object* v_default_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_Elab_RecKind_default_elim___redArg(v_default_514_);
lean_dec(v_default_514_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim(lean_object* v_motive_516_, uint8_t v_t_517_, lean_object* v_h_518_, lean_object* v_default_519_){
_start:
{
lean_inc(v_default_519_);
return v_default_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___boxed(lean_object* v_motive_520_, lean_object* v_t_521_, lean_object* v_h_522_, lean_object* v_default_523_){
_start:
{
uint8_t v_t_boxed_524_; lean_object* v_res_525_; 
v_t_boxed_524_ = lean_unbox(v_t_521_);
v_res_525_ = l_Lean_Elab_RecKind_default_elim(v_motive_520_, v_t_boxed_524_, v_h_522_, v_default_523_);
lean_dec(v_default_523_);
return v_res_525_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind_default(void){
_start:
{
uint8_t v___x_526_; 
v___x_526_ = 0;
return v___x_526_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind(void){
_start:
{
uint8_t v___x_527_; 
v___x_527_ = 0;
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx(uint8_t v_x_528_){
_start:
{
switch(v_x_528_)
{
case 0:
{
lean_object* v___x_529_; 
v___x_529_ = lean_unsigned_to_nat(0u);
return v___x_529_;
}
case 1:
{
lean_object* v___x_530_; 
v___x_530_ = lean_unsigned_to_nat(1u);
return v___x_530_;
}
default: 
{
lean_object* v___x_531_; 
v___x_531_ = lean_unsigned_to_nat(2u);
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___boxed(lean_object* v_x_532_){
_start:
{
uint8_t v_x_boxed_533_; lean_object* v_res_534_; 
v_x_boxed_533_ = lean_unbox(v_x_532_);
v_res_534_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_boxed_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_toCtorIdx(uint8_t v_x_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_toCtorIdx___boxed(lean_object* v_x_537_){
_start:
{
uint8_t v_x_4__boxed_538_; lean_object* v_res_539_; 
v_x_4__boxed_538_ = lean_unbox(v_x_537_);
v_res_539_ = l_Lean_Elab_ComputeKind_toCtorIdx(v_x_4__boxed_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg(lean_object* v_k_540_){
_start:
{
lean_inc(v_k_540_);
return v_k_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg___boxed(lean_object* v_k_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Elab_ComputeKind_ctorElim___redArg(v_k_541_);
lean_dec(v_k_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim(lean_object* v_motive_543_, lean_object* v_ctorIdx_544_, uint8_t v_t_545_, lean_object* v_h_546_, lean_object* v_k_547_){
_start:
{
lean_inc(v_k_547_);
return v_k_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___boxed(lean_object* v_motive_548_, lean_object* v_ctorIdx_549_, lean_object* v_t_550_, lean_object* v_h_551_, lean_object* v_k_552_){
_start:
{
uint8_t v_t_boxed_553_; lean_object* v_res_554_; 
v_t_boxed_553_ = lean_unbox(v_t_550_);
v_res_554_ = l_Lean_Elab_ComputeKind_ctorElim(v_motive_548_, v_ctorIdx_549_, v_t_boxed_553_, v_h_551_, v_k_552_);
lean_dec(v_k_552_);
lean_dec(v_ctorIdx_549_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg(lean_object* v_regular_555_){
_start:
{
lean_inc(v_regular_555_);
return v_regular_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg___boxed(lean_object* v_regular_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Elab_ComputeKind_regular_elim___redArg(v_regular_556_);
lean_dec(v_regular_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim(lean_object* v_motive_558_, uint8_t v_t_559_, lean_object* v_h_560_, lean_object* v_regular_561_){
_start:
{
lean_inc(v_regular_561_);
return v_regular_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___boxed(lean_object* v_motive_562_, lean_object* v_t_563_, lean_object* v_h_564_, lean_object* v_regular_565_){
_start:
{
uint8_t v_t_boxed_566_; lean_object* v_res_567_; 
v_t_boxed_566_ = lean_unbox(v_t_563_);
v_res_567_ = l_Lean_Elab_ComputeKind_regular_elim(v_motive_562_, v_t_boxed_566_, v_h_564_, v_regular_565_);
lean_dec(v_regular_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg(lean_object* v_meta_568_){
_start:
{
lean_inc(v_meta_568_);
return v_meta_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg___boxed(lean_object* v_meta_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Elab_ComputeKind_meta_elim___redArg(v_meta_569_);
lean_dec(v_meta_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim(lean_object* v_motive_571_, uint8_t v_t_572_, lean_object* v_h_573_, lean_object* v_meta_574_){
_start:
{
lean_inc(v_meta_574_);
return v_meta_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___boxed(lean_object* v_motive_575_, lean_object* v_t_576_, lean_object* v_h_577_, lean_object* v_meta_578_){
_start:
{
uint8_t v_t_boxed_579_; lean_object* v_res_580_; 
v_t_boxed_579_ = lean_unbox(v_t_576_);
v_res_580_ = l_Lean_Elab_ComputeKind_meta_elim(v_motive_575_, v_t_boxed_579_, v_h_577_, v_meta_578_);
lean_dec(v_meta_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(lean_object* v_noncomputable_581_){
_start:
{
lean_inc(v_noncomputable_581_);
return v_noncomputable_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg___boxed(lean_object* v_noncomputable_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(v_noncomputable_582_);
lean_dec(v_noncomputable_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim(lean_object* v_motive_584_, uint8_t v_t_585_, lean_object* v_h_586_, lean_object* v_noncomputable_587_){
_start:
{
lean_inc(v_noncomputable_587_);
return v_noncomputable_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___boxed(lean_object* v_motive_588_, lean_object* v_t_589_, lean_object* v_h_590_, lean_object* v_noncomputable_591_){
_start:
{
uint8_t v_t_boxed_592_; lean_object* v_res_593_; 
v_t_boxed_592_ = lean_unbox(v_t_589_);
v_res_593_ = l_Lean_Elab_ComputeKind_noncomputable_elim(v_motive_588_, v_t_boxed_592_, v_h_590_, v_noncomputable_591_);
lean_dec(v_noncomputable_591_);
return v_res_593_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind_default(void){
_start:
{
uint8_t v___x_594_; 
v___x_594_ = 0;
return v___x_594_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind(void){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = 0;
return v___x_595_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqComputeKind_beq(uint8_t v_x_596_, uint8_t v_y_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_598_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_596_);
v___x_599_ = l_Lean_Elab_ComputeKind_ctorIdx(v_y_597_);
v___x_600_ = lean_nat_dec_eq(v___x_598_, v___x_599_);
lean_dec(v___x_599_);
lean_dec(v___x_598_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqComputeKind_beq___boxed(lean_object* v_x_601_, lean_object* v_y_602_){
_start:
{
uint8_t v_x_17__boxed_603_; uint8_t v_y_18__boxed_604_; uint8_t v_res_605_; lean_object* v_r_606_; 
v_x_17__boxed_603_ = lean_unbox(v_x_601_);
v_y_18__boxed_604_ = lean_unbox(v_y_602_);
v_res_605_ = l_Lean_Elab_instBEqComputeKind_beq(v_x_17__boxed_603_, v_y_18__boxed_604_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
static lean_object* _init_l_Lean_Elab_instReprComputeKind_repr___closed__6(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(2u);
v___x_619_ = lean_nat_to_int(v___x_618_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_Elab_instReprComputeKind_repr___closed__7(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_to_int(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprComputeKind_repr(uint8_t v_x_622_, lean_object* v_prec_623_){
_start:
{
lean_object* v___y_625_; lean_object* v___y_632_; lean_object* v___y_639_; 
switch(v_x_622_)
{
case 0:
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(1024u);
v___x_646_ = lean_nat_dec_le(v___x_645_, v_prec_623_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
v___x_647_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_625_ = v___x_647_;
goto v___jp_624_;
}
else
{
lean_object* v___x_648_; 
v___x_648_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_625_ = v___x_648_;
goto v___jp_624_;
}
}
case 1:
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(1024u);
v___x_650_ = lean_nat_dec_le(v___x_649_, v_prec_623_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
v___x_651_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_632_ = v___x_651_;
goto v___jp_631_;
}
else
{
lean_object* v___x_652_; 
v___x_652_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_632_ = v___x_652_;
goto v___jp_631_;
}
}
default: 
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(1024u);
v___x_654_ = lean_nat_dec_le(v___x_653_, v_prec_623_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__6, &l_Lean_Elab_instReprComputeKind_repr___closed__6_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__6);
v___y_639_ = v___x_655_;
goto v___jp_638_;
}
else
{
lean_object* v___x_656_; 
v___x_656_ = lean_obj_once(&l_Lean_Elab_instReprComputeKind_repr___closed__7, &l_Lean_Elab_instReprComputeKind_repr___closed__7_once, _init_l_Lean_Elab_instReprComputeKind_repr___closed__7);
v___y_639_ = v___x_656_;
goto v___jp_638_;
}
}
}
v___jp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_626_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__1));
lean_inc(v___y_625_);
v___x_627_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_627_, 0, v___y_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = 0;
v___x_629_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*1, v___x_628_);
v___x_630_ = l_Repr_addAppParen(v___x_629_, v_prec_623_);
return v___x_630_;
}
v___jp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_633_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__3));
lean_inc(v___y_632_);
v___x_634_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_634_, 0, v___y_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = 0;
v___x_636_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set_uint8(v___x_636_, sizeof(void*)*1, v___x_635_);
v___x_637_ = l_Repr_addAppParen(v___x_636_, v_prec_623_);
return v___x_637_;
}
v___jp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_640_ = ((lean_object*)(l_Lean_Elab_instReprComputeKind_repr___closed__5));
lean_inc(v___y_639_);
v___x_641_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_641_, 0, v___y_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = 0;
v___x_643_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set_uint8(v___x_643_, sizeof(void*)*1, v___x_642_);
v___x_644_ = l_Repr_addAppParen(v___x_643_, v_prec_623_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprComputeKind_repr___boxed(lean_object* v_x_657_, lean_object* v_prec_658_){
_start:
{
uint8_t v_x_177__boxed_659_; lean_object* v_res_660_; 
v_x_177__boxed_659_ = lean_unbox(v_x_657_);
v_res_660_ = l_Lean_Elab_instReprComputeKind_repr(v_x_177__boxed_659_, v_prec_658_);
lean_dec(v_prec_658_);
return v_res_660_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object* v_m_675_){
_start:
{
uint8_t v_visibility_676_; uint8_t v___x_677_; 
v_visibility_676_ = lean_ctor_get_uint8(v_m_675_, sizeof(void*)*3);
v___x_677_ = l_Lean_Elab_Visibility_isPrivate(v_visibility_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPrivate___boxed(lean_object* v_m_678_){
_start:
{
uint8_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = l_Lean_Elab_Modifiers_isPrivate(v_m_678_);
lean_dec_ref(v_m_678_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPublic(lean_object* v_m_681_){
_start:
{
uint8_t v_visibility_682_; uint8_t v___x_683_; 
v_visibility_682_ = lean_ctor_get_uint8(v_m_681_, sizeof(void*)*3);
v___x_683_ = l_Lean_Elab_Visibility_isPublic(v_visibility_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPublic___boxed(lean_object* v_m_684_){
_start:
{
uint8_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = l_Lean_Elab_Modifiers_isPublic(v_m_684_);
lean_dec_ref(v_m_684_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isInferredPublic(lean_object* v_env_687_, lean_object* v_m_688_){
_start:
{
uint8_t v_visibility_689_; uint8_t v___x_690_; 
v_visibility_689_ = lean_ctor_get_uint8(v_m_688_, sizeof(void*)*3);
v___x_690_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_687_, v_visibility_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isInferredPublic___boxed(lean_object* v_env_691_, lean_object* v_m_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l_Lean_Elab_Modifiers_isInferredPublic(v_env_691_, v_m_692_);
lean_dec_ref(v_m_692_);
lean_dec_ref(v_env_691_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object* v_x_695_){
_start:
{
uint8_t v_recKind_696_; 
v_recKind_696_ = lean_ctor_get_uint8(v_x_695_, sizeof(void*)*3 + 3);
if (v_recKind_696_ == 0)
{
uint8_t v___x_697_; 
v___x_697_ = 1;
return v___x_697_;
}
else
{
uint8_t v___x_698_; 
v___x_698_ = 0;
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPartial___boxed(lean_object* v_x_699_){
_start:
{
uint8_t v_res_700_; lean_object* v_r_701_; 
v_res_700_ = l_Lean_Elab_Modifiers_isPartial(v_x_699_);
lean_dec_ref(v_x_699_);
v_r_701_ = lean_box(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNonrec(lean_object* v_x_702_){
_start:
{
uint8_t v_recKind_703_; 
v_recKind_703_ = lean_ctor_get_uint8(v_x_702_, sizeof(void*)*3 + 3);
if (v_recKind_703_ == 1)
{
uint8_t v___x_704_; 
v___x_704_ = 1;
return v___x_704_;
}
else
{
uint8_t v___x_705_; 
v___x_705_ = 0;
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNonrec___boxed(lean_object* v_x_706_){
_start:
{
uint8_t v_res_707_; lean_object* v_r_708_; 
v_res_707_ = l_Lean_Elab_Modifiers_isNonrec(v_x_706_);
lean_dec_ref(v_x_706_);
v_r_708_ = lean_box(v_res_707_);
return v_r_708_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isMeta(lean_object* v_m_709_){
_start:
{
uint8_t v_computeKind_710_; 
v_computeKind_710_ = lean_ctor_get_uint8(v_m_709_, sizeof(void*)*3 + 2);
if (v_computeKind_710_ == 1)
{
uint8_t v___x_711_; 
v___x_711_ = 1;
return v___x_711_;
}
else
{
uint8_t v___x_712_; 
v___x_712_ = 0;
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isMeta___boxed(lean_object* v_m_713_){
_start:
{
uint8_t v_res_714_; lean_object* v_r_715_; 
v_res_714_ = l_Lean_Elab_Modifiers_isMeta(v_m_713_);
lean_dec_ref(v_m_713_);
v_r_715_ = lean_box(v_res_714_);
return v_r_715_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNoncomputable(lean_object* v_m_716_){
_start:
{
uint8_t v_computeKind_717_; 
v_computeKind_717_ = lean_ctor_get_uint8(v_m_716_, sizeof(void*)*3 + 2);
if (v_computeKind_717_ == 2)
{
uint8_t v___x_718_; 
v___x_718_ = 1;
return v___x_718_;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = 0;
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNoncomputable___boxed(lean_object* v_m_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Lean_Elab_Modifiers_isNoncomputable(v_m_720_);
lean_dec_ref(v_m_720_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addAttr(lean_object* v_modifiers_723_, lean_object* v_attr_724_){
_start:
{
lean_object* v_stx_725_; lean_object* v_docString_x3f_726_; uint8_t v_visibility_727_; uint8_t v_isProtected_728_; uint8_t v_computeKind_729_; uint8_t v_recKind_730_; uint8_t v_isUnsafe_731_; lean_object* v_attrs_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_740_; 
v_stx_725_ = lean_ctor_get(v_modifiers_723_, 0);
v_docString_x3f_726_ = lean_ctor_get(v_modifiers_723_, 1);
v_visibility_727_ = lean_ctor_get_uint8(v_modifiers_723_, sizeof(void*)*3);
v_isProtected_728_ = lean_ctor_get_uint8(v_modifiers_723_, sizeof(void*)*3 + 1);
v_computeKind_729_ = lean_ctor_get_uint8(v_modifiers_723_, sizeof(void*)*3 + 2);
v_recKind_730_ = lean_ctor_get_uint8(v_modifiers_723_, sizeof(void*)*3 + 3);
v_isUnsafe_731_ = lean_ctor_get_uint8(v_modifiers_723_, sizeof(void*)*3 + 4);
v_attrs_732_ = lean_ctor_get(v_modifiers_723_, 2);
v_isSharedCheck_740_ = !lean_is_exclusive(v_modifiers_723_);
if (v_isSharedCheck_740_ == 0)
{
v___x_734_ = v_modifiers_723_;
v_isShared_735_ = v_isSharedCheck_740_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_attrs_732_);
lean_inc(v_docString_x3f_726_);
lean_inc(v_stx_725_);
lean_dec(v_modifiers_723_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_740_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_736_ = lean_array_push(v_attrs_732_, v_attr_724_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 2, v___x_736_);
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_stx_725_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_docString_x3f_726_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v___x_736_);
lean_ctor_set_uint8(v_reuseFailAlloc_739_, sizeof(void*)*3, v_visibility_727_);
lean_ctor_set_uint8(v_reuseFailAlloc_739_, sizeof(void*)*3 + 1, v_isProtected_728_);
lean_ctor_set_uint8(v_reuseFailAlloc_739_, sizeof(void*)*3 + 2, v_computeKind_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_739_, sizeof(void*)*3 + 3, v_recKind_730_);
lean_ctor_set_uint8(v_reuseFailAlloc_739_, sizeof(void*)*3 + 4, v_isUnsafe_731_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addFirstAttr(lean_object* v_modifiers_741_, lean_object* v_attr_742_){
_start:
{
lean_object* v_stx_743_; lean_object* v_docString_x3f_744_; uint8_t v_visibility_745_; uint8_t v_isProtected_746_; uint8_t v_computeKind_747_; uint8_t v_recKind_748_; uint8_t v_isUnsafe_749_; lean_object* v_attrs_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_761_; 
v_stx_743_ = lean_ctor_get(v_modifiers_741_, 0);
v_docString_x3f_744_ = lean_ctor_get(v_modifiers_741_, 1);
v_visibility_745_ = lean_ctor_get_uint8(v_modifiers_741_, sizeof(void*)*3);
v_isProtected_746_ = lean_ctor_get_uint8(v_modifiers_741_, sizeof(void*)*3 + 1);
v_computeKind_747_ = lean_ctor_get_uint8(v_modifiers_741_, sizeof(void*)*3 + 2);
v_recKind_748_ = lean_ctor_get_uint8(v_modifiers_741_, sizeof(void*)*3 + 3);
v_isUnsafe_749_ = lean_ctor_get_uint8(v_modifiers_741_, sizeof(void*)*3 + 4);
v_attrs_750_ = lean_ctor_get(v_modifiers_741_, 2);
v_isSharedCheck_761_ = !lean_is_exclusive(v_modifiers_741_);
if (v_isSharedCheck_761_ == 0)
{
v___x_752_ = v_modifiers_741_;
v_isShared_753_ = v_isSharedCheck_761_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_attrs_750_);
lean_inc(v_docString_x3f_744_);
lean_inc(v_stx_743_);
lean_dec(v_modifiers_741_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_761_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_mk_empty_array_with_capacity(v___x_754_);
v___x_756_ = lean_array_push(v___x_755_, v_attr_742_);
v___x_757_ = l_Array_append___redArg(v___x_756_, v_attrs_750_);
lean_dec_ref(v_attrs_750_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 2, v___x_757_);
v___x_759_ = v___x_752_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_stx_743_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_docString_x3f_744_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v___x_757_);
lean_ctor_set_uint8(v_reuseFailAlloc_760_, sizeof(void*)*3, v_visibility_745_);
lean_ctor_set_uint8(v_reuseFailAlloc_760_, sizeof(void*)*3 + 1, v_isProtected_746_);
lean_ctor_set_uint8(v_reuseFailAlloc_760_, sizeof(void*)*3 + 2, v_computeKind_747_);
lean_ctor_set_uint8(v_reuseFailAlloc_760_, sizeof(void*)*3 + 3, v_recKind_748_);
lean_ctor_set_uint8(v_reuseFailAlloc_760_, sizeof(void*)*3 + 4, v_isUnsafe_749_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(lean_object* v_p_762_, lean_object* v_as_763_, size_t v_i_764_, size_t v_stop_765_, lean_object* v_b_766_){
_start:
{
lean_object* v___y_768_; uint8_t v___x_772_; 
v___x_772_ = lean_usize_dec_eq(v_i_764_, v_stop_765_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_773_ = lean_array_uget_borrowed(v_as_763_, v_i_764_);
lean_inc_ref(v_p_762_);
lean_inc(v___x_773_);
v___x_774_ = lean_apply_1(v_p_762_, v___x_773_);
v___x_775_ = lean_unbox(v___x_774_);
if (v___x_775_ == 0)
{
v___y_768_ = v_b_766_;
goto v___jp_767_;
}
else
{
lean_object* v___x_776_; 
lean_inc(v___x_773_);
v___x_776_ = lean_array_push(v_b_766_, v___x_773_);
v___y_768_ = v___x_776_;
goto v___jp_767_;
}
}
else
{
lean_dec_ref(v_p_762_);
return v_b_766_;
}
v___jp_767_:
{
size_t v___x_769_; size_t v___x_770_; 
v___x_769_ = ((size_t)1ULL);
v___x_770_ = lean_usize_add(v_i_764_, v___x_769_);
v_i_764_ = v___x_770_;
v_b_766_ = v___y_768_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0___boxed(lean_object* v_p_777_, lean_object* v_as_778_, lean_object* v_i_779_, lean_object* v_stop_780_, lean_object* v_b_781_){
_start:
{
size_t v_i_boxed_782_; size_t v_stop_boxed_783_; lean_object* v_res_784_; 
v_i_boxed_782_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_stop_boxed_783_ = lean_unbox_usize(v_stop_780_);
lean_dec(v_stop_780_);
v_res_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_777_, v_as_778_, v_i_boxed_782_, v_stop_boxed_783_, v_b_781_);
lean_dec_ref(v_as_778_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object* v_modifiers_785_, lean_object* v_p_786_){
_start:
{
lean_object* v_stx_787_; lean_object* v_docString_x3f_788_; uint8_t v_visibility_789_; uint8_t v_isProtected_790_; uint8_t v_computeKind_791_; uint8_t v_recKind_792_; uint8_t v_isUnsafe_793_; lean_object* v_attrs_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_821_; 
v_stx_787_ = lean_ctor_get(v_modifiers_785_, 0);
v_docString_x3f_788_ = lean_ctor_get(v_modifiers_785_, 1);
v_visibility_789_ = lean_ctor_get_uint8(v_modifiers_785_, sizeof(void*)*3);
v_isProtected_790_ = lean_ctor_get_uint8(v_modifiers_785_, sizeof(void*)*3 + 1);
v_computeKind_791_ = lean_ctor_get_uint8(v_modifiers_785_, sizeof(void*)*3 + 2);
v_recKind_792_ = lean_ctor_get_uint8(v_modifiers_785_, sizeof(void*)*3 + 3);
v_isUnsafe_793_ = lean_ctor_get_uint8(v_modifiers_785_, sizeof(void*)*3 + 4);
v_attrs_794_ = lean_ctor_get(v_modifiers_785_, 2);
v_isSharedCheck_821_ = !lean_is_exclusive(v_modifiers_785_);
if (v_isSharedCheck_821_ == 0)
{
v___x_796_ = v_modifiers_785_;
v_isShared_797_ = v_isSharedCheck_821_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_attrs_794_);
lean_inc(v_docString_x3f_788_);
lean_inc(v_stx_787_);
lean_dec(v_modifiers_785_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_821_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_array_get_size(v_attrs_794_);
v___x_800_ = ((lean_object*)(l_Lean_Elab_instInhabitedModifiers_default___closed__0));
v___x_801_ = lean_nat_dec_lt(v___x_798_, v___x_799_);
if (v___x_801_ == 0)
{
lean_object* v___x_803_; 
lean_dec_ref(v_attrs_794_);
lean_dec_ref(v_p_786_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 2, v___x_800_);
v___x_803_ = v___x_796_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_stx_787_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_docString_x3f_788_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v___x_800_);
lean_ctor_set_uint8(v_reuseFailAlloc_804_, sizeof(void*)*3, v_visibility_789_);
lean_ctor_set_uint8(v_reuseFailAlloc_804_, sizeof(void*)*3 + 1, v_isProtected_790_);
lean_ctor_set_uint8(v_reuseFailAlloc_804_, sizeof(void*)*3 + 2, v_computeKind_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_804_, sizeof(void*)*3 + 3, v_recKind_792_);
lean_ctor_set_uint8(v_reuseFailAlloc_804_, sizeof(void*)*3 + 4, v_isUnsafe_793_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
else
{
uint8_t v___x_805_; 
v___x_805_ = lean_nat_dec_le(v___x_799_, v___x_799_);
if (v___x_805_ == 0)
{
if (v___x_801_ == 0)
{
lean_object* v___x_807_; 
lean_dec_ref(v_attrs_794_);
lean_dec_ref(v_p_786_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 2, v___x_800_);
v___x_807_ = v___x_796_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_stx_787_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_docString_x3f_788_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v___x_800_);
lean_ctor_set_uint8(v_reuseFailAlloc_808_, sizeof(void*)*3, v_visibility_789_);
lean_ctor_set_uint8(v_reuseFailAlloc_808_, sizeof(void*)*3 + 1, v_isProtected_790_);
lean_ctor_set_uint8(v_reuseFailAlloc_808_, sizeof(void*)*3 + 2, v_computeKind_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_808_, sizeof(void*)*3 + 3, v_recKind_792_);
lean_ctor_set_uint8(v_reuseFailAlloc_808_, sizeof(void*)*3 + 4, v_isUnsafe_793_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
else
{
size_t v___x_809_; size_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_809_ = ((size_t)0ULL);
v___x_810_ = lean_usize_of_nat(v___x_799_);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_786_, v_attrs_794_, v___x_809_, v___x_810_, v___x_800_);
lean_dec_ref(v_attrs_794_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 2, v___x_811_);
v___x_813_ = v___x_796_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_stx_787_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_docString_x3f_788_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v___x_811_);
lean_ctor_set_uint8(v_reuseFailAlloc_814_, sizeof(void*)*3, v_visibility_789_);
lean_ctor_set_uint8(v_reuseFailAlloc_814_, sizeof(void*)*3 + 1, v_isProtected_790_);
lean_ctor_set_uint8(v_reuseFailAlloc_814_, sizeof(void*)*3 + 2, v_computeKind_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_814_, sizeof(void*)*3 + 3, v_recKind_792_);
lean_ctor_set_uint8(v_reuseFailAlloc_814_, sizeof(void*)*3 + 4, v_isUnsafe_793_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
else
{
size_t v___x_815_; size_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_815_ = ((size_t)0ULL);
v___x_816_ = lean_usize_of_nat(v___x_799_);
v___x_817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_786_, v_attrs_794_, v___x_815_, v___x_816_, v___x_800_);
lean_dec_ref(v_attrs_794_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 2, v___x_817_);
v___x_819_ = v___x_796_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_stx_787_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_docString_x3f_788_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v___x_817_);
lean_ctor_set_uint8(v_reuseFailAlloc_820_, sizeof(void*)*3, v_visibility_789_);
lean_ctor_set_uint8(v_reuseFailAlloc_820_, sizeof(void*)*3 + 1, v_isProtected_790_);
lean_ctor_set_uint8(v_reuseFailAlloc_820_, sizeof(void*)*3 + 2, v_computeKind_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_820_, sizeof(void*)*3 + 3, v_recKind_792_);
lean_ctor_set_uint8(v_reuseFailAlloc_820_, sizeof(void*)*3 + 4, v_isUnsafe_793_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(lean_object* v_p_822_, lean_object* v_as_823_, size_t v_i_824_, size_t v_stop_825_){
_start:
{
uint8_t v___x_826_; 
v___x_826_ = lean_usize_dec_eq(v_i_824_, v_stop_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_827_ = lean_array_uget_borrowed(v_as_823_, v_i_824_);
lean_inc_ref(v_p_822_);
lean_inc(v___x_827_);
v___x_828_ = lean_apply_1(v_p_822_, v___x_827_);
v___x_829_ = lean_unbox(v___x_828_);
if (v___x_829_ == 0)
{
size_t v___x_830_; size_t v___x_831_; 
v___x_830_ = ((size_t)1ULL);
v___x_831_ = lean_usize_add(v_i_824_, v___x_830_);
v_i_824_ = v___x_831_;
goto _start;
}
else
{
uint8_t v___x_833_; 
lean_dec_ref(v_p_822_);
v___x_833_ = lean_unbox(v___x_828_);
return v___x_833_;
}
}
else
{
uint8_t v___x_834_; 
lean_dec_ref(v_p_822_);
v___x_834_ = 0;
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0___boxed(lean_object* v_p_835_, lean_object* v_as_836_, lean_object* v_i_837_, lean_object* v_stop_838_){
_start:
{
size_t v_i_boxed_839_; size_t v_stop_boxed_840_; uint8_t v_res_841_; lean_object* v_r_842_; 
v_i_boxed_839_ = lean_unbox_usize(v_i_837_);
lean_dec(v_i_837_);
v_stop_boxed_840_ = lean_unbox_usize(v_stop_838_);
lean_dec(v_stop_838_);
v_res_841_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_835_, v_as_836_, v_i_boxed_839_, v_stop_boxed_840_);
lean_dec_ref(v_as_836_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_anyAttr(lean_object* v_modifiers_843_, lean_object* v_p_844_){
_start:
{
lean_object* v_attrs_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v_attrs_845_ = lean_ctor_get(v_modifiers_843_, 2);
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = lean_array_get_size(v_attrs_845_);
v___x_848_ = lean_nat_dec_lt(v___x_846_, v___x_847_);
if (v___x_848_ == 0)
{
lean_dec_ref(v_p_844_);
return v___x_848_;
}
else
{
if (v___x_848_ == 0)
{
lean_dec_ref(v_p_844_);
return v___x_848_;
}
else
{
size_t v___x_849_; size_t v___x_850_; uint8_t v___x_851_; 
v___x_849_ = ((size_t)0ULL);
v___x_850_ = lean_usize_of_nat(v___x_847_);
v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_844_, v_attrs_845_, v___x_849_, v___x_850_);
return v___x_851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_anyAttr___boxed(lean_object* v_modifiers_852_, lean_object* v_p_853_){
_start:
{
uint8_t v_res_854_; lean_object* v_r_855_; 
v_res_854_ = l_Lean_Elab_Modifiers_anyAttr(v_modifiers_852_, v_p_853_);
lean_dec_ref(v_modifiers_852_);
v_r_855_ = lean_box(v_res_854_);
return v_r_855_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__0));
v___x_859_ = lean_string_length(v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__2, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__2_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2);
v___x_861_ = lean_nat_to_int(v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__0(lean_object* v_attr_869_){
_start:
{
uint8_t v_kind_870_; lean_object* v_name_871_; lean_object* v_stx_872_; lean_object* v___y_874_; 
v_kind_870_ = lean_ctor_get_uint8(v_attr_869_, sizeof(void*)*2);
v_name_871_ = lean_ctor_get(v_attr_869_, 0);
lean_inc(v_name_871_);
v_stx_872_ = lean_ctor_get(v_attr_869_, 1);
lean_inc(v_stx_872_);
lean_dec_ref(v_attr_869_);
switch(v_kind_870_)
{
case 0:
{
lean_object* v___x_896_; 
v___x_896_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__6));
v___y_874_ = v___x_896_;
goto v___jp_873_;
}
case 1:
{
lean_object* v___x_897_; 
v___x_897_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__7));
v___y_874_ = v___x_897_;
goto v___jp_873_;
}
default: 
{
lean_object* v___x_898_; 
v___x_898_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__8));
v___y_874_ = v___x_898_;
goto v___jp_873_;
}
}
v___jp_873_:
{
lean_object* v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; 
lean_inc_ref(v___y_874_);
v___x_875_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_875_, 0, v___y_874_);
v___x_876_ = 1;
v___x_877_ = l_Lean_Name_toString(v_name_871_, v___x_876_);
v___x_878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
v___x_879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_875_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_box(0);
v___x_881_ = 0;
v___x_882_ = l_Lean_Syntax_formatStx(v_stx_872_, v___x_880_, v___x_881_);
v___x_883_ = l_Std_Format_defWidth;
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = l_Std_Format_pretty(v___x_882_, v___x_883_, v___x_884_, v___x_884_);
v___x_886_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
v___x_887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_879_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__3, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__3_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3);
v___x_889_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__4));
v___x_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v___x_887_);
v___x_891_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__5));
v___x_892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_888_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = 0;
v___x_895_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set_uint8(v___x_895_, sizeof(void*)*1, v___x_894_);
return v___x_895_;
}
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__0));
v___x_908_ = lean_string_length(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__5, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__5_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5);
v___x_910_ = lean_nat_to_int(v___x_909_);
return v___x_910_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__35(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__33));
v___x_967_ = lean_string_length(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__36(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__35, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__35_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__35);
v___x_969_ = lean_nat_to_int(v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__1(lean_object* v___f_979_, lean_object* v___f_980_, lean_object* v_m_981_){
_start:
{
lean_object* v_docString_x3f_982_; uint8_t v_visibility_983_; uint8_t v_isProtected_984_; uint8_t v_computeKind_985_; uint8_t v_recKind_986_; uint8_t v_isUnsafe_987_; lean_object* v_attrs_988_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1034_; 
v_docString_x3f_982_ = lean_ctor_get(v_m_981_, 1);
lean_inc(v_docString_x3f_982_);
v_visibility_983_ = lean_ctor_get_uint8(v_m_981_, sizeof(void*)*3);
v_isProtected_984_ = lean_ctor_get_uint8(v_m_981_, sizeof(void*)*3 + 1);
v_computeKind_985_ = lean_ctor_get_uint8(v_m_981_, sizeof(void*)*3 + 2);
v_recKind_986_ = lean_ctor_get_uint8(v_m_981_, sizeof(void*)*3 + 3);
v_isUnsafe_987_ = lean_ctor_get_uint8(v_m_981_, sizeof(void*)*3 + 4);
v_attrs_988_ = lean_ctor_get(v_m_981_, 2);
lean_inc_ref(v_attrs_988_);
lean_dec_ref(v_m_981_);
if (lean_obj_tag(v_docString_x3f_982_) == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_box(0);
v___y_1034_ = v___x_1038_;
goto v___jp_1033_;
}
else
{
lean_object* v_val_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1081_; 
v_val_1039_ = lean_ctor_get(v_docString_x3f_982_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_docString_x3f_982_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1041_ = v_docString_x3f_982_;
v_isShared_1042_ = v_isSharedCheck_1081_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_val_1039_);
lean_dec(v_docString_x3f_982_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1081_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_fst_1043_; lean_object* v_snd_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1080_; 
v_fst_1043_ = lean_ctor_get(v_val_1039_, 0);
v_snd_1044_ = lean_ctor_get(v_val_1039_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_val_1039_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1046_ = v_val_1039_;
v_isShared_1047_ = v_isSharedCheck_1080_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_snd_1044_);
lean_inc(v_fst_1043_);
lean_dec(v_val_1039_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1080_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1048_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__32));
v___x_1049_ = lean_box(0);
v___x_1050_ = 0;
v___x_1051_ = l_Lean_Syntax_formatStx(v_fst_1043_, v___x_1049_, v___x_1050_);
v___x_1052_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__2));
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 5);
lean_ctor_set(v___x_1046_, 1, v___x_1052_);
lean_ctor_set(v___x_1046_, 0, v___x_1051_);
v___x_1054_ = v___x_1046_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___y_1058_; uint8_t v___x_1076_; 
v___x_1055_ = lean_box(1);
v___x_1056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1076_ = lean_unbox(v_snd_1044_);
lean_dec(v_snd_1044_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__41));
v___y_1058_ = v___x_1077_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1078_; 
v___x_1078_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__42));
v___y_1058_ = v___x_1078_;
goto v___jp_1057_;
}
v___jp_1057_:
{
lean_object* v___x_1060_; 
lean_inc_ref(v___y_1058_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set_tag(v___x_1041_, 3);
lean_ctor_set(v___x_1041_, 0, v___y_1058_);
v___x_1060_ = v___x_1041_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___y_1058_);
v___x_1060_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1056_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__36, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__36_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__36);
v___x_1063_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__37));
v___x_1064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___x_1061_);
v___x_1065_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__38));
v___x_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1062_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = 0;
v___x_1069_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*1, v___x_1068_);
v___x_1070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1048_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__40));
v___x_1072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_box(0);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___y_1034_ = v___x_1074_;
goto v___jp_1033_;
}
}
}
}
}
}
v___jp_989_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v_components_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; 
lean_inc(v___y_991_);
v___x_992_ = l_List_appendTR___redArg(v___y_990_, v___y_991_);
v___x_993_ = lean_array_to_list(v_attrs_988_);
v___x_994_ = lean_box(0);
v___x_995_ = l_List_mapTR_loop___redArg(v___f_979_, v___x_993_, v___x_994_);
v_components_996_ = l_List_appendTR___redArg(v___x_992_, v___x_995_);
v___x_997_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__3));
v___x_998_ = l_Std_Format_joinSep___redArg(v___f_980_, v_components_996_, v___x_997_);
v___x_999_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__6, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__6_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__7));
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_998_);
v___x_1002_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__8));
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_999_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = 0;
v___x_1006_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*1, v___x_1005_);
return v___x_1006_;
}
v___jp_1007_:
{
lean_object* v___x_1010_; 
lean_inc(v___y_1009_);
v___x_1010_ = l_List_appendTR___redArg(v___y_1008_, v___y_1009_);
if (v_isUnsafe_987_ == 0)
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_box(0);
v___y_990_ = v___x_1010_;
v___y_991_ = v___x_1011_;
goto v___jp_989_;
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__11));
v___y_990_ = v___x_1010_;
v___y_991_ = v___x_1012_;
goto v___jp_989_;
}
}
v___jp_1013_:
{
lean_object* v___x_1016_; 
lean_inc(v___y_1015_);
v___x_1016_ = l_List_appendTR___redArg(v___y_1014_, v___y_1015_);
switch(v_recKind_986_)
{
case 0:
{
lean_object* v___x_1017_; 
v___x_1017_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__14));
v___y_1008_ = v___x_1016_;
v___y_1009_ = v___x_1017_;
goto v___jp_1007_;
}
case 1:
{
lean_object* v___x_1018_; 
v___x_1018_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__17));
v___y_1008_ = v___x_1016_;
v___y_1009_ = v___x_1018_;
goto v___jp_1007_;
}
default: 
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_box(0);
v___y_1008_ = v___x_1016_;
v___y_1009_ = v___x_1019_;
goto v___jp_1007_;
}
}
}
v___jp_1020_:
{
lean_object* v___x_1023_; 
lean_inc(v___y_1022_);
v___x_1023_ = l_List_appendTR___redArg(v___y_1021_, v___y_1022_);
switch(v_computeKind_985_)
{
case 0:
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_box(0);
v___y_1014_ = v___x_1023_;
v___y_1015_ = v___x_1024_;
goto v___jp_1013_;
}
case 1:
{
lean_object* v___x_1025_; 
v___x_1025_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__20));
v___y_1014_ = v___x_1023_;
v___y_1015_ = v___x_1025_;
goto v___jp_1013_;
}
default: 
{
lean_object* v___x_1026_; 
v___x_1026_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__23));
v___y_1014_ = v___x_1023_;
v___y_1015_ = v___x_1026_;
goto v___jp_1013_;
}
}
}
v___jp_1027_:
{
lean_object* v___x_1030_; 
lean_inc(v___y_1029_);
v___x_1030_ = l_List_appendTR___redArg(v___y_1028_, v___y_1029_);
if (v_isProtected_984_ == 0)
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_box(0);
v___y_1021_ = v___x_1030_;
v___y_1022_ = v___x_1031_;
goto v___jp_1020_;
}
else
{
lean_object* v___x_1032_; 
v___x_1032_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__26));
v___y_1021_ = v___x_1030_;
v___y_1022_ = v___x_1032_;
goto v___jp_1020_;
}
}
v___jp_1033_:
{
switch(v_visibility_983_)
{
case 0:
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_box(0);
v___y_1028_ = v___y_1034_;
v___y_1029_ = v___x_1035_;
goto v___jp_1027_;
}
case 1:
{
lean_object* v___x_1036_; 
v___x_1036_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__28));
v___y_1028_ = v___y_1034_;
v___y_1029_ = v___x_1036_;
goto v___jp_1027_;
}
default: 
{
lean_object* v___x_1037_; 
v___x_1037_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__30));
v___y_1028_ = v___y_1034_;
v___y_1029_ = v___x_1037_;
goto v___jp_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lam__0(lean_object* v_f_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = l_Std_Format_defWidth;
v___x_1090_ = lean_unsigned_to_nat(0u);
v___x_1091_ = l_Std_Format_pretty(v_f_1088_, v___x_1089_, v___x_1090_, v___x_1090_);
return v___x_1091_;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0));
v___x_1099_ = l_Lean_stringToMessageData(v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg(lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_optDocComment_1102_){
_start:
{
lean_object* v_toApplicative_1103_; lean_object* v_toPure_1104_; lean_object* v___x_1105_; 
v_toApplicative_1103_ = lean_ctor_get(v_inst_1100_, 0);
v_toPure_1104_ = lean_ctor_get(v_toApplicative_1103_, 1);
v___x_1105_ = l_Lean_Syntax_getOptional_x3f(v_optDocComment_1102_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_inc(v_toPure_1104_);
lean_dec_ref(v_inst_1101_);
lean_dec_ref(v_inst_1100_);
v___x_1106_ = lean_box(0);
v___x_1107_ = lean_apply_2(v_toPure_1104_, lean_box(0), v___x_1106_);
return v___x_1107_;
}
else
{
lean_object* v_val_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1129_; 
v_val_1108_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1110_ = v___x_1105_;
v_isShared_1111_ = v_isSharedCheck_1129_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_val_1108_);
lean_dec(v___x_1105_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1129_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_unsigned_to_nat(1u);
v___x_1113_ = l_Lean_Syntax_getArg(v_val_1108_, v___x_1112_);
if (lean_obj_tag(v___x_1113_) == 2)
{
lean_object* v_val_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
lean_inc(v_toPure_1104_);
lean_dec(v_val_1108_);
lean_dec_ref(v_inst_1101_);
lean_dec_ref(v_inst_1100_);
v_val_1114_ = lean_ctor_get(v___x_1113_, 1);
lean_inc_ref(v_val_1114_);
lean_dec_ref(v___x_1113_);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = lean_string_utf8_byte_size(v_val_1114_);
v___x_1117_ = lean_unsigned_to_nat(2u);
v___x_1118_ = lean_nat_sub(v___x_1116_, v___x_1117_);
v___x_1119_ = lean_string_utf8_extract(v_val_1114_, v___x_1115_, v___x_1118_);
lean_dec(v___x_1118_);
lean_dec_ref(v_val_1114_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1119_);
v___x_1121_ = v___x_1110_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_apply_2(v_toPure_1104_, lean_box(0), v___x_1121_);
return v___x_1122_;
}
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_del_object(v___x_1110_);
v___x_1124_ = lean_obj_once(&l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1, &l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1_once, _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1);
v___x_1125_ = l_Lean_MessageData_ofSyntax(v___x_1113_);
v___x_1126_ = l_Lean_indentD(v___x_1125_);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1124_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = l_Lean_throwErrorAt___redArg(v_inst_1100_, v_inst_1101_, v_val_1108_, v___x_1127_);
return v___x_1128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___boxed(lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_optDocComment_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1130_, v_inst_1131_, v_optDocComment_1132_);
lean_dec(v_optDocComment_1132_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f(lean_object* v_m_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_optDocComment_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1135_, v_inst_1136_, v_optDocComment_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___boxed(lean_object* v_m_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_optDocComment_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Elab_expandOptDocComment_x3f(v_m_1139_, v_inst_1140_, v_inst_1141_, v_optDocComment_1142_);
lean_dec(v_optDocComment_1142_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0(lean_object* v_stx_1144_, lean_object* v___y_1145_, uint8_t v_visibility_1146_, uint8_t v___y_1147_, uint8_t v___y_1148_, uint8_t v___y_1149_, lean_object* v_toPure_1150_, lean_object* v_unsafeStx_1151_, lean_object* v_attrs_1152_){
_start:
{
uint8_t v___y_1154_; uint8_t v___x_1157_; 
v___x_1157_ = l_Lean_Syntax_isNone(v_unsafeStx_1151_);
if (v___x_1157_ == 0)
{
uint8_t v___x_1158_; 
v___x_1158_ = 1;
v___y_1154_ = v___x_1158_;
goto v___jp_1153_;
}
else
{
uint8_t v___x_1159_; 
v___x_1159_ = 0;
v___y_1154_ = v___x_1159_;
goto v___jp_1153_;
}
v___jp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1155_, 0, v_stx_1144_);
lean_ctor_set(v___x_1155_, 1, v___y_1145_);
lean_ctor_set(v___x_1155_, 2, v_attrs_1152_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3, v_visibility_1146_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 1, v___y_1147_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 2, v___y_1148_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 3, v___y_1149_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 4, v___y_1154_);
v___x_1156_ = lean_apply_2(v_toPure_1150_, lean_box(0), v___x_1155_);
return v___x_1156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0___boxed(lean_object* v_stx_1160_, lean_object* v___y_1161_, lean_object* v_visibility_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v_toPure_1166_, lean_object* v_unsafeStx_1167_, lean_object* v_attrs_1168_){
_start:
{
uint8_t v_visibility_boxed_1169_; uint8_t v___y_482__boxed_1170_; uint8_t v___y_483__boxed_1171_; uint8_t v___y_484__boxed_1172_; lean_object* v_res_1173_; 
v_visibility_boxed_1169_ = lean_unbox(v_visibility_1162_);
v___y_482__boxed_1170_ = lean_unbox(v___y_1163_);
v___y_483__boxed_1171_ = lean_unbox(v___y_1164_);
v___y_484__boxed_1172_ = lean_unbox(v___y_1165_);
v_res_1173_ = l_Lean_Elab_elabModifiers___redArg___lam__0(v_stx_1160_, v___y_1161_, v_visibility_boxed_1169_, v___y_482__boxed_1170_, v___y_483__boxed_1171_, v___y_484__boxed_1172_, v_toPure_1166_, v_unsafeStx_1167_, v_attrs_1168_);
lean_dec(v_unsafeStx_1167_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__1(lean_object* v___f_1174_, lean_object* v_attrs_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_apply_1(v___f_1174_, v_attrs_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3(lean_object* v_stx_1177_, lean_object* v___y_1178_, uint8_t v___y_1179_, uint8_t v___y_1180_, lean_object* v_toPure_1181_, lean_object* v_unsafeStx_1182_, lean_object* v_attrsStx_1183_, lean_object* v___x_1184_, lean_object* v_toBind_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_protectedStx_1198_, uint8_t v_visibility_1199_){
_start:
{
uint8_t v___y_1201_; uint8_t v___x_1216_; 
v___x_1216_ = l_Lean_Syntax_isNone(v_protectedStx_1198_);
if (v___x_1216_ == 0)
{
uint8_t v___x_1217_; 
v___x_1217_ = 1;
v___y_1201_ = v___x_1217_;
goto v___jp_1200_;
}
else
{
uint8_t v___x_1218_; 
v___x_1218_ = 0;
v___y_1201_ = v___x_1218_;
goto v___jp_1200_;
}
v___jp_1200_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___f_1206_; lean_object* v___x_1207_; 
v___x_1202_ = lean_box(v_visibility_1199_);
v___x_1203_ = lean_box(v___y_1201_);
v___x_1204_ = lean_box(v___y_1179_);
v___x_1205_ = lean_box(v___y_1180_);
lean_inc(v_toPure_1181_);
v___f_1206_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_1206_, 0, v_stx_1177_);
lean_closure_set(v___f_1206_, 1, v___y_1178_);
lean_closure_set(v___f_1206_, 2, v___x_1202_);
lean_closure_set(v___f_1206_, 3, v___x_1203_);
lean_closure_set(v___f_1206_, 4, v___x_1204_);
lean_closure_set(v___f_1206_, 5, v___x_1205_);
lean_closure_set(v___f_1206_, 6, v_toPure_1181_);
lean_closure_set(v___f_1206_, 7, v_unsafeStx_1182_);
v___x_1207_ = l_Lean_Syntax_getOptional_x3f(v_attrsStx_1183_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v___f_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec(v_inst_1197_);
lean_dec(v_inst_1196_);
lean_dec_ref(v_inst_1195_);
lean_dec(v_inst_1194_);
lean_dec(v_inst_1193_);
lean_dec_ref(v_inst_1192_);
lean_dec_ref(v_inst_1191_);
lean_dec_ref(v_inst_1190_);
lean_dec_ref(v_inst_1189_);
lean_dec_ref(v_inst_1188_);
lean_dec_ref(v_inst_1187_);
lean_dec_ref(v_inst_1186_);
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1208_, 0, v___f_1206_);
v___x_1209_ = lean_mk_empty_array_with_capacity(v___x_1184_);
v___x_1210_ = lean_apply_2(v_toPure_1181_, lean_box(0), v___x_1209_);
v___x_1211_ = lean_apply_4(v_toBind_1185_, lean_box(0), lean_box(0), v___x_1210_, v___f_1208_);
return v___x_1211_;
}
else
{
lean_object* v_val_1212_; lean_object* v___f_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec(v_toPure_1181_);
v_val_1212_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_val_1212_);
lean_dec_ref(v___x_1207_);
v___f_1213_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1213_, 0, v___f_1206_);
v___x_1214_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_1186_, v_inst_1187_, v_inst_1188_, v_inst_1189_, v_inst_1190_, v_inst_1191_, v_inst_1192_, v_inst_1193_, v_inst_1194_, v_inst_1195_, v_inst_1196_, v_inst_1197_, v_val_1212_);
lean_dec(v_val_1212_);
v___x_1215_ = lean_apply_4(v_toBind_1185_, lean_box(0), lean_box(0), v___x_1214_, v___f_1213_);
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_stx_1219_ = _args[0];
lean_object* v___y_1220_ = _args[1];
lean_object* v___y_1221_ = _args[2];
lean_object* v___y_1222_ = _args[3];
lean_object* v_toPure_1223_ = _args[4];
lean_object* v_unsafeStx_1224_ = _args[5];
lean_object* v_attrsStx_1225_ = _args[6];
lean_object* v___x_1226_ = _args[7];
lean_object* v_toBind_1227_ = _args[8];
lean_object* v_inst_1228_ = _args[9];
lean_object* v_inst_1229_ = _args[10];
lean_object* v_inst_1230_ = _args[11];
lean_object* v_inst_1231_ = _args[12];
lean_object* v_inst_1232_ = _args[13];
lean_object* v_inst_1233_ = _args[14];
lean_object* v_inst_1234_ = _args[15];
lean_object* v_inst_1235_ = _args[16];
lean_object* v_inst_1236_ = _args[17];
lean_object* v_inst_1237_ = _args[18];
lean_object* v_inst_1238_ = _args[19];
lean_object* v_inst_1239_ = _args[20];
lean_object* v_protectedStx_1240_ = _args[21];
lean_object* v_visibility_1241_ = _args[22];
_start:
{
uint8_t v___y_512__boxed_1242_; uint8_t v___y_513__boxed_1243_; uint8_t v_visibility_boxed_1244_; lean_object* v_res_1245_; 
v___y_512__boxed_1242_ = lean_unbox(v___y_1221_);
v___y_513__boxed_1243_ = lean_unbox(v___y_1222_);
v_visibility_boxed_1244_ = lean_unbox(v_visibility_1241_);
v_res_1245_ = l_Lean_Elab_elabModifiers___redArg___lam__3(v_stx_1219_, v___y_1220_, v___y_512__boxed_1242_, v___y_513__boxed_1243_, v_toPure_1223_, v_unsafeStx_1224_, v_attrsStx_1225_, v___x_1226_, v_toBind_1227_, v_inst_1228_, v_inst_1229_, v_inst_1230_, v_inst_1231_, v_inst_1232_, v_inst_1233_, v_inst_1234_, v_inst_1235_, v_inst_1236_, v_inst_1237_, v_inst_1238_, v_inst_1239_, v_protectedStx_1240_, v_visibility_boxed_1244_);
lean_dec(v_protectedStx_1240_);
lean_dec(v___x_1226_);
lean_dec(v_attrsStx_1225_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2(lean_object* v_inst_1246_, lean_object* v_inst_1247_, lean_object* v_toBind_1248_, lean_object* v_stx_1249_, uint8_t v___y_1250_, uint8_t v___y_1251_, lean_object* v_toPure_1252_, lean_object* v_unsafeStx_1253_, lean_object* v_attrsStx_1254_, lean_object* v___x_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_protectedStx_1266_, lean_object* v_visibilityStx_1267_, lean_object* v_docCommentStx_1268_, lean_object* v___x_1269_, lean_object* v_____do__lift_1270_){
_start:
{
lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1277_; lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_Syntax_getOptional_x3f(v_docCommentStx_1268_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v___x_1292_; 
lean_dec_ref(v___x_1269_);
v___x_1292_ = lean_box(0);
v___y_1277_ = v___x_1292_;
goto v___jp_1276_;
}
else
{
lean_object* v_val_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1303_; 
v_val_1293_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1295_ = v___x_1291_;
v_isShared_1296_ = v_isSharedCheck_1303_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_val_1293_);
lean_dec(v___x_1291_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1303_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1297_ = l_Lean_doc_verso;
v___x_1298_ = l_Lean_Option_get___redArg(v___x_1269_, v_____do__lift_1270_, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v_val_1293_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1299_);
v___x_1301_ = v___x_1295_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
v___y_1277_ = v___x_1301_;
goto v___jp_1276_;
}
}
}
v___jp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = l_Lean_Elab_elabVisibility___redArg(v_inst_1246_, v_inst_1247_, v___y_1273_);
v___x_1275_ = lean_apply_4(v_toBind_1248_, lean_box(0), lean_box(0), v___x_1274_, v___y_1272_);
return v___x_1275_;
}
v___jp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___f_1280_; lean_object* v___x_1281_; 
v___x_1278_ = lean_box(v___y_1250_);
v___x_1279_ = lean_box(v___y_1251_);
lean_inc_ref(v_inst_1247_);
lean_inc_ref(v_inst_1246_);
lean_inc(v_toBind_1248_);
v___f_1280_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__3___boxed), 23, 22);
lean_closure_set(v___f_1280_, 0, v_stx_1249_);
lean_closure_set(v___f_1280_, 1, v___y_1277_);
lean_closure_set(v___f_1280_, 2, v___x_1278_);
lean_closure_set(v___f_1280_, 3, v___x_1279_);
lean_closure_set(v___f_1280_, 4, v_toPure_1252_);
lean_closure_set(v___f_1280_, 5, v_unsafeStx_1253_);
lean_closure_set(v___f_1280_, 6, v_attrsStx_1254_);
lean_closure_set(v___f_1280_, 7, v___x_1255_);
lean_closure_set(v___f_1280_, 8, v_toBind_1248_);
lean_closure_set(v___f_1280_, 9, v_inst_1246_);
lean_closure_set(v___f_1280_, 10, v_inst_1256_);
lean_closure_set(v___f_1280_, 11, v_inst_1257_);
lean_closure_set(v___f_1280_, 12, v_inst_1247_);
lean_closure_set(v___f_1280_, 13, v_inst_1258_);
lean_closure_set(v___f_1280_, 14, v_inst_1259_);
lean_closure_set(v___f_1280_, 15, v_inst_1260_);
lean_closure_set(v___f_1280_, 16, v_inst_1261_);
lean_closure_set(v___f_1280_, 17, v_inst_1262_);
lean_closure_set(v___f_1280_, 18, v_inst_1263_);
lean_closure_set(v___f_1280_, 19, v_inst_1264_);
lean_closure_set(v___f_1280_, 20, v_inst_1265_);
lean_closure_set(v___f_1280_, 21, v_protectedStx_1266_);
v___x_1281_ = l_Lean_Syntax_getOptional_x3f(v_visibilityStx_1267_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_box(0);
v___y_1272_ = v___f_1280_;
v___y_1273_ = v___x_1282_;
goto v___jp_1271_;
}
else
{
lean_object* v_val_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
v_val_1283_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1281_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_val_1283_);
lean_dec(v___x_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_val_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
v___y_1272_ = v___f_1280_;
v___y_1273_ = v___x_1288_;
goto v___jp_1271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_inst_1304_ = _args[0];
lean_object* v_inst_1305_ = _args[1];
lean_object* v_toBind_1306_ = _args[2];
lean_object* v_stx_1307_ = _args[3];
lean_object* v___y_1308_ = _args[4];
lean_object* v___y_1309_ = _args[5];
lean_object* v_toPure_1310_ = _args[6];
lean_object* v_unsafeStx_1311_ = _args[7];
lean_object* v_attrsStx_1312_ = _args[8];
lean_object* v___x_1313_ = _args[9];
lean_object* v_inst_1314_ = _args[10];
lean_object* v_inst_1315_ = _args[11];
lean_object* v_inst_1316_ = _args[12];
lean_object* v_inst_1317_ = _args[13];
lean_object* v_inst_1318_ = _args[14];
lean_object* v_inst_1319_ = _args[15];
lean_object* v_inst_1320_ = _args[16];
lean_object* v_inst_1321_ = _args[17];
lean_object* v_inst_1322_ = _args[18];
lean_object* v_inst_1323_ = _args[19];
lean_object* v_protectedStx_1324_ = _args[20];
lean_object* v_visibilityStx_1325_ = _args[21];
lean_object* v_docCommentStx_1326_ = _args[22];
lean_object* v___x_1327_ = _args[23];
lean_object* v_____do__lift_1328_ = _args[24];
_start:
{
uint8_t v___y_599__boxed_1329_; uint8_t v___y_600__boxed_1330_; lean_object* v_res_1331_; 
v___y_599__boxed_1329_ = lean_unbox(v___y_1308_);
v___y_600__boxed_1330_ = lean_unbox(v___y_1309_);
v_res_1331_ = l_Lean_Elab_elabModifiers___redArg___lam__2(v_inst_1304_, v_inst_1305_, v_toBind_1306_, v_stx_1307_, v___y_599__boxed_1329_, v___y_600__boxed_1330_, v_toPure_1310_, v_unsafeStx_1311_, v_attrsStx_1312_, v___x_1313_, v_inst_1314_, v_inst_1315_, v_inst_1316_, v_inst_1317_, v_inst_1318_, v_inst_1319_, v_inst_1320_, v_inst_1321_, v_inst_1322_, v_inst_1323_, v_protectedStx_1324_, v_visibilityStx_1325_, v_docCommentStx_1326_, v___x_1327_, v_____do__lift_1328_);
lean_dec_ref(v_____do__lift_1328_);
lean_dec(v_docCommentStx_1326_);
lean_dec(v_visibilityStx_1325_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg(lean_object* v_inst_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_stx_1354_){
_start:
{
lean_object* v___x_1355_; lean_object* v_toApplicative_1356_; lean_object* v_toBind_1357_; lean_object* v_toPure_1358_; lean_object* v___x_1359_; lean_object* v_docCommentStx_1360_; lean_object* v___x_1361_; lean_object* v_attrsStx_1362_; lean_object* v___x_1363_; lean_object* v_visibilityStx_1364_; lean_object* v___x_1365_; lean_object* v_protectedStx_1366_; lean_object* v___y_1368_; uint8_t v___y_1369_; uint8_t v___y_1370_; uint8_t v___y_1376_; lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1355_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1356_ = lean_ctor_get(v_inst_1342_, 0);
v_toBind_1357_ = lean_ctor_get(v_inst_1342_, 1);
lean_inc(v_toBind_1357_);
v_toPure_1358_ = lean_ctor_get(v_toApplicative_1356_, 1);
lean_inc(v_toPure_1358_);
v___x_1359_ = lean_unsigned_to_nat(0u);
v_docCommentStx_1360_ = l_Lean_Syntax_getArg(v_stx_1354_, v___x_1359_);
v___x_1361_ = lean_unsigned_to_nat(1u);
v_attrsStx_1362_ = l_Lean_Syntax_getArg(v_stx_1354_, v___x_1361_);
v___x_1363_ = lean_unsigned_to_nat(2u);
v_visibilityStx_1364_ = l_Lean_Syntax_getArg(v_stx_1354_, v___x_1363_);
v___x_1365_ = lean_unsigned_to_nat(3u);
v_protectedStx_1366_ = l_Lean_Syntax_getArg(v_stx_1354_, v___x_1365_);
v___x_1389_ = lean_unsigned_to_nat(4u);
v___x_1390_ = l_Lean_Syntax_getArg(v_stx_1354_, v___x_1389_);
v___x_1391_ = l_Lean_Syntax_isNone(v___x_1390_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1392_ = l_Lean_Syntax_getArg(v___x_1390_, v___x_1359_);
lean_dec(v___x_1390_);
v___x_1393_ = l_Lean_Syntax_getKind(v___x_1392_);
v___x_1394_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__1));
v___x_1395_ = lean_name_eq(v___x_1393_, v___x_1394_);
lean_dec(v___x_1393_);
if (v___x_1395_ == 0)
{
uint8_t v___x_1396_; 
v___x_1396_ = 2;
v___y_1376_ = v___x_1396_;
goto v___jp_1375_;
}
else
{
uint8_t v___x_1397_; 
v___x_1397_ = 1;
v___y_1376_ = v___x_1397_;
goto v___jp_1375_;
}
}
else
{
uint8_t v___x_1398_; 
lean_dec(v___x_1390_);
v___x_1398_ = 0;
v___y_1376_ = v___x_1398_;
goto v___jp_1375_;
}
v___jp_1367_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___f_1373_; lean_object* v___x_1374_; 
v___x_1371_ = lean_box(v___y_1369_);
v___x_1372_ = lean_box(v___y_1370_);
lean_inc(v_inst_1350_);
lean_inc(v_toBind_1357_);
v___f_1373_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__2___boxed), 25, 24);
lean_closure_set(v___f_1373_, 0, v_inst_1342_);
lean_closure_set(v___f_1373_, 1, v_inst_1345_);
lean_closure_set(v___f_1373_, 2, v_toBind_1357_);
lean_closure_set(v___f_1373_, 3, v_stx_1354_);
lean_closure_set(v___f_1373_, 4, v___x_1371_);
lean_closure_set(v___f_1373_, 5, v___x_1372_);
lean_closure_set(v___f_1373_, 6, v_toPure_1358_);
lean_closure_set(v___f_1373_, 7, v___y_1368_);
lean_closure_set(v___f_1373_, 8, v_attrsStx_1362_);
lean_closure_set(v___f_1373_, 9, v___x_1359_);
lean_closure_set(v___f_1373_, 10, v_inst_1343_);
lean_closure_set(v___f_1373_, 11, v_inst_1344_);
lean_closure_set(v___f_1373_, 12, v_inst_1347_);
lean_closure_set(v___f_1373_, 13, v_inst_1348_);
lean_closure_set(v___f_1373_, 14, v_inst_1349_);
lean_closure_set(v___f_1373_, 15, v_inst_1350_);
lean_closure_set(v___f_1373_, 16, v_inst_1351_);
lean_closure_set(v___f_1373_, 17, v_inst_1352_);
lean_closure_set(v___f_1373_, 18, v_inst_1353_);
lean_closure_set(v___f_1373_, 19, v_inst_1346_);
lean_closure_set(v___f_1373_, 20, v_protectedStx_1366_);
lean_closure_set(v___f_1373_, 21, v_visibilityStx_1364_);
lean_closure_set(v___f_1373_, 22, v_docCommentStx_1360_);
lean_closure_set(v___f_1373_, 23, v___x_1355_);
v___x_1374_ = lean_apply_4(v_toBind_1357_, lean_box(0), lean_box(0), v_inst_1350_, v___f_1373_);
return v___x_1374_;
}
v___jp_1375_:
{
lean_object* v___x_1377_; lean_object* v_unsafeStx_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1377_ = lean_unsigned_to_nat(5u);
v_unsafeStx_1378_ = l_Lean_Syntax_getArg(v_stx_1354_, v___x_1377_);
v___x_1379_ = lean_unsigned_to_nat(6u);
v___x_1380_ = l_Lean_Syntax_getArg(v_stx_1354_, v___x_1379_);
v___x_1381_ = l_Lean_Syntax_isNone(v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1382_ = l_Lean_Syntax_getArg(v___x_1380_, v___x_1359_);
lean_dec(v___x_1380_);
v___x_1383_ = l_Lean_Syntax_getKind(v___x_1382_);
v___x_1384_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__0));
v___x_1385_ = lean_name_eq(v___x_1383_, v___x_1384_);
lean_dec(v___x_1383_);
if (v___x_1385_ == 0)
{
uint8_t v___x_1386_; 
v___x_1386_ = 1;
v___y_1368_ = v_unsafeStx_1378_;
v___y_1369_ = v___y_1376_;
v___y_1370_ = v___x_1386_;
goto v___jp_1367_;
}
else
{
uint8_t v___x_1387_; 
v___x_1387_ = 0;
v___y_1368_ = v_unsafeStx_1378_;
v___y_1369_ = v___y_1376_;
v___y_1370_ = v___x_1387_;
goto v___jp_1367_;
}
}
else
{
uint8_t v___x_1388_; 
lean_dec(v___x_1380_);
v___x_1388_ = 2;
v___y_1368_ = v_unsafeStx_1378_;
v___y_1369_ = v___y_1376_;
v___y_1370_ = v___x_1388_;
goto v___jp_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object* v_m_1399_, lean_object* v_inst_1400_, lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v_inst_1405_, lean_object* v_inst_1406_, lean_object* v_inst_1407_, lean_object* v_inst_1408_, lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_inst_1411_, lean_object* v_stx_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_Elab_elabModifiers___redArg(v_inst_1400_, v_inst_1401_, v_inst_1402_, v_inst_1403_, v_inst_1404_, v_inst_1405_, v_inst_1406_, v_inst_1407_, v_inst_1408_, v_inst_1409_, v_inst_1410_, v_inst_1411_, v_stx_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__0(lean_object* v_toPure_1414_, lean_object* v_declName_1415_, lean_object* v_____r_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_apply_2(v_toPure_1414_, lean_box(0), v_declName_1415_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__1(lean_object* v_declName_1418_, lean_object* v_env_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_addProtected(v_env_1419_, v_declName_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2(lean_object* v_modifiers_1421_, lean_object* v_toPure_1422_, lean_object* v_declName_1423_, lean_object* v_modifyEnv_1424_, lean_object* v___f_1425_, lean_object* v_toBind_1426_, lean_object* v___f_1427_, lean_object* v_____r_1428_){
_start:
{
uint8_t v_isProtected_1429_; 
v_isProtected_1429_ = lean_ctor_get_uint8(v_modifiers_1421_, sizeof(void*)*3 + 1);
if (v_isProtected_1429_ == 0)
{
lean_object* v___x_1430_; 
lean_dec(v___f_1427_);
lean_dec(v_toBind_1426_);
lean_dec_ref(v___f_1425_);
lean_dec(v_modifyEnv_1424_);
v___x_1430_ = lean_apply_2(v_toPure_1422_, lean_box(0), v_declName_1423_);
return v___x_1430_;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec(v_declName_1423_);
lean_dec(v_toPure_1422_);
v___x_1431_ = lean_apply_1(v_modifyEnv_1424_, v___f_1425_);
v___x_1432_ = lean_apply_4(v_toBind_1426_, lean_box(0), lean_box(0), v___x_1431_, v___f_1427_);
return v___x_1432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2___boxed(lean_object* v_modifiers_1433_, lean_object* v_toPure_1434_, lean_object* v_declName_1435_, lean_object* v_modifyEnv_1436_, lean_object* v___f_1437_, lean_object* v_toBind_1438_, lean_object* v___f_1439_, lean_object* v_____r_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_Elab_applyVisibility___redArg___lam__2(v_modifiers_1433_, v_toPure_1434_, v_declName_1435_, v_modifyEnv_1436_, v___f_1437_, v_toBind_1438_, v___f_1439_, v_____r_1440_);
lean_dec_ref(v_modifiers_1433_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__3(lean_object* v_toPure_1442_, lean_object* v_modifiers_1443_, lean_object* v_modifyEnv_1444_, lean_object* v_toBind_1445_, lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_inst_1448_, lean_object* v_inst_1449_, lean_object* v_inst_1450_, lean_object* v_____r_1451_, lean_object* v_declName_1452_){
_start:
{
lean_object* v___f_1453_; lean_object* v___f_1454_; lean_object* v___f_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_inc_n(v_declName_1452_, 3);
lean_inc(v_toPure_1442_);
v___f_1453_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1453_, 0, v_toPure_1442_);
lean_closure_set(v___f_1453_, 1, v_declName_1452_);
v___f_1454_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1454_, 0, v_declName_1452_);
lean_inc(v_toBind_1445_);
v___f_1455_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1455_, 0, v_modifiers_1443_);
lean_closure_set(v___f_1455_, 1, v_toPure_1442_);
lean_closure_set(v___f_1455_, 2, v_declName_1452_);
lean_closure_set(v___f_1455_, 3, v_modifyEnv_1444_);
lean_closure_set(v___f_1455_, 4, v___f_1454_);
lean_closure_set(v___f_1455_, 5, v_toBind_1445_);
lean_closure_set(v___f_1455_, 6, v___f_1453_);
v___x_1456_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(v_inst_1446_, v_inst_1447_, v_inst_1448_, v_inst_1449_, v_inst_1450_, v_declName_1452_);
v___x_1457_ = lean_apply_4(v_toBind_1445_, lean_box(0), lean_box(0), v___x_1456_, v___f_1455_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4(lean_object* v_declName_1458_, lean_object* v___f_1459_, lean_object* v_____do__lift_1460_){
_start:
{
lean_object* v_declName_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_declName_1461_ = l_Lean_mkPrivateName(v_____do__lift_1460_, v_declName_1458_);
v___x_1462_ = lean_box(0);
v___x_1463_ = lean_apply_2(v___f_1459_, v___x_1462_, v_declName_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4___boxed(lean_object* v_declName_1464_, lean_object* v___f_1465_, lean_object* v_____do__lift_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Elab_applyVisibility___redArg___lam__4(v_declName_1464_, v___f_1465_, v_____do__lift_1466_);
lean_dec_ref(v_____do__lift_1466_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5(lean_object* v_modifiers_1468_, lean_object* v_toBind_1469_, lean_object* v_getEnv_1470_, lean_object* v___f_1471_, lean_object* v___f_1472_, lean_object* v_declName_1473_, lean_object* v_____do__lift_1474_){
_start:
{
uint8_t v_visibility_1475_; uint8_t v___x_1476_; 
v_visibility_1475_ = lean_ctor_get_uint8(v_modifiers_1468_, sizeof(void*)*3);
v___x_1476_ = l_Lean_Elab_Visibility_isInferredPublic(v_____do__lift_1474_, v_visibility_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_dec(v_declName_1473_);
lean_dec(v___f_1472_);
v___x_1477_ = lean_apply_4(v_toBind_1469_, lean_box(0), lean_box(0), v_getEnv_1470_, v___f_1471_);
return v___x_1477_;
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec(v___f_1471_);
lean_dec(v_getEnv_1470_);
lean_dec(v_toBind_1469_);
v___x_1478_ = lean_box(0);
v___x_1479_ = lean_apply_2(v___f_1472_, v___x_1478_, v_declName_1473_);
return v___x_1479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5___boxed(lean_object* v_modifiers_1480_, lean_object* v_toBind_1481_, lean_object* v_getEnv_1482_, lean_object* v___f_1483_, lean_object* v___f_1484_, lean_object* v_declName_1485_, lean_object* v_____do__lift_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_Elab_applyVisibility___redArg___lam__5(v_modifiers_1480_, v_toBind_1481_, v_getEnv_1482_, v___f_1483_, v___f_1484_, v_declName_1485_, v_____do__lift_1486_);
lean_dec_ref(v_____do__lift_1486_);
lean_dec_ref(v_modifiers_1480_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg(lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_inst_1490_, lean_object* v_inst_1491_, lean_object* v_inst_1492_, lean_object* v_modifiers_1493_, lean_object* v_declName_1494_){
_start:
{
lean_object* v_toApplicative_1495_; lean_object* v_toBind_1496_; lean_object* v_getEnv_1497_; lean_object* v_modifyEnv_1498_; lean_object* v_toPure_1499_; lean_object* v___f_1500_; lean_object* v___f_1501_; lean_object* v___f_1502_; lean_object* v___x_1503_; 
v_toApplicative_1495_ = lean_ctor_get(v_inst_1488_, 0);
v_toBind_1496_ = lean_ctor_get(v_inst_1488_, 1);
lean_inc_n(v_toBind_1496_, 3);
v_getEnv_1497_ = lean_ctor_get(v_inst_1489_, 0);
lean_inc_n(v_getEnv_1497_, 2);
v_modifyEnv_1498_ = lean_ctor_get(v_inst_1489_, 1);
lean_inc(v_modifyEnv_1498_);
v_toPure_1499_ = lean_ctor_get(v_toApplicative_1495_, 1);
lean_inc(v_toPure_1499_);
lean_inc_ref(v_modifiers_1493_);
v___f_1500_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__3), 11, 9);
lean_closure_set(v___f_1500_, 0, v_toPure_1499_);
lean_closure_set(v___f_1500_, 1, v_modifiers_1493_);
lean_closure_set(v___f_1500_, 2, v_modifyEnv_1498_);
lean_closure_set(v___f_1500_, 3, v_toBind_1496_);
lean_closure_set(v___f_1500_, 4, v_inst_1488_);
lean_closure_set(v___f_1500_, 5, v_inst_1489_);
lean_closure_set(v___f_1500_, 6, v_inst_1490_);
lean_closure_set(v___f_1500_, 7, v_inst_1491_);
lean_closure_set(v___f_1500_, 8, v_inst_1492_);
lean_inc_ref(v___f_1500_);
lean_inc(v_declName_1494_);
v___f_1501_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_1501_, 0, v_declName_1494_);
lean_closure_set(v___f_1501_, 1, v___f_1500_);
v___f_1502_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1502_, 0, v_modifiers_1493_);
lean_closure_set(v___f_1502_, 1, v_toBind_1496_);
lean_closure_set(v___f_1502_, 2, v_getEnv_1497_);
lean_closure_set(v___f_1502_, 3, v___f_1501_);
lean_closure_set(v___f_1502_, 4, v___f_1500_);
lean_closure_set(v___f_1502_, 5, v_declName_1494_);
v___x_1503_ = lean_apply_4(v_toBind_1496_, lean_box(0), lean_box(0), v_getEnv_1497_, v___f_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility(lean_object* v_m_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_modifiers_1510_, lean_object* v_declName_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1505_, v_inst_1506_, v_inst_1507_, v_inst_1508_, v_inst_1509_, v_modifiers_1510_, v_declName_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0(lean_object* v_toPure_1513_, lean_object* v_____s_1514_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_box(0);
v___x_1516_ = lean_apply_2(v_toPure_1513_, lean_box(0), v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1(lean_object* v___x_1517_, lean_object* v_toPure_1518_, lean_object* v_r_1519_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1517_);
v___x_1521_ = lean_apply_2(v_toPure_1518_, lean_box(0), v___x_1520_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0));
v___x_1524_ = l_Lean_stringToMessageData(v___x_1523_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2));
v___x_1527_ = l_Lean_stringToMessageData(v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4));
v___x_1530_ = l_Lean_stringToMessageData(v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2(lean_object* v_pre_1531_, lean_object* v_declName_1532_, lean_object* v___x_1533_, lean_object* v_toPure_1534_, lean_object* v_inst_1535_, lean_object* v_inst_1536_, lean_object* v_toBind_1537_, lean_object* v___f_1538_, lean_object* v_a_1539_, lean_object* v_x_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1542_; uint8_t v___x_1543_; 
lean_inc(v_a_1539_);
lean_inc(v_pre_1531_);
v___x_1542_ = l_Lean_Name_append(v_pre_1531_, v_a_1539_);
v___x_1543_ = lean_name_eq(v___x_1542_, v_declName_1532_);
lean_dec(v___x_1542_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec(v_a_1539_);
lean_dec(v___f_1538_);
lean_dec(v_toBind_1537_);
lean_dec_ref(v_inst_1536_);
lean_dec_ref(v_inst_1535_);
lean_dec(v_declName_1532_);
lean_dec(v_pre_1531_);
v___x_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1533_);
v___x_1545_ = lean_apply_2(v_toPure_1534_, lean_box(0), v___x_1544_);
return v___x_1545_;
}
else
{
lean_object* v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec(v_toPure_1534_);
v___x_1546_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1547_ = 0;
v___x_1548_ = l_Lean_MessageData_ofConstName(v_declName_1532_, v___x_1547_);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1546_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = l_Lean_MessageData_ofName(v_pre_1531_);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = l_Lean_MessageData_ofName(v_a_1539_);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = l_Lean_throwError___redArg(v_inst_1535_, v_inst_1536_, v___x_1559_);
v___x_1561_ = lean_apply_4(v_toBind_1537_, lean_box(0), lean_box(0), v___x_1560_, v___f_1538_);
return v___x_1561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(lean_object* v_pre_1562_, uint8_t v___x_1563_, lean_object* v_toPure_1564_, lean_object* v_declName_1565_, lean_object* v_inst_1566_, lean_object* v_inst_1567_, lean_object* v_toBind_1568_, lean_object* v___f_1569_, lean_object* v_____do__lift_1570_){
_start:
{
lean_object* v_fieldNames_1571_; lean_object* v___x_1572_; lean_object* v___f_1573_; lean_object* v___f_1574_; size_t v_sz_1575_; size_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_inc(v_pre_1562_);
v_fieldNames_1571_ = l_Lean_getStructureFieldsFlattened(v_____do__lift_1570_, v_pre_1562_, v___x_1563_);
v___x_1572_ = lean_box(0);
lean_inc(v_toPure_1564_);
v___f_1573_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1573_, 0, v___x_1572_);
lean_closure_set(v___f_1573_, 1, v_toPure_1564_);
lean_inc(v_toBind_1568_);
lean_inc_ref(v_inst_1566_);
v___f_1574_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2), 11, 8);
lean_closure_set(v___f_1574_, 0, v_pre_1562_);
lean_closure_set(v___f_1574_, 1, v_declName_1565_);
lean_closure_set(v___f_1574_, 2, v___x_1572_);
lean_closure_set(v___f_1574_, 3, v_toPure_1564_);
lean_closure_set(v___f_1574_, 4, v_inst_1566_);
lean_closure_set(v___f_1574_, 5, v_inst_1567_);
lean_closure_set(v___f_1574_, 6, v_toBind_1568_);
lean_closure_set(v___f_1574_, 7, v___f_1573_);
v_sz_1575_ = lean_array_size(v_fieldNames_1571_);
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1566_, v_fieldNames_1571_, v___f_1574_, v_sz_1575_, v___x_1576_, v___x_1572_);
v___x_1578_ = lean_apply_4(v_toBind_1568_, lean_box(0), lean_box(0), v___x_1577_, v___f_1569_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed(lean_object* v_pre_1579_, lean_object* v___x_1580_, lean_object* v_toPure_1581_, lean_object* v_declName_1582_, lean_object* v_inst_1583_, lean_object* v_inst_1584_, lean_object* v_toBind_1585_, lean_object* v___f_1586_, lean_object* v_____do__lift_1587_){
_start:
{
uint8_t v___x_671__boxed_1588_; lean_object* v_res_1589_; 
v___x_671__boxed_1588_ = lean_unbox(v___x_1580_);
v_res_1589_ = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(v_pre_1579_, v___x_671__boxed_1588_, v_toPure_1581_, v_declName_1582_, v_inst_1583_, v_inst_1584_, v_toBind_1585_, v___f_1586_, v_____do__lift_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4(lean_object* v_pre_1590_, lean_object* v_toPure_1591_, lean_object* v_declName_1592_, lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_toBind_1595_, lean_object* v___f_1596_, lean_object* v_getEnv_1597_, lean_object* v_____do__lift_1598_){
_start:
{
uint8_t v___x_1599_; 
lean_inc(v_pre_1590_);
v___x_1599_ = l_Lean_isStructure(v_____do__lift_1598_, v_pre_1590_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec(v_getEnv_1597_);
lean_dec(v___f_1596_);
lean_dec(v_toBind_1595_);
lean_dec_ref(v_inst_1594_);
lean_dec_ref(v_inst_1593_);
lean_dec(v_declName_1592_);
lean_dec(v_pre_1590_);
v___x_1600_ = lean_box(0);
v___x_1601_ = lean_apply_2(v_toPure_1591_, lean_box(0), v___x_1600_);
return v___x_1601_;
}
else
{
lean_object* v___x_1602_; lean_object* v___f_1603_; lean_object* v___x_1604_; 
v___x_1602_ = lean_box(v___x_1599_);
lean_inc(v_toBind_1595_);
v___f_1603_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1603_, 0, v_pre_1590_);
lean_closure_set(v___f_1603_, 1, v___x_1602_);
lean_closure_set(v___f_1603_, 2, v_toPure_1591_);
lean_closure_set(v___f_1603_, 3, v_declName_1592_);
lean_closure_set(v___f_1603_, 4, v_inst_1593_);
lean_closure_set(v___f_1603_, 5, v_inst_1594_);
lean_closure_set(v___f_1603_, 6, v_toBind_1595_);
lean_closure_set(v___f_1603_, 7, v___f_1596_);
v___x_1604_ = lean_apply_4(v_toBind_1595_, lean_box(0), lean_box(0), v_getEnv_1597_, v___f_1603_);
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg(lean_object* v_inst_1605_, lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v_declName_1608_){
_start:
{
if (lean_obj_tag(v_declName_1608_) == 1)
{
lean_object* v_toApplicative_1609_; lean_object* v_toBind_1610_; lean_object* v_toPure_1611_; lean_object* v_pre_1612_; lean_object* v_getEnv_1613_; lean_object* v___f_1614_; lean_object* v___f_1615_; lean_object* v___x_1616_; 
v_toApplicative_1609_ = lean_ctor_get(v_inst_1605_, 0);
v_toBind_1610_ = lean_ctor_get(v_inst_1605_, 1);
lean_inc_n(v_toBind_1610_, 2);
v_toPure_1611_ = lean_ctor_get(v_toApplicative_1609_, 1);
lean_inc_n(v_toPure_1611_, 2);
v_pre_1612_ = lean_ctor_get(v_declName_1608_, 0);
lean_inc(v_pre_1612_);
v_getEnv_1613_ = lean_ctor_get(v_inst_1606_, 0);
lean_inc_n(v_getEnv_1613_, 2);
lean_dec_ref(v_inst_1606_);
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1614_, 0, v_toPure_1611_);
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1615_, 0, v_pre_1612_);
lean_closure_set(v___f_1615_, 1, v_toPure_1611_);
lean_closure_set(v___f_1615_, 2, v_declName_1608_);
lean_closure_set(v___f_1615_, 3, v_inst_1605_);
lean_closure_set(v___f_1615_, 4, v_inst_1607_);
lean_closure_set(v___f_1615_, 5, v_toBind_1610_);
lean_closure_set(v___f_1615_, 6, v___f_1614_);
lean_closure_set(v___f_1615_, 7, v_getEnv_1613_);
v___x_1616_ = lean_apply_4(v_toBind_1610_, lean_box(0), lean_box(0), v_getEnv_1613_, v___f_1615_);
return v___x_1616_;
}
else
{
lean_object* v_toApplicative_1617_; lean_object* v_toPure_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_toApplicative_1617_ = lean_ctor_get(v_inst_1605_, 0);
lean_inc_ref(v_toApplicative_1617_);
lean_dec(v_declName_1608_);
lean_dec_ref(v_inst_1607_);
lean_dec_ref(v_inst_1606_);
lean_dec_ref(v_inst_1605_);
v_toPure_1618_ = lean_ctor_get(v_toApplicative_1617_, 1);
lean_inc(v_toPure_1618_);
lean_dec_ref(v_toApplicative_1617_);
v___x_1619_ = lean_box(0);
v___x_1620_ = lean_apply_2(v_toPure_1618_, lean_box(0), v___x_1619_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField(lean_object* v_m_1621_, lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_declName_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1622_, v_inst_1623_, v_inst_1624_, v_declName_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__0(lean_object* v_toApplicative_1627_, lean_object* v_declName_1628_, lean_object* v_shortName_1629_, lean_object* v_____r_1630_){
_start:
{
lean_object* v_toPure_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_toPure_1631_ = lean_ctor_get(v_toApplicative_1627_, 1);
lean_inc(v_toPure_1631_);
lean_dec_ref(v_toApplicative_1627_);
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v_declName_1628_);
lean_ctor_set(v___x_1632_, 1, v_shortName_1629_);
v___x_1633_ = lean_apply_2(v_toPure_1631_, lean_box(0), v___x_1632_);
return v___x_1633_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0));
v___x_1636_ = l_Lean_stringToMessageData(v___x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2(lean_object* v_modifiers_1637_, lean_object* v_toApplicative_1638_, lean_object* v_shortName_1639_, lean_object* v_currNamespace_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_toBind_1643_, lean_object* v_declName_1644_){
_start:
{
uint8_t v_isProtected_1645_; 
v_isProtected_1645_ = lean_ctor_get_uint8(v_modifiers_1637_, sizeof(void*)*3 + 1);
if (v_isProtected_1645_ == 0)
{
lean_object* v_toPure_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec(v_toBind_1643_);
lean_dec_ref(v_inst_1642_);
lean_dec_ref(v_inst_1641_);
lean_dec(v_currNamespace_1640_);
v_toPure_1646_ = lean_ctor_get(v_toApplicative_1638_, 1);
lean_inc(v_toPure_1646_);
lean_dec_ref(v_toApplicative_1638_);
v___x_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1647_, 0, v_declName_1644_);
lean_ctor_set(v___x_1647_, 1, v_shortName_1639_);
v___x_1648_ = lean_apply_2(v_toPure_1646_, lean_box(0), v___x_1647_);
return v___x_1648_;
}
else
{
if (lean_obj_tag(v_currNamespace_1640_) == 1)
{
lean_object* v_str_1649_; lean_object* v_toPure_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec(v_toBind_1643_);
lean_dec_ref(v_inst_1642_);
lean_dec_ref(v_inst_1641_);
v_str_1649_ = lean_ctor_get(v_currNamespace_1640_, 1);
lean_inc_ref(v_str_1649_);
lean_dec_ref(v_currNamespace_1640_);
v_toPure_1650_ = lean_ctor_get(v_toApplicative_1638_, 1);
lean_inc(v_toPure_1650_);
lean_dec_ref(v_toApplicative_1638_);
v___x_1651_ = lean_box(0);
v___x_1652_ = l_Lean_Name_str___override(v___x_1651_, v_str_1649_);
v___x_1653_ = l_Lean_Name_append(v___x_1652_, v_shortName_1639_);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_declName_1644_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = lean_apply_2(v_toPure_1650_, lean_box(0), v___x_1654_);
return v___x_1655_;
}
else
{
lean_object* v___f_1656_; uint8_t v___x_1657_; 
lean_dec(v_currNamespace_1640_);
lean_inc(v_shortName_1639_);
lean_inc(v_declName_1644_);
lean_inc_ref(v_toApplicative_1638_);
v___f_1656_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1656_, 0, v_toApplicative_1638_);
lean_closure_set(v___f_1656_, 1, v_declName_1644_);
lean_closure_set(v___f_1656_, 2, v_shortName_1639_);
v___x_1657_ = l_Lean_Name_isAtomic(v_shortName_1639_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec_ref(v___f_1656_);
lean_dec(v_toBind_1643_);
lean_dec_ref(v_inst_1642_);
lean_dec_ref(v_inst_1641_);
v___x_1658_ = lean_box(0);
v___x_1659_ = l_Lean_Elab_mkDeclName___redArg___lam__0(v_toApplicative_1638_, v_declName_1644_, v_shortName_1639_, v___x_1658_);
return v___x_1659_;
}
else
{
lean_object* v___f_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_dec(v_declName_1644_);
lean_dec(v_shortName_1639_);
lean_dec_ref(v_toApplicative_1638_);
v___f_1660_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1660_, 0, v___f_1656_);
v___x_1661_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_1662_ = l_Lean_throwError___redArg(v_inst_1641_, v_inst_1642_, v___x_1661_);
v___x_1663_ = lean_apply_4(v_toBind_1643_, lean_box(0), lean_box(0), v___x_1662_, v___f_1660_);
return v___x_1663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2___boxed(lean_object* v_modifiers_1664_, lean_object* v_toApplicative_1665_, lean_object* v_shortName_1666_, lean_object* v_currNamespace_1667_, lean_object* v_inst_1668_, lean_object* v_inst_1669_, lean_object* v_toBind_1670_, lean_object* v_declName_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Elab_mkDeclName___redArg___lam__2(v_modifiers_1664_, v_toApplicative_1665_, v_shortName_1666_, v_currNamespace_1667_, v_inst_1668_, v_inst_1669_, v_toBind_1670_, v_declName_1671_);
lean_dec_ref(v_modifiers_1664_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__1(lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_modifiers_1678_, lean_object* v___y_1679_, lean_object* v_toBind_1680_, lean_object* v___f_1681_, lean_object* v_____r_1682_){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1673_, v_inst_1674_, v_inst_1675_, v_inst_1676_, v_inst_1677_, v_modifiers_1678_, v___y_1679_);
v___x_1684_ = lean_apply_4(v_toBind_1680_, lean_box(0), lean_box(0), v___x_1683_, v___f_1681_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3(lean_object* v_modifiers_1685_, lean_object* v_toApplicative_1686_, lean_object* v_inst_1687_, lean_object* v_inst_1688_, lean_object* v_toBind_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v___y_1693_, lean_object* v_____r_1694_, lean_object* v_shortName_1695_, lean_object* v_currNamespace_1696_){
_start:
{
lean_object* v___f_1697_; lean_object* v___f_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_inc_n(v_toBind_1689_, 2);
lean_inc_ref_n(v_inst_1688_, 2);
lean_inc_ref_n(v_inst_1687_, 2);
lean_inc_ref(v_modifiers_1685_);
v___f_1697_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1697_, 0, v_modifiers_1685_);
lean_closure_set(v___f_1697_, 1, v_toApplicative_1686_);
lean_closure_set(v___f_1697_, 2, v_shortName_1695_);
lean_closure_set(v___f_1697_, 3, v_currNamespace_1696_);
lean_closure_set(v___f_1697_, 4, v_inst_1687_);
lean_closure_set(v___f_1697_, 5, v_inst_1688_);
lean_closure_set(v___f_1697_, 6, v_toBind_1689_);
lean_inc(v___y_1693_);
lean_inc_ref(v_inst_1690_);
v___f_1698_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1698_, 0, v_inst_1687_);
lean_closure_set(v___f_1698_, 1, v_inst_1690_);
lean_closure_set(v___f_1698_, 2, v_inst_1688_);
lean_closure_set(v___f_1698_, 3, v_inst_1691_);
lean_closure_set(v___f_1698_, 4, v_inst_1692_);
lean_closure_set(v___f_1698_, 5, v_modifiers_1685_);
lean_closure_set(v___f_1698_, 6, v___y_1693_);
lean_closure_set(v___f_1698_, 7, v_toBind_1689_);
lean_closure_set(v___f_1698_, 8, v___f_1697_);
v___x_1699_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1687_, v_inst_1690_, v_inst_1688_, v___y_1693_);
v___x_1700_ = lean_apply_4(v_toBind_1689_, lean_box(0), lean_box(0), v___x_1699_, v___f_1698_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__4(lean_object* v___f_1701_, lean_object* v_shortName_1702_, lean_object* v_currNamespace_1703_, lean_object* v_____r_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_apply_3(v___f_1701_, v_____r_1704_, v_shortName_1702_, v_currNamespace_1703_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5(lean_object* v_modifiers_1706_, lean_object* v_toApplicative_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_toBind_1710_, lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_inst_1713_, uint8_t v_isRootName_1714_, lean_object* v_shortName_1715_, lean_object* v_currNamespace_1716_, lean_object* v_name_1717_, lean_object* v___x_1718_, lean_object* v_imported_1719_, lean_object* v_ctx_1720_, lean_object* v_scopes_1721_, lean_object* v_____r_1722_){
_start:
{
lean_object* v___y_1724_; 
if (v_isRootName_1714_ == 0)
{
lean_object* v___x_1743_; 
lean_dec(v_scopes_1721_);
lean_dec(v_ctx_1720_);
lean_dec(v_imported_1719_);
lean_inc(v_shortName_1715_);
lean_inc(v_currNamespace_1716_);
v___x_1743_ = l_Lean_Name_append(v_currNamespace_1716_, v_shortName_1715_);
v___y_1724_ = v___x_1743_;
goto v___jp_1723_;
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1744_ = lean_box(0);
lean_inc(v_name_1717_);
v___x_1745_ = l_Lean_Name_replacePrefix(v_name_1717_, v___x_1718_, v___x_1744_);
v___x_1746_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
lean_ctor_set(v___x_1746_, 1, v_imported_1719_);
lean_ctor_set(v___x_1746_, 2, v_ctx_1720_);
lean_ctor_set(v___x_1746_, 3, v_scopes_1721_);
v___x_1747_ = l_Lean_MacroScopesView_review(v___x_1746_);
v___y_1724_ = v___x_1747_;
goto v___jp_1723_;
}
v___jp_1723_:
{
lean_object* v___f_1725_; 
lean_inc(v___y_1724_);
lean_inc_ref(v_inst_1713_);
lean_inc(v_inst_1712_);
lean_inc_ref(v_inst_1711_);
lean_inc(v_toBind_1710_);
lean_inc_ref(v_inst_1709_);
lean_inc_ref(v_inst_1708_);
lean_inc_ref(v_toApplicative_1707_);
lean_inc_ref(v_modifiers_1706_);
v___f_1725_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__3), 12, 9);
lean_closure_set(v___f_1725_, 0, v_modifiers_1706_);
lean_closure_set(v___f_1725_, 1, v_toApplicative_1707_);
lean_closure_set(v___f_1725_, 2, v_inst_1708_);
lean_closure_set(v___f_1725_, 3, v_inst_1709_);
lean_closure_set(v___f_1725_, 4, v_toBind_1710_);
lean_closure_set(v___f_1725_, 5, v_inst_1711_);
lean_closure_set(v___f_1725_, 6, v_inst_1712_);
lean_closure_set(v___f_1725_, 7, v_inst_1713_);
lean_closure_set(v___f_1725_, 8, v___y_1724_);
if (v_isRootName_1714_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec_ref(v___f_1725_);
lean_dec(v_name_1717_);
v___x_1726_ = lean_box(0);
v___x_1727_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1706_, v_toApplicative_1707_, v_inst_1708_, v_inst_1709_, v_toBind_1710_, v_inst_1711_, v_inst_1712_, v_inst_1713_, v___y_1724_, v___x_1726_, v_shortName_1715_, v_currNamespace_1716_);
return v___x_1727_;
}
else
{
if (lean_obj_tag(v_name_1717_) == 1)
{
lean_object* v_pre_1728_; lean_object* v_str_1729_; lean_object* v___x_1730_; lean_object* v_shortName_1731_; lean_object* v_currNamespace_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_dec_ref(v___f_1725_);
lean_dec(v_currNamespace_1716_);
lean_dec(v_shortName_1715_);
v_pre_1728_ = lean_ctor_get(v_name_1717_, 0);
lean_inc(v_pre_1728_);
v_str_1729_ = lean_ctor_get(v_name_1717_, 1);
lean_inc_ref(v_str_1729_);
lean_dec_ref(v_name_1717_);
v___x_1730_ = lean_box(0);
v_shortName_1731_ = l_Lean_Name_str___override(v___x_1730_, v_str_1729_);
v_currNamespace_1732_ = l_Lean_Name_replacePrefix(v_pre_1728_, v___x_1718_, v___x_1730_);
v___x_1733_ = lean_box(0);
v___x_1734_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1706_, v_toApplicative_1707_, v_inst_1708_, v_inst_1709_, v_toBind_1710_, v_inst_1711_, v_inst_1712_, v_inst_1713_, v___y_1724_, v___x_1733_, v_shortName_1731_, v_currNamespace_1732_);
return v___x_1734_;
}
else
{
lean_object* v___f_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_dec(v___y_1724_);
lean_dec_ref(v_inst_1713_);
lean_dec(v_inst_1712_);
lean_dec_ref(v_inst_1711_);
lean_dec_ref(v_toApplicative_1707_);
lean_dec_ref(v_modifiers_1706_);
v___f_1735_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__4), 4, 3);
lean_closure_set(v___f_1735_, 0, v___f_1725_);
lean_closure_set(v___f_1735_, 1, v_shortName_1715_);
lean_closure_set(v___f_1735_, 2, v_currNamespace_1716_);
v___x_1736_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1737_ = l_Lean_MessageData_ofName(v_name_1717_);
v___x_1738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1738_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = l_Lean_throwError___redArg(v_inst_1708_, v_inst_1709_, v___x_1740_);
v___x_1742_ = lean_apply_4(v_toBind_1710_, lean_box(0), lean_box(0), v___x_1741_, v___f_1735_);
return v___x_1742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_modifiers_1748_ = _args[0];
lean_object* v_toApplicative_1749_ = _args[1];
lean_object* v_inst_1750_ = _args[2];
lean_object* v_inst_1751_ = _args[3];
lean_object* v_toBind_1752_ = _args[4];
lean_object* v_inst_1753_ = _args[5];
lean_object* v_inst_1754_ = _args[6];
lean_object* v_inst_1755_ = _args[7];
lean_object* v_isRootName_1756_ = _args[8];
lean_object* v_shortName_1757_ = _args[9];
lean_object* v_currNamespace_1758_ = _args[10];
lean_object* v_name_1759_ = _args[11];
lean_object* v___x_1760_ = _args[12];
lean_object* v_imported_1761_ = _args[13];
lean_object* v_ctx_1762_ = _args[14];
lean_object* v_scopes_1763_ = _args[15];
lean_object* v_____r_1764_ = _args[16];
_start:
{
uint8_t v_isRootName_boxed_1765_; lean_object* v_res_1766_; 
v_isRootName_boxed_1765_ = lean_unbox(v_isRootName_1756_);
v_res_1766_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1748_, v_toApplicative_1749_, v_inst_1750_, v_inst_1751_, v_toBind_1752_, v_inst_1753_, v_inst_1754_, v_inst_1755_, v_isRootName_boxed_1765_, v_shortName_1757_, v_currNamespace_1758_, v_name_1759_, v___x_1760_, v_imported_1761_, v_ctx_1762_, v_scopes_1763_, v_____r_1764_);
lean_dec(v___x_1760_);
return v_res_1766_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___closed__3(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__2));
v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg(lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_inst_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_currNamespace_1778_, lean_object* v_modifiers_1779_, lean_object* v_shortName_1780_){
_start:
{
lean_object* v_view_1781_; lean_object* v_name_1782_; lean_object* v_imported_1783_; lean_object* v_ctx_1784_; lean_object* v_scopes_1785_; lean_object* v_toApplicative_1786_; lean_object* v_toBind_1787_; lean_object* v___x_1788_; uint8_t v_isRootName_1789_; lean_object* v___x_1790_; lean_object* v___f_1791_; uint8_t v___x_1792_; 
lean_inc_n(v_shortName_1780_, 2);
v_view_1781_ = l_Lean_extractMacroScopes(v_shortName_1780_);
v_name_1782_ = lean_ctor_get(v_view_1781_, 0);
lean_inc_n(v_name_1782_, 2);
v_imported_1783_ = lean_ctor_get(v_view_1781_, 1);
lean_inc_n(v_imported_1783_, 2);
v_ctx_1784_ = lean_ctor_get(v_view_1781_, 2);
lean_inc_n(v_ctx_1784_, 2);
v_scopes_1785_ = lean_ctor_get(v_view_1781_, 3);
lean_inc_n(v_scopes_1785_, 2);
lean_dec_ref(v_view_1781_);
v_toApplicative_1786_ = lean_ctor_get(v_inst_1773_, 0);
v_toBind_1787_ = lean_ctor_get(v_inst_1773_, 1);
lean_inc_n(v_toBind_1787_, 2);
v___x_1788_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_1789_ = l_Lean_Name_isPrefixOf(v___x_1788_, v_name_1782_);
v___x_1790_ = lean_box(v_isRootName_1789_);
lean_inc(v_currNamespace_1778_);
lean_inc_ref(v_inst_1777_);
lean_inc(v_inst_1776_);
lean_inc_ref(v_inst_1774_);
lean_inc_ref(v_inst_1775_);
lean_inc_ref(v_inst_1773_);
lean_inc_ref(v_toApplicative_1786_);
lean_inc_ref(v_modifiers_1779_);
v___f_1791_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1791_, 0, v_modifiers_1779_);
lean_closure_set(v___f_1791_, 1, v_toApplicative_1786_);
lean_closure_set(v___f_1791_, 2, v_inst_1773_);
lean_closure_set(v___f_1791_, 3, v_inst_1775_);
lean_closure_set(v___f_1791_, 4, v_toBind_1787_);
lean_closure_set(v___f_1791_, 5, v_inst_1774_);
lean_closure_set(v___f_1791_, 6, v_inst_1776_);
lean_closure_set(v___f_1791_, 7, v_inst_1777_);
lean_closure_set(v___f_1791_, 8, v___x_1790_);
lean_closure_set(v___f_1791_, 9, v_shortName_1780_);
lean_closure_set(v___f_1791_, 10, v_currNamespace_1778_);
lean_closure_set(v___f_1791_, 11, v_name_1782_);
lean_closure_set(v___f_1791_, 12, v___x_1788_);
lean_closure_set(v___f_1791_, 13, v_imported_1783_);
lean_closure_set(v___f_1791_, 14, v_ctx_1784_);
lean_closure_set(v___f_1791_, 15, v_scopes_1785_);
v___x_1792_ = lean_name_eq(v_name_1782_, v___x_1788_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_inc_ref(v_toApplicative_1786_);
lean_dec_ref(v___f_1791_);
v___x_1793_ = lean_box(0);
v___x_1794_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1779_, v_toApplicative_1786_, v_inst_1773_, v_inst_1775_, v_toBind_1787_, v_inst_1774_, v_inst_1776_, v_inst_1777_, v_isRootName_1789_, v_shortName_1780_, v_currNamespace_1778_, v_name_1782_, v___x_1788_, v_imported_1783_, v_ctx_1784_, v_scopes_1785_, v___x_1793_);
return v___x_1794_;
}
else
{
lean_object* v___f_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_dec(v_scopes_1785_);
lean_dec(v_ctx_1784_);
lean_dec(v_imported_1783_);
lean_dec(v_name_1782_);
lean_dec(v_shortName_1780_);
lean_dec_ref(v_modifiers_1779_);
lean_dec(v_currNamespace_1778_);
lean_dec_ref(v_inst_1777_);
lean_dec(v_inst_1776_);
lean_dec_ref(v_inst_1774_);
v___f_1795_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1795_, 0, v___f_1791_);
v___x_1796_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_1797_ = l_Lean_throwError___redArg(v_inst_1773_, v_inst_1775_, v___x_1796_);
v___x_1798_ = lean_apply_4(v_toBind_1787_, lean_box(0), lean_box(0), v___x_1797_, v___f_1795_);
return v___x_1798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName(lean_object* v_m_1799_, lean_object* v_inst_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_inst_1804_, lean_object* v_currNamespace_1805_, lean_object* v_modifiers_1806_, lean_object* v_shortName_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_Elab_mkDeclName___redArg(v_inst_1800_, v_inst_1801_, v_inst_1802_, v_inst_1803_, v_inst_1804_, v_currNamespace_1805_, v_modifiers_1806_, v_shortName_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore(lean_object* v_declId_1818_){
_start:
{
uint8_t v___x_1819_; 
v___x_1819_ = l_Lean_Syntax_isIdent(v_declId_1818_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v_id_1822_; lean_object* v___x_1823_; lean_object* v_optUnivDeclStx_1824_; lean_object* v___x_1825_; 
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = l_Lean_Syntax_getArg(v_declId_1818_, v___x_1820_);
v_id_1822_ = l_Lean_Syntax_getId(v___x_1821_);
lean_dec(v___x_1821_);
v___x_1823_ = lean_unsigned_to_nat(1u);
v_optUnivDeclStx_1824_ = l_Lean_Syntax_getArg(v_declId_1818_, v___x_1823_);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v_id_1822_);
lean_ctor_set(v___x_1825_, 1, v_optUnivDeclStx_1824_);
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = l_Lean_Syntax_getId(v_declId_1818_);
v___x_1827_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__3));
v___x_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1826_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
return v___x_1828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore___boxed(lean_object* v_declId_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_Elab_expandDeclIdCore(v_declId_1829_);
lean_dec(v_declId_1829_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(lean_object* v_msgData_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v___x_1837_; lean_object* v_env_1838_; lean_object* v___x_1839_; lean_object* v_mctx_1840_; lean_object* v_lctx_1841_; lean_object* v_options_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1837_ = lean_st_ref_get(v___y_1835_);
v_env_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc_ref(v_env_1838_);
lean_dec(v___x_1837_);
v___x_1839_ = lean_st_ref_get(v___y_1833_);
v_mctx_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc_ref(v_mctx_1840_);
lean_dec(v___x_1839_);
v_lctx_1841_ = lean_ctor_get(v___y_1832_, 2);
v_options_1842_ = lean_ctor_get(v___y_1834_, 2);
lean_inc_ref(v_options_1842_);
lean_inc_ref(v_lctx_1841_);
v___x_1843_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1843_, 0, v_env_1838_);
lean_ctor_set(v___x_1843_, 1, v_mctx_1840_);
lean_ctor_set(v___x_1843_, 2, v_lctx_1841_);
lean_ctor_set(v___x_1843_, 3, v_options_1842_);
v___x_1844_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v_msgData_1831_);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msgData_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
return v_res_1852_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(lean_object* v_opts_1853_, lean_object* v_opt_1854_){
_start:
{
lean_object* v_name_1855_; lean_object* v_defValue_1856_; lean_object* v_map_1857_; lean_object* v___x_1858_; 
v_name_1855_ = lean_ctor_get(v_opt_1854_, 0);
v_defValue_1856_ = lean_ctor_get(v_opt_1854_, 1);
v_map_1857_ = lean_ctor_get(v_opts_1853_, 0);
v___x_1858_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1857_, v_name_1855_);
if (lean_obj_tag(v___x_1858_) == 0)
{
uint8_t v___x_1859_; 
v___x_1859_ = lean_unbox(v_defValue_1856_);
return v___x_1859_;
}
else
{
lean_object* v_val_1860_; 
v_val_1860_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_val_1860_);
lean_dec_ref(v___x_1858_);
if (lean_obj_tag(v_val_1860_) == 1)
{
uint8_t v_v_1861_; 
v_v_1861_ = lean_ctor_get_uint8(v_val_1860_, 0);
lean_dec_ref(v_val_1860_);
return v_v_1861_;
}
else
{
uint8_t v___x_1862_; 
lean_dec(v_val_1860_);
v___x_1862_ = lean_unbox(v_defValue_1856_);
return v___x_1862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_opts_1863_, lean_object* v_opt_1864_){
_start:
{
uint8_t v_res_1865_; lean_object* v_r_1866_; 
v_res_1865_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_opts_1863_, v_opt_1864_);
lean_dec_ref(v_opt_1864_);
lean_dec_ref(v_opts_1863_);
v_r_1866_ = lean_box(v_res_1865_);
return v_r_1866_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = lean_box(1);
v___x_1868_ = l_Lean_MessageData_ofFormat(v___x_1867_);
return v___x_1868_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2));
v___x_1873_ = l_Lean_MessageData_ofFormat(v___x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(lean_object* v_x_1874_, lean_object* v_x_1875_){
_start:
{
if (lean_obj_tag(v_x_1875_) == 0)
{
return v_x_1874_;
}
else
{
lean_object* v_head_1876_; lean_object* v_tail_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1899_; 
v_head_1876_ = lean_ctor_get(v_x_1875_, 0);
v_tail_1877_ = lean_ctor_get(v_x_1875_, 1);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1879_ = v_x_1875_;
v_isShared_1880_ = v_isSharedCheck_1899_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_tail_1877_);
lean_inc(v_head_1876_);
lean_dec(v_x_1875_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1899_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_before_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1897_; 
v_before_1881_ = lean_ctor_get(v_head_1876_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_head_1876_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v_head_1876_, 1);
lean_dec(v_unused_1898_);
v___x_1883_ = v_head_1876_;
v_isShared_1884_ = v_isSharedCheck_1897_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_before_1881_);
lean_dec(v_head_1876_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1897_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_1884_ == 0)
{
lean_ctor_set_tag(v___x_1883_, 7);
lean_ctor_set(v___x_1883_, 1, v___x_1885_);
lean_ctor_set(v___x_1883_, 0, v_x_1874_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_x_1874_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1888_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3);
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 7);
lean_ctor_set(v___x_1879_, 1, v___x_1888_);
lean_ctor_set(v___x_1879_, 0, v___x_1887_);
v___x_1890_ = v___x_1879_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = l_Lean_MessageData_ofSyntax(v_before_1881_);
v___x_1892_ = l_Lean_indentD(v___x_1891_);
v___x_1893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1890_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v_x_1874_ = v___x_1893_;
v_x_1875_ = v_tail_1877_;
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
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1));
v___x_1904_ = l_Lean_MessageData_ofFormat(v___x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_1905_, lean_object* v_macroStack_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_options_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v_options_1909_ = lean_ctor_get(v___y_1907_, 2);
v___x_1910_ = l_Lean_Elab_pp_macroStack;
v___x_1911_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_options_1909_, v___x_1910_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; 
lean_dec(v_macroStack_1906_);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_msgData_1905_);
return v___x_1912_;
}
else
{
if (lean_obj_tag(v_macroStack_1906_) == 0)
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_msgData_1905_);
return v___x_1913_;
}
else
{
lean_object* v_head_1914_; lean_object* v_after_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1930_; 
v_head_1914_ = lean_ctor_get(v_macroStack_1906_, 0);
lean_inc(v_head_1914_);
v_after_1915_ = lean_ctor_get(v_head_1914_, 1);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_head_1914_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; 
v_unused_1931_ = lean_ctor_get(v_head_1914_, 0);
lean_dec(v_unused_1931_);
v___x_1917_ = v_head_1914_;
v_isShared_1918_ = v_isSharedCheck_1930_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_after_1915_);
lean_dec(v_head_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1930_;
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
lean_ctor_set(v___x_1917_, 0, v_msgData_1905_);
v___x_1921_ = v___x_1917_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_msgData_1905_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v_msgData_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1922_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = l_Lean_MessageData_ofSyntax(v_after_1915_);
v___x_1925_ = l_Lean_indentD(v___x_1924_);
v_msgData_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1926_, 0, v___x_1923_);
lean_ctor_set(v_msgData_1926_, 1, v___x_1925_);
v___x_1927_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(v_msgData_1926_, v_macroStack_1906_);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
return v___x_1928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_1932_, lean_object* v_macroStack_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_1932_, v_macroStack_1933_, v___y_1934_);
lean_dec_ref(v___y_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(lean_object* v_msg_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_ref_1945_; lean_object* v___x_1946_; lean_object* v_a_1947_; lean_object* v_macroStack_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1959_; 
v_ref_1945_ = lean_ctor_get(v___y_1942_, 5);
v___x_1946_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msg_1937_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref(v___x_1946_);
v_macroStack_1948_ = lean_ctor_get(v___y_1938_, 1);
lean_inc_n(v_macroStack_1948_, 2);
v___x_1949_ = l_Lean_Elab_getBetterRef(v_ref_1945_, v_macroStack_1948_);
v___x_1950_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_a_1947_, v_macroStack_1948_, v___y_1942_);
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1949_);
lean_ctor_set(v___x_1955_, 1, v_a_1951_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set_tag(v___x_1953_, 1);
lean_ctor_set(v___x_1953_, 0, v___x_1955_);
v___x_1957_ = v___x_1953_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(lean_object* v_env_1969_, lean_object* v_declName_1970_, lean_object* v___f_1971_, lean_object* v_addInfo_1972_, lean_object* v_____r_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v___x_1981_; uint8_t v___x_1982_; uint8_t v___x_1983_; 
lean_inc(v_declName_1970_);
v___x_1981_ = l_Lean_mkPrivateName(v_env_1969_, v_declName_1970_);
v___x_1982_ = 1;
lean_inc(v___x_1981_);
v___x_1983_ = l_Lean_Environment_contains(v_env_1969_, v___x_1981_, v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_dec(v___x_1981_);
lean_dec_ref(v_addInfo_1972_);
lean_dec(v_declName_1970_);
v___x_1984_ = lean_box(0);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
lean_inc(v___y_1975_);
lean_inc_ref(v___y_1974_);
v___x_1985_ = lean_apply_8(v___f_1971_, v___x_1984_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, lean_box(0));
return v___x_1985_;
}
else
{
lean_object* v___x_1986_; 
lean_dec_ref(v___f_1971_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
lean_inc(v___y_1975_);
lean_inc_ref(v___y_1974_);
v___x_1986_ = lean_apply_8(v_addInfo_1972_, v___x_1981_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, lean_box(0));
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
lean_dec_ref(v___x_1986_);
v___x_1987_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1);
v___x_1988_ = l_Lean_MessageData_ofConstName(v_declName_1970_, v___x_1982_);
v___x_1989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_1991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_1991_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
return v___x_1992_;
}
else
{
lean_dec(v_declName_1970_);
return v___x_1986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed(lean_object* v_env_1993_, lean_object* v_declName_1994_, lean_object* v___f_1995_, lean_object* v_addInfo_1996_, lean_object* v_____r_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(v_env_1993_, v_declName_1994_, v___f_1995_, v_addInfo_1996_, v_____r_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(lean_object* v___f_2006_, lean_object* v_declName_2007_, uint8_t v___x_2008_, lean_object* v_env_2009_, lean_object* v_____do__lift_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
uint8_t v___y_2019_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
lean_inc(v_declName_2007_);
v___x_2028_ = l_Lean_privateToUserName(v_declName_2007_);
lean_inc_ref(v_env_2009_);
v___x_2029_ = lean_is_reserved_name(v_env_2009_, v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; uint8_t v___x_2031_; 
lean_inc(v_declName_2007_);
v___x_2030_ = l_Lean_mkPrivateName(v_____do__lift_2010_, v_declName_2007_);
v___x_2031_ = lean_is_reserved_name(v_env_2009_, v___x_2030_);
v___y_2019_ = v___x_2031_;
goto v___jp_2018_;
}
else
{
lean_dec_ref(v_env_2009_);
v___y_2019_ = v___x_2029_;
goto v___jp_2018_;
}
v___jp_2018_:
{
if (v___y_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_dec(v_declName_2007_);
v___x_2020_ = lean_box(0);
lean_inc(v___y_2016_);
lean_inc_ref(v___y_2015_);
lean_inc(v___y_2014_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2012_);
lean_inc_ref(v___y_2011_);
v___x_2021_ = lean_apply_8(v___f_2006_, v___x_2020_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, lean_box(0));
return v___x_2021_;
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_dec_ref(v___f_2006_);
v___x_2022_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2023_ = l_Lean_MessageData_ofConstName(v_declName_2007_, v___x_2008_);
v___x_2024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2022_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
v___x_2025_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3);
v___x_2026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2024_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2026_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
return v___x_2027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed(lean_object* v___f_2032_, lean_object* v_declName_2033_, lean_object* v___x_2034_, lean_object* v_env_2035_, lean_object* v_____do__lift_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
uint8_t v___x_17521__boxed_2044_; lean_object* v_res_2045_; 
v___x_17521__boxed_2044_ = lean_unbox(v___x_2034_);
v_res_2045_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(v___f_2032_, v_declName_2033_, v___x_17521__boxed_2044_, v_env_2035_, v_____do__lift_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec_ref(v_____do__lift_2036_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(lean_object* v_t_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___x_2049_; lean_object* v_infoState_2050_; uint8_t v_enabled_2051_; 
v___x_2049_ = lean_st_ref_get(v___y_2047_);
v_infoState_2050_ = lean_ctor_get(v___x_2049_, 7);
lean_inc_ref(v_infoState_2050_);
lean_dec(v___x_2049_);
v_enabled_2051_ = lean_ctor_get_uint8(v_infoState_2050_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2050_);
if (v_enabled_2051_ == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_dec_ref(v_t_2046_);
v___x_2052_ = lean_box(0);
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
return v___x_2053_;
}
else
{
lean_object* v___x_2054_; lean_object* v_infoState_2055_; lean_object* v_env_2056_; lean_object* v_nextMacroScope_2057_; lean_object* v_ngen_2058_; lean_object* v_auxDeclNGen_2059_; lean_object* v_traceState_2060_; lean_object* v_cache_2061_; lean_object* v_messages_2062_; lean_object* v_snapshotTasks_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2085_; 
v___x_2054_ = lean_st_ref_take(v___y_2047_);
v_infoState_2055_ = lean_ctor_get(v___x_2054_, 7);
v_env_2056_ = lean_ctor_get(v___x_2054_, 0);
v_nextMacroScope_2057_ = lean_ctor_get(v___x_2054_, 1);
v_ngen_2058_ = lean_ctor_get(v___x_2054_, 2);
v_auxDeclNGen_2059_ = lean_ctor_get(v___x_2054_, 3);
v_traceState_2060_ = lean_ctor_get(v___x_2054_, 4);
v_cache_2061_ = lean_ctor_get(v___x_2054_, 5);
v_messages_2062_ = lean_ctor_get(v___x_2054_, 6);
v_snapshotTasks_2063_ = lean_ctor_get(v___x_2054_, 8);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2065_ = v___x_2054_;
v_isShared_2066_ = v_isSharedCheck_2085_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_snapshotTasks_2063_);
lean_inc(v_infoState_2055_);
lean_inc(v_messages_2062_);
lean_inc(v_cache_2061_);
lean_inc(v_traceState_2060_);
lean_inc(v_auxDeclNGen_2059_);
lean_inc(v_ngen_2058_);
lean_inc(v_nextMacroScope_2057_);
lean_inc(v_env_2056_);
lean_dec(v___x_2054_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2085_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
uint8_t v_enabled_2067_; lean_object* v_assignment_2068_; lean_object* v_lazyAssignment_2069_; lean_object* v_trees_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2084_; 
v_enabled_2067_ = lean_ctor_get_uint8(v_infoState_2055_, sizeof(void*)*3);
v_assignment_2068_ = lean_ctor_get(v_infoState_2055_, 0);
v_lazyAssignment_2069_ = lean_ctor_get(v_infoState_2055_, 1);
v_trees_2070_ = lean_ctor_get(v_infoState_2055_, 2);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_infoState_2055_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2072_ = v_infoState_2055_;
v_isShared_2073_ = v_isSharedCheck_2084_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_trees_2070_);
lean_inc(v_lazyAssignment_2069_);
lean_inc(v_assignment_2068_);
lean_dec(v_infoState_2055_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2084_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2074_ = l_Lean_PersistentArray_push___redArg(v_trees_2070_, v_t_2046_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 2, v___x_2074_);
v___x_2076_ = v___x_2072_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_assignment_2068_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_lazyAssignment_2069_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v___x_2074_);
lean_ctor_set_uint8(v_reuseFailAlloc_2083_, sizeof(void*)*3, v_enabled_2067_);
v___x_2076_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2078_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 7, v___x_2076_);
v___x_2078_ = v___x_2065_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_env_2056_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_nextMacroScope_2057_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_ngen_2058_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v_auxDeclNGen_2059_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v_traceState_2060_);
lean_ctor_set(v_reuseFailAlloc_2082_, 5, v_cache_2061_);
lean_ctor_set(v_reuseFailAlloc_2082_, 6, v_messages_2062_);
lean_ctor_set(v_reuseFailAlloc_2082_, 7, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2082_, 8, v_snapshotTasks_2063_);
v___x_2078_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_st_ref_set(v___y_2047_, v___x_2078_);
v___x_2080_ = lean_box(0);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
return v___x_2081_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg___boxed(lean_object* v_t_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_2086_, v___y_2087_);
lean_dec(v___y_2087_);
return v_res_2089_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2090_ = lean_unsigned_to_nat(32u);
v___x_2091_ = lean_mk_empty_array_with_capacity(v___x_2090_);
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
return v___x_2092_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1(void){
_start:
{
size_t v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2093_ = ((size_t)5ULL);
v___x_2094_ = lean_unsigned_to_nat(0u);
v___x_2095_ = lean_unsigned_to_nat(32u);
v___x_2096_ = lean_mk_empty_array_with_capacity(v___x_2095_);
v___x_2097_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0);
v___x_2098_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v___x_2096_);
lean_ctor_set(v___x_2098_, 2, v___x_2094_);
lean_ctor_set(v___x_2098_, 3, v___x_2094_);
lean_ctor_set_usize(v___x_2098_, 4, v___x_2093_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(lean_object* v_t_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; lean_object* v_infoState_2108_; uint8_t v_enabled_2109_; 
v___x_2107_ = lean_st_ref_get(v___y_2105_);
v_infoState_2108_ = lean_ctor_get(v___x_2107_, 7);
lean_inc_ref(v_infoState_2108_);
lean_dec(v___x_2107_);
v_enabled_2109_ = lean_ctor_get_uint8(v_infoState_2108_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2108_);
if (v_enabled_2109_ == 0)
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
lean_dec_ref(v_t_2099_);
v___x_2110_ = lean_box(0);
v___x_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
return v___x_2111_;
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1);
v___x_2113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2113_, 0, v_t_2099_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v___x_2113_, v___y_2105_);
return v___x_2114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___boxed(lean_object* v_t_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v_t_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
if (lean_obj_tag(v_a_2124_) == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = l_List_reverse___redArg(v_a_2125_);
return v___x_2126_;
}
else
{
lean_object* v_head_2127_; lean_object* v_tail_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2137_; 
v_head_2127_ = lean_ctor_get(v_a_2124_, 0);
v_tail_2128_ = lean_ctor_get(v_a_2124_, 1);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_a_2124_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2130_ = v_a_2124_;
v_isShared_2131_ = v_isSharedCheck_2137_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_tail_2128_);
lean_inc(v_head_2127_);
lean_dec(v_a_2124_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2137_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2132_ = l_Lean_mkLevelParam(v_head_2127_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 1, v_a_2125_);
lean_ctor_set(v___x_2130_, 0, v___x_2132_);
v___x_2134_ = v___x_2130_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_a_2125_);
v___x_2134_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
v_a_2124_ = v_tail_2128_;
v_a_2125_ = v___x_2134_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0(void){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2138_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0);
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
return v___x_2140_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
lean_ctor_set(v___x_2143_, 2, v___x_2142_);
lean_ctor_set(v___x_2143_, 3, v___x_2142_);
lean_ctor_set(v___x_2143_, 4, v___x_2141_);
lean_ctor_set(v___x_2143_, 5, v___x_2141_);
lean_ctor_set(v___x_2143_, 6, v___x_2141_);
lean_ctor_set(v___x_2143_, 7, v___x_2141_);
lean_ctor_set(v___x_2143_, 8, v___x_2141_);
lean_ctor_set(v___x_2143_, 9, v___x_2141_);
return v___x_2143_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2144_ = lean_box(1);
v___x_2145_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3);
v___x_2146_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
v___x_2147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
lean_ctor_set(v___x_2147_, 1, v___x_2145_);
lean_ctor_set(v___x_2147_, 2, v___x_2144_);
return v___x_2147_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4));
v___x_2150_ = l_Lean_stringToMessageData(v___x_2149_);
return v___x_2150_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7(void){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6));
v___x_2153_ = l_Lean_stringToMessageData(v___x_2152_);
return v___x_2153_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8));
v___x_2156_ = l_Lean_stringToMessageData(v___x_2155_);
return v___x_2156_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10));
v___x_2159_ = l_Lean_stringToMessageData(v___x_2158_);
return v___x_2159_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12));
v___x_2162_ = l_Lean_stringToMessageData(v___x_2161_);
return v___x_2162_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14));
v___x_2165_ = l_Lean_stringToMessageData(v___x_2164_);
return v___x_2165_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16));
v___x_2168_ = l_Lean_stringToMessageData(v___x_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(lean_object* v_msg_2169_, lean_object* v_declHint_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v___x_2173_; lean_object* v_env_2174_; uint8_t v___x_2175_; 
v___x_2173_ = lean_st_ref_get(v___y_2171_);
v_env_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc_ref(v_env_2174_);
lean_dec(v___x_2173_);
v___x_2175_ = l_Lean_Name_isAnonymous(v_declHint_2170_);
if (v___x_2175_ == 0)
{
uint8_t v_isExporting_2176_; 
v_isExporting_2176_ = lean_ctor_get_uint8(v_env_2174_, sizeof(void*)*8);
if (v_isExporting_2176_ == 0)
{
lean_object* v___x_2177_; 
lean_dec_ref(v_env_2174_);
lean_dec(v_declHint_2170_);
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v_msg_2169_);
return v___x_2177_;
}
else
{
lean_object* v___x_2178_; uint8_t v___x_2179_; 
lean_inc_ref(v_env_2174_);
v___x_2178_ = l_Lean_Environment_setExporting(v_env_2174_, v___x_2175_);
lean_inc(v_declHint_2170_);
lean_inc_ref(v___x_2178_);
v___x_2179_ = l_Lean_Environment_contains(v___x_2178_, v_declHint_2170_, v_isExporting_2176_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; 
lean_dec_ref(v___x_2178_);
lean_dec_ref(v_env_2174_);
lean_dec(v_declHint_2170_);
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v_msg_2169_);
return v___x_2180_;
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_c_2186_; lean_object* v___x_2187_; 
v___x_2181_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2);
v___x_2182_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3);
v___x_2183_ = l_Lean_Options_empty;
v___x_2184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2178_);
lean_ctor_set(v___x_2184_, 1, v___x_2181_);
lean_ctor_set(v___x_2184_, 2, v___x_2182_);
lean_ctor_set(v___x_2184_, 3, v___x_2183_);
lean_inc(v_declHint_2170_);
v___x_2185_ = l_Lean_MessageData_ofConstName(v_declHint_2170_, v___x_2175_);
v_c_2186_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2186_, 0, v___x_2184_);
lean_ctor_set(v_c_2186_, 1, v___x_2185_);
v___x_2187_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2174_, v_declHint_2170_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
lean_dec_ref(v_env_2174_);
lean_dec(v_declHint_2170_);
v___x_2188_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5);
v___x_2189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v_c_2186_);
v___x_2190_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = l_Lean_MessageData_note(v___x_2191_);
v___x_2193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2193_, 0, v_msg_2169_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
return v___x_2194_;
}
else
{
lean_object* v_val_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2230_; 
v_val_2195_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2197_ = v___x_2187_;
v_isShared_2198_ = v_isSharedCheck_2230_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_val_2195_);
lean_dec(v___x_2187_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2230_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v_mod_2202_; uint8_t v___x_2203_; 
v___x_2199_ = lean_box(0);
v___x_2200_ = l_Lean_Environment_header(v_env_2174_);
lean_dec_ref(v_env_2174_);
v___x_2201_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2200_);
v_mod_2202_ = lean_array_get(v___x_2199_, v___x_2201_, v_val_2195_);
lean_dec(v_val_2195_);
lean_dec_ref(v___x_2201_);
v___x_2203_ = l_Lean_isPrivateName(v_declHint_2170_);
lean_dec(v_declHint_2170_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2204_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9);
v___x_2205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v_c_2186_);
v___x_2206_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11);
v___x_2207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = l_Lean_MessageData_ofName(v_mod_2202_);
v___x_2209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13);
v___x_2211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2209_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = l_Lean_MessageData_note(v___x_2211_);
v___x_2213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2213_, 0, v_msg_2169_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set_tag(v___x_2197_, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2213_);
v___x_2215_ = v___x_2197_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2217_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5);
v___x_2218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v_c_2186_);
v___x_2219_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15);
v___x_2220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = l_Lean_MessageData_ofName(v_mod_2202_);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17);
v___x_2224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = l_Lean_MessageData_note(v___x_2224_);
v___x_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2226_, 0, v_msg_2169_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set_tag(v___x_2197_, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2226_);
v___x_2228_ = v___x_2197_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2231_; 
lean_dec_ref(v_env_2174_);
lean_dec(v_declHint_2170_);
v___x_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2231_, 0, v_msg_2169_);
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___boxed(lean_object* v_msg_2232_, lean_object* v_declHint_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2232_, v_declHint_2233_, v___y_2234_);
lean_dec(v___y_2234_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(lean_object* v_msg_2237_, lean_object* v_declHint_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2256_; 
v___x_2246_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2237_, v_declHint_2238_, v___y_2244_);
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2256_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2256_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2254_; 
v___x_2251_ = l_Lean_unknownIdentifierMessageTag;
v___x_2252_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v_a_2247_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2252_);
v___x_2254_ = v___x_2249_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23___boxed(lean_object* v_msg_2257_, lean_object* v_declHint_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2257_, v_declHint_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(lean_object* v_ref_2267_, lean_object* v_msg_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_fileName_2276_; lean_object* v_fileMap_2277_; lean_object* v_options_2278_; lean_object* v_currRecDepth_2279_; lean_object* v_maxRecDepth_2280_; lean_object* v_ref_2281_; lean_object* v_currNamespace_2282_; lean_object* v_openDecls_2283_; lean_object* v_initHeartbeats_2284_; lean_object* v_maxHeartbeats_2285_; lean_object* v_quotContext_2286_; lean_object* v_currMacroScope_2287_; uint8_t v_diag_2288_; lean_object* v_cancelTk_x3f_2289_; uint8_t v_suppressElabErrors_2290_; lean_object* v_inheritedTraceOptions_2291_; lean_object* v_ref_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_fileName_2276_ = lean_ctor_get(v___y_2273_, 0);
v_fileMap_2277_ = lean_ctor_get(v___y_2273_, 1);
v_options_2278_ = lean_ctor_get(v___y_2273_, 2);
v_currRecDepth_2279_ = lean_ctor_get(v___y_2273_, 3);
v_maxRecDepth_2280_ = lean_ctor_get(v___y_2273_, 4);
v_ref_2281_ = lean_ctor_get(v___y_2273_, 5);
v_currNamespace_2282_ = lean_ctor_get(v___y_2273_, 6);
v_openDecls_2283_ = lean_ctor_get(v___y_2273_, 7);
v_initHeartbeats_2284_ = lean_ctor_get(v___y_2273_, 8);
v_maxHeartbeats_2285_ = lean_ctor_get(v___y_2273_, 9);
v_quotContext_2286_ = lean_ctor_get(v___y_2273_, 10);
v_currMacroScope_2287_ = lean_ctor_get(v___y_2273_, 11);
v_diag_2288_ = lean_ctor_get_uint8(v___y_2273_, sizeof(void*)*14);
v_cancelTk_x3f_2289_ = lean_ctor_get(v___y_2273_, 12);
v_suppressElabErrors_2290_ = lean_ctor_get_uint8(v___y_2273_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2291_ = lean_ctor_get(v___y_2273_, 13);
v_ref_2292_ = l_Lean_replaceRef(v_ref_2267_, v_ref_2281_);
lean_inc_ref(v_inheritedTraceOptions_2291_);
lean_inc(v_cancelTk_x3f_2289_);
lean_inc(v_currMacroScope_2287_);
lean_inc(v_quotContext_2286_);
lean_inc(v_maxHeartbeats_2285_);
lean_inc(v_initHeartbeats_2284_);
lean_inc(v_openDecls_2283_);
lean_inc(v_currNamespace_2282_);
lean_inc(v_maxRecDepth_2280_);
lean_inc(v_currRecDepth_2279_);
lean_inc_ref(v_options_2278_);
lean_inc_ref(v_fileMap_2277_);
lean_inc_ref(v_fileName_2276_);
v___x_2293_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2293_, 0, v_fileName_2276_);
lean_ctor_set(v___x_2293_, 1, v_fileMap_2277_);
lean_ctor_set(v___x_2293_, 2, v_options_2278_);
lean_ctor_set(v___x_2293_, 3, v_currRecDepth_2279_);
lean_ctor_set(v___x_2293_, 4, v_maxRecDepth_2280_);
lean_ctor_set(v___x_2293_, 5, v_ref_2292_);
lean_ctor_set(v___x_2293_, 6, v_currNamespace_2282_);
lean_ctor_set(v___x_2293_, 7, v_openDecls_2283_);
lean_ctor_set(v___x_2293_, 8, v_initHeartbeats_2284_);
lean_ctor_set(v___x_2293_, 9, v_maxHeartbeats_2285_);
lean_ctor_set(v___x_2293_, 10, v_quotContext_2286_);
lean_ctor_set(v___x_2293_, 11, v_currMacroScope_2287_);
lean_ctor_set(v___x_2293_, 12, v_cancelTk_x3f_2289_);
lean_ctor_set(v___x_2293_, 13, v_inheritedTraceOptions_2291_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*14, v_diag_2288_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*14 + 1, v_suppressElabErrors_2290_);
v___x_2294_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___x_2293_, v___y_2274_);
lean_dec_ref(v___x_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg___boxed(lean_object* v_ref_2295_, lean_object* v_msg_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2295_, v_msg_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v_ref_2295_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(lean_object* v_ref_2305_, lean_object* v_msg_2306_, lean_object* v_declHint_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; lean_object* v_a_2316_; lean_object* v___x_2317_; 
v___x_2315_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2306_, v_declHint_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref(v___x_2315_);
v___x_2317_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2305_, v_a_2316_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg___boxed(lean_object* v_ref_2318_, lean_object* v_msg_2319_, lean_object* v_declHint_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2318_, v_msg_2319_, v_declHint_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v_ref_2318_);
return v_res_2328_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0));
v___x_2331_ = l_Lean_stringToMessageData(v___x_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(lean_object* v_ref_2332_, lean_object* v_constName_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___x_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2341_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1);
v___x_2342_ = 0;
lean_inc(v_constName_2333_);
v___x_2343_ = l_Lean_MessageData_ofConstName(v_constName_2333_, v___x_2342_);
v___x_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2341_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
v___x_2347_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2332_, v___x_2346_, v_constName_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___boxed(lean_object* v_ref_2348_, lean_object* v_constName_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2348_, v_constName_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v_ref_2348_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(lean_object* v_constName_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_ref_2366_; lean_object* v___x_2367_; 
v_ref_2366_ = lean_ctor_get(v___y_2363_, 5);
v___x_2367_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2366_, v_constName_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_constName_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(lean_object* v_constName_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___x_2385_; lean_object* v_env_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; 
v___x_2385_ = lean_st_ref_get(v___y_2383_);
v_env_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc_ref(v_env_2386_);
lean_dec(v___x_2385_);
v___x_2387_ = 0;
lean_inc(v_constName_2377_);
v___x_2388_ = l_Lean_Environment_findConstVal_x3f(v_env_2386_, v_constName_2377_, v___x_2387_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
return v___x_2389_;
}
else
{
lean_object* v_val_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v_constName_2377_);
v_val_2390_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2388_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_val_2390_);
lean_dec(v___x_2388_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
lean_ctor_set_tag(v___x_2392_, 0);
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_val_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14___boxed(lean_object* v_constName_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(lean_object* v_constName_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___x_2415_; 
lean_inc(v_constName_2407_);
v___x_2415_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2427_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2427_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2427_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_levelParams_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2425_; 
v_levelParams_2420_ = lean_ctor_get(v_a_2416_, 1);
lean_inc(v_levelParams_2420_);
lean_dec(v_a_2416_);
v___x_2421_ = lean_box(0);
v___x_2422_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(v_levelParams_2420_, v___x_2421_);
v___x_2423_ = l_Lean_mkConst(v_constName_2407_, v___x_2422_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2423_);
v___x_2425_ = v___x_2418_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_constName_2407_);
v_a_2428_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2415_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2415_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_constName_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_constName_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(uint8_t v___x_2445_, lean_object* v_declName_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v_ref_2454_; lean_object* v___x_2455_; 
v_ref_2454_ = lean_ctor_get(v___y_2451_, 5);
v___x_2455_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_declName_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref(v___x_2455_);
v___x_2457_ = lean_box(0);
lean_inc(v_ref_2454_);
v___x_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
lean_ctor_set(v___x_2458_, 1, v_ref_2454_);
v___x_2459_ = lean_unsigned_to_nat(32u);
v___x_2460_ = lean_mk_empty_array_with_capacity(v___x_2459_);
lean_dec_ref(v___x_2460_);
v___x_2461_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4);
v___x_2462_ = lean_box(0);
v___x_2463_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2463_, 0, v___x_2458_);
lean_ctor_set(v___x_2463_, 1, v___x_2461_);
lean_ctor_set(v___x_2463_, 2, v___x_2462_);
lean_ctor_set(v___x_2463_, 3, v_a_2456_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*4, v___x_2445_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*4 + 1, v___x_2445_);
v___x_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
v___x_2465_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v___x_2464_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2465_;
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
v_a_2466_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2455_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2455_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v___x_2474_, lean_object* v_declName_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
uint8_t v___x_18250__boxed_2483_; lean_object* v_res_2484_; 
v___x_18250__boxed_2483_ = lean_unbox(v___x_2474_);
v_res_2484_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(v___x_18250__boxed_2483_, v_declName_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(lean_object* v___f_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v___x_2493_; lean_object* v_env_2494_; lean_object* v___x_2495_; 
v___x_2493_ = lean_st_ref_get(v___y_2491_);
v_env_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc_ref(v_env_2494_);
lean_dec(v___x_2493_);
v___x_2495_ = lean_apply_8(v___f_2485_, v_env_2494_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, lean_box(0));
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed(lean_object* v___f_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(v___f_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
return v_res_2504_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2505_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
return v___x_2507_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
return v___x_2509_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
v___x_2511_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
lean_ctor_set(v___x_2511_, 2, v___x_2510_);
lean_ctor_set(v___x_2511_, 3, v___x_2510_);
lean_ctor_set(v___x_2511_, 4, v___x_2510_);
lean_ctor_set(v___x_2511_, 5, v___x_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(lean_object* v_env_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v___x_2516_; lean_object* v_nextMacroScope_2517_; lean_object* v_ngen_2518_; lean_object* v_auxDeclNGen_2519_; lean_object* v_traceState_2520_; lean_object* v_messages_2521_; lean_object* v_infoState_2522_; lean_object* v_snapshotTasks_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2549_; 
v___x_2516_ = lean_st_ref_take(v___y_2514_);
v_nextMacroScope_2517_ = lean_ctor_get(v___x_2516_, 1);
v_ngen_2518_ = lean_ctor_get(v___x_2516_, 2);
v_auxDeclNGen_2519_ = lean_ctor_get(v___x_2516_, 3);
v_traceState_2520_ = lean_ctor_get(v___x_2516_, 4);
v_messages_2521_ = lean_ctor_get(v___x_2516_, 6);
v_infoState_2522_ = lean_ctor_get(v___x_2516_, 7);
v_snapshotTasks_2523_ = lean_ctor_get(v___x_2516_, 8);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2549_ == 0)
{
lean_object* v_unused_2550_; lean_object* v_unused_2551_; 
v_unused_2550_ = lean_ctor_get(v___x_2516_, 5);
lean_dec(v_unused_2550_);
v_unused_2551_ = lean_ctor_get(v___x_2516_, 0);
lean_dec(v_unused_2551_);
v___x_2525_ = v___x_2516_;
v_isShared_2526_ = v_isSharedCheck_2549_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_snapshotTasks_2523_);
lean_inc(v_infoState_2522_);
lean_inc(v_messages_2521_);
lean_inc(v_traceState_2520_);
lean_inc(v_auxDeclNGen_2519_);
lean_inc(v_ngen_2518_);
lean_inc(v_nextMacroScope_2517_);
lean_dec(v___x_2516_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2549_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2527_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 5, v___x_2527_);
lean_ctor_set(v___x_2525_, 0, v_env_2512_);
v___x_2529_ = v___x_2525_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_env_2512_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_nextMacroScope_2517_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_ngen_2518_);
lean_ctor_set(v_reuseFailAlloc_2548_, 3, v_auxDeclNGen_2519_);
lean_ctor_set(v_reuseFailAlloc_2548_, 4, v_traceState_2520_);
lean_ctor_set(v_reuseFailAlloc_2548_, 5, v___x_2527_);
lean_ctor_set(v_reuseFailAlloc_2548_, 6, v_messages_2521_);
lean_ctor_set(v_reuseFailAlloc_2548_, 7, v_infoState_2522_);
lean_ctor_set(v_reuseFailAlloc_2548_, 8, v_snapshotTasks_2523_);
v___x_2529_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v_mctx_2532_; lean_object* v_zetaDeltaFVarIds_2533_; lean_object* v_postponed_2534_; lean_object* v_diag_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2546_; 
v___x_2530_ = lean_st_ref_set(v___y_2514_, v___x_2529_);
v___x_2531_ = lean_st_ref_take(v___y_2513_);
v_mctx_2532_ = lean_ctor_get(v___x_2531_, 0);
v_zetaDeltaFVarIds_2533_ = lean_ctor_get(v___x_2531_, 2);
v_postponed_2534_ = lean_ctor_get(v___x_2531_, 3);
v_diag_2535_ = lean_ctor_get(v___x_2531_, 4);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2546_ == 0)
{
lean_object* v_unused_2547_; 
v_unused_2547_ = lean_ctor_get(v___x_2531_, 1);
lean_dec(v_unused_2547_);
v___x_2537_ = v___x_2531_;
v_isShared_2538_ = v_isSharedCheck_2546_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_diag_2535_);
lean_inc(v_postponed_2534_);
lean_inc(v_zetaDeltaFVarIds_2533_);
lean_inc(v_mctx_2532_);
lean_dec(v___x_2531_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2546_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2539_; lean_object* v___x_2541_; 
v___x_2539_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 1, v___x_2539_);
v___x_2541_ = v___x_2537_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_mctx_2532_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2545_, 2, v_zetaDeltaFVarIds_2533_);
lean_ctor_set(v_reuseFailAlloc_2545_, 3, v_postponed_2534_);
lean_ctor_set(v_reuseFailAlloc_2545_, 4, v_diag_2535_);
v___x_2541_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = lean_st_ref_set(v___y_2513_, v___x_2541_);
v___x_2543_ = lean_box(0);
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
return v___x_2544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___boxed(lean_object* v_env_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2552_, v___y_2553_, v___y_2554_);
lean_dec(v___y_2554_);
lean_dec(v___y_2553_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(lean_object* v_env_2557_, lean_object* v_x_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; lean_object* v_env_2567_; lean_object* v_a_2569_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2566_ = lean_st_ref_get(v___y_2564_);
v_env_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc_ref(v_env_2567_);
lean_dec(v___x_2566_);
v___x_2579_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2557_, v___y_2562_, v___y_2564_);
lean_dec_ref(v___x_2579_);
lean_inc(v___y_2564_);
lean_inc_ref(v___y_2563_);
lean_inc(v___y_2562_);
lean_inc_ref(v___y_2561_);
lean_inc(v___y_2560_);
lean_inc_ref(v___y_2559_);
v___x_2580_ = lean_apply_7(v_x_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, lean_box(0));
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref(v___x_2580_);
v___x_2582_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2567_, v___y_2562_, v___y_2564_);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2589_ == 0)
{
lean_object* v_unused_2590_; 
v_unused_2590_ = lean_ctor_get(v___x_2582_, 0);
lean_dec(v_unused_2590_);
v___x_2584_ = v___x_2582_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_dec(v___x_2582_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v_a_2581_);
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2581_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
else
{
lean_object* v_a_2591_; 
v_a_2591_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2591_);
lean_dec_ref(v___x_2580_);
v_a_2569_ = v_a_2591_;
goto v___jp_2568_;
}
v___jp_2568_:
{
lean_object* v___x_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
v___x_2570_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2567_, v___y_2562_, v___y_2564_);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v___x_2570_, 0);
lean_dec(v_unused_2578_);
v___x_2572_ = v___x_2570_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_dec(v___x_2570_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
lean_ctor_set_tag(v___x_2572_, 1);
lean_ctor_set(v___x_2572_, 0, v_a_2569_);
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2569_);
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
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_env_2592_, lean_object* v_x_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2592_, v_x_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(lean_object* v_declName_2602_, lean_object* v_env_2603_, lean_object* v_addInfo_2604_, lean_object* v_____r_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = lean_private_to_user_name(v_declName_2602_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_dec_ref(v_addInfo_2604_);
lean_dec_ref(v_env_2603_);
v___x_2614_ = lean_box(0);
v___x_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
return v___x_2615_;
}
else
{
lean_object* v_val_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2633_; 
v_val_2616_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2618_ = v___x_2613_;
v_isShared_2619_ = v_isSharedCheck_2633_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_val_2616_);
lean_dec(v___x_2613_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2633_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
uint8_t v___x_2620_; uint8_t v___x_2621_; 
v___x_2620_ = 1;
lean_inc(v_val_2616_);
v___x_2621_ = l_Lean_Environment_contains(v_env_2603_, v_val_2616_, v___x_2620_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; lean_object* v___x_2624_; 
lean_dec(v_val_2616_);
lean_dec_ref(v_addInfo_2604_);
v___x_2622_ = lean_box(0);
if (v_isShared_2619_ == 0)
{
lean_ctor_set_tag(v___x_2618_, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2622_);
v___x_2624_ = v___x_2618_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
else
{
lean_object* v___x_2626_; 
lean_del_object(v___x_2618_);
lean_inc(v___y_2611_);
lean_inc_ref(v___y_2610_);
lean_inc(v___y_2609_);
lean_inc_ref(v___y_2608_);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc(v_val_2616_);
v___x_2626_ = lean_apply_8(v_addInfo_2604_, v_val_2616_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, lean_box(0));
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_dec_ref(v___x_2626_);
v___x_2627_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
v___x_2628_ = l_Lean_MessageData_ofConstName(v_val_2616_, v___x_2620_);
v___x_2629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2627_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___x_2630_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2629_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2631_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2632_;
}
else
{
lean_dec(v_val_2616_);
return v___x_2626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed(lean_object* v_declName_2634_, lean_object* v_env_2635_, lean_object* v_addInfo_2636_, lean_object* v_____r_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(v_declName_2634_, v_env_2635_, v_addInfo_2636_, v_____r_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(lean_object* v_addInfo_2646_, lean_object* v_declName_2647_, uint8_t v___x_2648_, lean_object* v___f_2649_, uint8_t v___x_2650_, lean_object* v_env_2651_, lean_object* v___f_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; 
lean_inc(v___y_2658_);
lean_inc_ref(v___y_2657_);
lean_inc(v___y_2656_);
lean_inc_ref(v___y_2655_);
lean_inc(v___y_2654_);
lean_inc_ref(v___y_2653_);
lean_inc(v_declName_2647_);
v___x_2660_ = lean_apply_8(v_addInfo_2646_, v_declName_2647_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, lean_box(0));
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v___x_2661_; 
lean_dec_ref(v___x_2660_);
lean_inc(v_declName_2647_);
v___x_2661_ = lean_private_to_user_name(v_declName_2647_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2662_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2663_ = l_Lean_MessageData_ofConstName(v_declName_2647_, v___x_2648_);
v___x_2664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2662_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
v___x_2665_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2666_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
return v___x_2667_;
}
else
{
lean_object* v_val_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_dec(v_declName_2647_);
v_val_2668_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_val_2668_);
lean_dec_ref(v___x_2661_);
v___x_2669_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1);
v___x_2670_ = l_Lean_MessageData_ofConstName(v_val_2668_, v___x_2648_);
v___x_2671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2671_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2673_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
return v___x_2674_;
}
}
else
{
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v_declName_2647_);
return v___x_2660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed(lean_object* v_addInfo_2675_, lean_object* v_declName_2676_, lean_object* v___x_2677_, lean_object* v___f_2678_, lean_object* v___x_2679_, lean_object* v_env_2680_, lean_object* v___f_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
uint8_t v___x_18604__boxed_2689_; uint8_t v___x_18606__boxed_2690_; lean_object* v_res_2691_; 
v___x_18604__boxed_2689_ = lean_unbox(v___x_2677_);
v___x_18606__boxed_2690_ = lean_unbox(v___x_2679_);
v_res_2691_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(v_addInfo_2675_, v_declName_2676_, v___x_18604__boxed_2689_, v___f_2678_, v___x_18606__boxed_2690_, v_env_2680_, v___f_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec_ref(v___f_2681_);
lean_dec_ref(v_env_2680_);
lean_dec_ref(v___f_2678_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(lean_object* v_declName_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; lean_object* v_env_2704_; uint8_t v___x_2705_; lean_object* v_addInfo_2706_; lean_object* v_env_2707_; lean_object* v___f_2708_; lean_object* v___f_2709_; lean_object* v___x_2710_; lean_object* v___f_2711_; uint8_t v___x_2712_; uint8_t v___x_2713_; 
v___x_2703_ = lean_st_ref_get(v___y_2701_);
v_env_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc_ref(v_env_2704_);
lean_dec(v___x_2703_);
v___x_2705_ = 0;
v_addInfo_2706_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0));
v_env_2707_ = l_Lean_Environment_setExporting(v_env_2704_, v___x_2705_);
lean_inc_ref_n(v_env_2707_, 4);
lean_inc_n(v_declName_2695_, 4);
v___f_2708_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed), 11, 3);
lean_closure_set(v___f_2708_, 0, v_declName_2695_);
lean_closure_set(v___f_2708_, 1, v_env_2707_);
lean_closure_set(v___f_2708_, 2, v_addInfo_2706_);
v___f_2709_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2709_, 0, v_env_2707_);
lean_closure_set(v___f_2709_, 1, v_declName_2695_);
lean_closure_set(v___f_2709_, 2, v___f_2708_);
lean_closure_set(v___f_2709_, 3, v_addInfo_2706_);
v___x_2710_ = lean_box(v___x_2705_);
lean_inc_ref(v___f_2709_);
v___f_2711_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed), 12, 4);
lean_closure_set(v___f_2711_, 0, v___f_2709_);
lean_closure_set(v___f_2711_, 1, v_declName_2695_);
lean_closure_set(v___f_2711_, 2, v___x_2710_);
lean_closure_set(v___f_2711_, 3, v_env_2707_);
v___x_2712_ = 1;
v___x_2713_ = l_Lean_Environment_contains(v_env_2707_, v_declName_2695_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___f_2714_; lean_object* v___x_2715_; 
lean_dec_ref(v___f_2709_);
lean_dec(v_declName_2695_);
v___f_2714_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed), 8, 1);
lean_closure_set(v___f_2714_, 0, v___f_2711_);
v___x_2715_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2707_, v___f_2714_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
return v___x_2715_;
}
else
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___f_2718_; lean_object* v___x_2719_; 
v___x_2716_ = lean_box(v___x_2712_);
v___x_2717_ = lean_box(v___x_2705_);
lean_inc_ref(v_env_2707_);
v___f_2718_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed), 14, 7);
lean_closure_set(v___f_2718_, 0, v_addInfo_2706_);
lean_closure_set(v___f_2718_, 1, v_declName_2695_);
lean_closure_set(v___f_2718_, 2, v___x_2716_);
lean_closure_set(v___f_2718_, 3, v___f_2709_);
lean_closure_set(v___f_2718_, 4, v___x_2717_);
lean_closure_set(v___f_2718_, 5, v_env_2707_);
lean_closure_set(v___f_2718_, 6, v___f_2711_);
v___x_2719_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2707_, v___f_2718_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
return v___x_2719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___boxed(lean_object* v_declName_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(lean_object* v_modifiers_2729_, lean_object* v_declName_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2738_; lean_object* v_env_2739_; uint8_t v_visibility_2740_; uint8_t v_isProtected_2741_; lean_object* v_declName_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; uint8_t v___x_2805_; 
v___x_2738_ = lean_st_ref_get(v___y_2736_);
v_env_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc_ref(v_env_2739_);
lean_dec(v___x_2738_);
v_visibility_2740_ = lean_ctor_get_uint8(v_modifiers_2729_, sizeof(void*)*3);
v_isProtected_2741_ = lean_ctor_get_uint8(v_modifiers_2729_, sizeof(void*)*3 + 1);
v___x_2805_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_2739_, v_visibility_2740_);
lean_dec_ref(v_env_2739_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; lean_object* v_env_2807_; lean_object* v_declName_2808_; 
v___x_2806_ = lean_st_ref_get(v___y_2736_);
v_env_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc_ref(v_env_2807_);
lean_dec(v___x_2806_);
v_declName_2808_ = l_Lean_mkPrivateName(v_env_2807_, v_declName_2730_);
lean_dec_ref(v_env_2807_);
v_declName_2743_ = v_declName_2808_;
v___y_2744_ = v___y_2731_;
v___y_2745_ = v___y_2732_;
v___y_2746_ = v___y_2733_;
v___y_2747_ = v___y_2734_;
v___y_2748_ = v___y_2735_;
v___y_2749_ = v___y_2736_;
goto v___jp_2742_;
}
else
{
v_declName_2743_ = v_declName_2730_;
v___y_2744_ = v___y_2731_;
v___y_2745_ = v___y_2732_;
v___y_2746_ = v___y_2733_;
v___y_2747_ = v___y_2734_;
v___y_2748_ = v___y_2735_;
v___y_2749_ = v___y_2736_;
goto v___jp_2742_;
}
v___jp_2742_:
{
lean_object* v___x_2750_; 
lean_inc(v_declName_2743_);
v___x_2750_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2795_; 
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2795_ == 0)
{
lean_object* v_unused_2796_; 
v_unused_2796_ = lean_ctor_get(v___x_2750_, 0);
lean_dec(v_unused_2796_);
v___x_2752_ = v___x_2750_;
v_isShared_2753_ = v_isSharedCheck_2795_;
goto v_resetjp_2751_;
}
else
{
lean_dec(v___x_2750_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2795_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
if (v_isProtected_2741_ == 0)
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v_declName_2743_);
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_declName_2743_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
else
{
lean_object* v___x_2757_; lean_object* v_env_2758_; lean_object* v_nextMacroScope_2759_; lean_object* v_ngen_2760_; lean_object* v_auxDeclNGen_2761_; lean_object* v_traceState_2762_; lean_object* v_messages_2763_; lean_object* v_infoState_2764_; lean_object* v_snapshotTasks_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2793_; 
v___x_2757_ = lean_st_ref_take(v___y_2749_);
v_env_2758_ = lean_ctor_get(v___x_2757_, 0);
v_nextMacroScope_2759_ = lean_ctor_get(v___x_2757_, 1);
v_ngen_2760_ = lean_ctor_get(v___x_2757_, 2);
v_auxDeclNGen_2761_ = lean_ctor_get(v___x_2757_, 3);
v_traceState_2762_ = lean_ctor_get(v___x_2757_, 4);
v_messages_2763_ = lean_ctor_get(v___x_2757_, 6);
v_infoState_2764_ = lean_ctor_get(v___x_2757_, 7);
v_snapshotTasks_2765_ = lean_ctor_get(v___x_2757_, 8);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2793_ == 0)
{
lean_object* v_unused_2794_; 
v_unused_2794_ = lean_ctor_get(v___x_2757_, 5);
lean_dec(v_unused_2794_);
v___x_2767_ = v___x_2757_;
v_isShared_2768_ = v_isSharedCheck_2793_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_snapshotTasks_2765_);
lean_inc(v_infoState_2764_);
lean_inc(v_messages_2763_);
lean_inc(v_traceState_2762_);
lean_inc(v_auxDeclNGen_2761_);
lean_inc(v_ngen_2760_);
lean_inc(v_nextMacroScope_2759_);
lean_inc(v_env_2758_);
lean_dec(v___x_2757_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2793_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_inc(v_declName_2743_);
v___x_2769_ = l_Lean_addProtected(v_env_2758_, v_declName_2743_);
v___x_2770_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 5, v___x_2770_);
lean_ctor_set(v___x_2767_, 0, v___x_2769_);
v___x_2772_ = v___x_2767_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_nextMacroScope_2759_);
lean_ctor_set(v_reuseFailAlloc_2792_, 2, v_ngen_2760_);
lean_ctor_set(v_reuseFailAlloc_2792_, 3, v_auxDeclNGen_2761_);
lean_ctor_set(v_reuseFailAlloc_2792_, 4, v_traceState_2762_);
lean_ctor_set(v_reuseFailAlloc_2792_, 5, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2792_, 6, v_messages_2763_);
lean_ctor_set(v_reuseFailAlloc_2792_, 7, v_infoState_2764_);
lean_ctor_set(v_reuseFailAlloc_2792_, 8, v_snapshotTasks_2765_);
v___x_2772_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v_mctx_2775_; lean_object* v_zetaDeltaFVarIds_2776_; lean_object* v_postponed_2777_; lean_object* v_diag_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2790_; 
v___x_2773_ = lean_st_ref_set(v___y_2749_, v___x_2772_);
v___x_2774_ = lean_st_ref_take(v___y_2747_);
v_mctx_2775_ = lean_ctor_get(v___x_2774_, 0);
v_zetaDeltaFVarIds_2776_ = lean_ctor_get(v___x_2774_, 2);
v_postponed_2777_ = lean_ctor_get(v___x_2774_, 3);
v_diag_2778_ = lean_ctor_get(v___x_2774_, 4);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2790_ == 0)
{
lean_object* v_unused_2791_; 
v_unused_2791_ = lean_ctor_get(v___x_2774_, 1);
lean_dec(v_unused_2791_);
v___x_2780_ = v___x_2774_;
v_isShared_2781_ = v_isSharedCheck_2790_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_diag_2778_);
lean_inc(v_postponed_2777_);
lean_inc(v_zetaDeltaFVarIds_2776_);
lean_inc(v_mctx_2775_);
lean_dec(v___x_2774_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2790_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2782_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 1, v___x_2782_);
v___x_2784_ = v___x_2780_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_mctx_2775_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v___x_2782_);
lean_ctor_set(v_reuseFailAlloc_2789_, 2, v_zetaDeltaFVarIds_2776_);
lean_ctor_set(v_reuseFailAlloc_2789_, 3, v_postponed_2777_);
lean_ctor_set(v_reuseFailAlloc_2789_, 4, v_diag_2778_);
v___x_2784_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2785_ = lean_st_ref_set(v___y_2747_, v___x_2784_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v_declName_2743_);
v___x_2787_ = v___x_2752_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_declName_2743_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
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
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2804_; 
lean_dec(v_declName_2743_);
v_a_2797_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2799_ = v___x_2750_;
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2750_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2800_ == 0)
{
v___x_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2797_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4___boxed(lean_object* v_modifiers_2809_, lean_object* v_declName_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2809_, v_declName_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec_ref(v_modifiers_2809_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(lean_object* v_pre_2819_, lean_object* v_declName_2820_, lean_object* v_as_2821_, size_t v_sz_2822_, size_t v_i_2823_, lean_object* v_b_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v_a_2833_; uint8_t v___x_2837_; 
v___x_2837_ = lean_usize_dec_lt(v_i_2823_, v_sz_2822_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; 
lean_dec(v_declName_2820_);
lean_dec(v_pre_2819_);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v_b_2824_);
return v___x_2838_;
}
else
{
lean_object* v___x_2839_; lean_object* v_a_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2839_ = lean_box(0);
v_a_2840_ = lean_array_uget_borrowed(v_as_2821_, v_i_2823_);
lean_inc(v_a_2840_);
lean_inc(v_pre_2819_);
v___x_2841_ = l_Lean_Name_append(v_pre_2819_, v_a_2840_);
v___x_2842_ = lean_name_eq(v___x_2841_, v_declName_2820_);
lean_dec(v___x_2841_);
if (v___x_2842_ == 0)
{
v_a_2833_ = v___x_2839_;
goto v___jp_2832_;
}
else
{
lean_object* v___x_2843_; uint8_t v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2843_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_2844_ = 0;
lean_inc(v_declName_2820_);
v___x_2845_ = l_Lean_MessageData_ofConstName(v_declName_2820_, v___x_2844_);
v___x_2846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2843_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
v___x_2847_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_2848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2846_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
lean_inc(v_pre_2819_);
v___x_2849_ = l_Lean_MessageData_ofName(v_pre_2819_);
v___x_2850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2848_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
v___x_2851_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_2852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2850_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
lean_inc(v_a_2840_);
v___x_2853_ = l_Lean_MessageData_ofName(v_a_2840_);
v___x_2854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2852_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2856_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_dec_ref(v___x_2857_);
v_a_2833_ = v___x_2839_;
goto v___jp_2832_;
}
else
{
lean_dec(v_declName_2820_);
lean_dec(v_pre_2819_);
return v___x_2857_;
}
}
}
v___jp_2832_:
{
size_t v___x_2834_; size_t v___x_2835_; 
v___x_2834_ = ((size_t)1ULL);
v___x_2835_ = lean_usize_add(v_i_2823_, v___x_2834_);
v_i_2823_ = v___x_2835_;
v_b_2824_ = v_a_2833_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6___boxed(lean_object* v_pre_2858_, lean_object* v_declName_2859_, lean_object* v_as_2860_, lean_object* v_sz_2861_, lean_object* v_i_2862_, lean_object* v_b_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
size_t v_sz_boxed_2871_; size_t v_i_boxed_2872_; lean_object* v_res_2873_; 
v_sz_boxed_2871_ = lean_unbox_usize(v_sz_2861_);
lean_dec(v_sz_2861_);
v_i_boxed_2872_ = lean_unbox_usize(v_i_2862_);
lean_dec(v_i_2862_);
v_res_2873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2858_, v_declName_2859_, v_as_2860_, v_sz_boxed_2871_, v_i_boxed_2872_, v_b_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v_as_2860_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(lean_object* v_declName_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
if (lean_obj_tag(v_declName_2874_) == 1)
{
lean_object* v_pre_2882_; lean_object* v___x_2883_; lean_object* v_env_2884_; uint8_t v___x_2885_; 
v_pre_2882_ = lean_ctor_get(v_declName_2874_, 0);
lean_inc_n(v_pre_2882_, 2);
v___x_2883_ = lean_st_ref_get(v___y_2880_);
v_env_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc_ref(v_env_2884_);
lean_dec(v___x_2883_);
v___x_2885_ = l_Lean_isStructure(v_env_2884_, v_pre_2882_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
lean_dec_ref(v_declName_2874_);
lean_dec(v_pre_2882_);
v___x_2886_ = lean_box(0);
v___x_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
return v___x_2887_;
}
else
{
lean_object* v___x_2888_; lean_object* v_env_2889_; lean_object* v_fieldNames_2890_; lean_object* v___x_2891_; size_t v_sz_2892_; size_t v___x_2893_; lean_object* v___x_2894_; 
v___x_2888_ = lean_st_ref_get(v___y_2880_);
v_env_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc_ref(v_env_2889_);
lean_dec(v___x_2888_);
lean_inc(v_pre_2882_);
v_fieldNames_2890_ = l_Lean_getStructureFieldsFlattened(v_env_2889_, v_pre_2882_, v___x_2885_);
v___x_2891_ = lean_box(0);
v_sz_2892_ = lean_array_size(v_fieldNames_2890_);
v___x_2893_ = ((size_t)0ULL);
v___x_2894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2882_, v_declName_2874_, v_fieldNames_2890_, v_sz_2892_, v___x_2893_, v___x_2891_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec_ref(v_fieldNames_2890_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2901_ == 0)
{
lean_object* v_unused_2902_; 
v_unused_2902_ = lean_ctor_get(v___x_2894_, 0);
lean_dec(v_unused_2902_);
v___x_2896_ = v___x_2894_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_dec(v___x_2894_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2891_);
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2891_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
else
{
return v___x_2894_;
}
}
}
else
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
lean_dec(v_declName_2874_);
v___x_2903_ = lean_box(0);
v___x_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
return v___x_2904_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3___boxed(lean_object* v_declName_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v_declName_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(lean_object* v_currNamespace_2914_, lean_object* v_modifiers_2915_, lean_object* v_shortName_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2930_; lean_object* v_shortName_2931_; lean_object* v_currNamespace_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v_view_2992_; lean_object* v_name_2993_; lean_object* v_imported_2994_; lean_object* v_ctx_2995_; lean_object* v_scopes_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3054_; 
lean_inc(v_shortName_2916_);
v_view_2992_ = l_Lean_extractMacroScopes(v_shortName_2916_);
v_name_2993_ = lean_ctor_get(v_view_2992_, 0);
v_imported_2994_ = lean_ctor_get(v_view_2992_, 1);
v_ctx_2995_ = lean_ctor_get(v_view_2992_, 2);
v_scopes_2996_ = lean_ctor_get(v_view_2992_, 3);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_view_2992_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_2998_ = v_view_2992_;
v_isShared_2999_ = v_isSharedCheck_3054_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_scopes_2996_);
lean_inc(v_ctx_2995_);
lean_inc(v_imported_2994_);
lean_inc(v_name_2993_);
lean_dec(v_view_2992_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3054_;
goto v_resetjp_2997_;
}
v___jp_2924_:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___y_2926_);
lean_ctor_set(v___x_2927_, 1, v___y_2925_);
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
return v___x_2928_;
}
v___jp_2929_:
{
lean_object* v___x_2939_; 
lean_inc(v___y_2930_);
v___x_2939_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v___y_2930_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v___x_2940_; 
lean_dec_ref(v___x_2939_);
v___x_2940_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2915_, v___y_2930_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2940_) == 0)
{
uint8_t v_isProtected_2941_; 
v_isProtected_2941_ = lean_ctor_get_uint8(v_modifiers_2915_, sizeof(void*)*3 + 1);
if (v_isProtected_2941_ == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2950_; 
lean_dec(v_currNamespace_2932_);
v_a_2942_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2944_ = v___x_2940_;
v_isShared_2945_ = v_isSharedCheck_2950_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2940_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2950_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2946_, 0, v_a_2942_);
lean_ctor_set(v___x_2946_, 1, v_shortName_2931_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 0, v___x_2946_);
v___x_2948_ = v___x_2944_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
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
if (lean_obj_tag(v_currNamespace_2932_) == 1)
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2963_; 
v_a_2951_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2953_ = v___x_2940_;
v_isShared_2954_ = v_isSharedCheck_2963_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2940_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2963_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v_str_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2961_; 
v_str_2955_ = lean_ctor_get(v_currNamespace_2932_, 1);
lean_inc_ref(v_str_2955_);
lean_dec_ref(v_currNamespace_2932_);
v___x_2956_ = lean_box(0);
v___x_2957_ = l_Lean_Name_str___override(v___x_2956_, v_str_2955_);
v___x_2958_ = l_Lean_Name_append(v___x_2957_, v_shortName_2931_);
v___x_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2959_, 0, v_a_2951_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 0, v___x_2959_);
v___x_2961_ = v___x_2953_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
else
{
lean_object* v_a_2964_; uint8_t v___x_2965_; 
lean_dec(v_currNamespace_2932_);
v_a_2964_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2964_);
lean_dec_ref(v___x_2940_);
v___x_2965_ = l_Lean_Name_isAtomic(v_shortName_2931_);
if (v___x_2965_ == 0)
{
v___y_2925_ = v_shortName_2931_;
v___y_2926_ = v_a_2964_;
goto v___jp_2924_;
}
else
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec(v_a_2964_);
lean_dec(v_shortName_2931_);
v___x_2966_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_2967_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2966_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2967_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2967_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec(v_currNamespace_2932_);
lean_dec(v_shortName_2931_);
v_a_2976_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2940_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2940_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v_currNamespace_2932_);
lean_dec(v_shortName_2931_);
lean_dec(v___y_2930_);
v_a_2984_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2939_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2939_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
v_resetjp_2997_:
{
lean_object* v___x_3000_; uint8_t v_isRootName_3001_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; uint8_t v___x_3043_; 
v___x_3000_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_3001_ = l_Lean_Name_isPrefixOf(v___x_3000_, v_name_2993_);
v___x_3043_ = lean_name_eq(v_name_2993_, v___x_3000_);
if (v___x_3043_ == 0)
{
v___y_3030_ = v___y_2917_;
v___y_3031_ = v___y_2918_;
v___y_3032_ = v___y_2919_;
v___y_3033_ = v___y_2920_;
v___y_3034_ = v___y_2921_;
v___y_3035_ = v___y_2922_;
goto v___jp_3029_;
}
else
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_del_object(v___x_2998_);
lean_dec(v_scopes_2996_);
lean_dec(v_ctx_2995_);
lean_dec(v_imported_2994_);
lean_dec(v_name_2993_);
lean_dec(v_shortName_2916_);
lean_dec(v_currNamespace_2914_);
v___x_3044_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_3045_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3044_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3045_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
v___jp_3002_:
{
if (v_isRootName_3001_ == 0)
{
lean_dec(v_name_2993_);
v___y_2930_ = v___y_3009_;
v_shortName_2931_ = v_shortName_2916_;
v_currNamespace_2932_ = v_currNamespace_2914_;
v___y_2933_ = v___y_3008_;
v___y_2934_ = v___y_3003_;
v___y_2935_ = v___y_3005_;
v___y_2936_ = v___y_3007_;
v___y_2937_ = v___y_3006_;
v___y_2938_ = v___y_3004_;
goto v___jp_2929_;
}
else
{
lean_dec(v_shortName_2916_);
lean_dec(v_currNamespace_2914_);
if (lean_obj_tag(v_name_2993_) == 1)
{
lean_object* v_pre_3010_; lean_object* v_str_3011_; lean_object* v___x_3012_; lean_object* v_shortName_3013_; lean_object* v_currNamespace_3014_; 
v_pre_3010_ = lean_ctor_get(v_name_2993_, 0);
lean_inc(v_pre_3010_);
v_str_3011_ = lean_ctor_get(v_name_2993_, 1);
lean_inc_ref(v_str_3011_);
lean_dec_ref(v_name_2993_);
v___x_3012_ = lean_box(0);
v_shortName_3013_ = l_Lean_Name_str___override(v___x_3012_, v_str_3011_);
v_currNamespace_3014_ = l_Lean_Name_replacePrefix(v_pre_3010_, v___x_3000_, v___x_3012_);
v___y_2930_ = v___y_3009_;
v_shortName_2931_ = v_shortName_3013_;
v_currNamespace_2932_ = v_currNamespace_3014_;
v___y_2933_ = v___y_3008_;
v___y_2934_ = v___y_3003_;
v___y_2935_ = v___y_3005_;
v___y_2936_ = v___y_3007_;
v___y_2937_ = v___y_3006_;
v___y_2938_ = v___y_3004_;
goto v___jp_2929_;
}
else
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec(v___y_3009_);
v___x_3015_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_3016_ = l_Lean_MessageData_ofName(v_name_2993_);
v___x_3017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3015_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
v___x_3018_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_3019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3017_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3019_, v___y_3008_, v___y_3003_, v___y_3005_, v___y_3007_, v___y_3006_, v___y_3004_);
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3020_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3020_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
}
v___jp_3029_:
{
if (v_isRootName_3001_ == 0)
{
lean_object* v___x_3036_; 
lean_del_object(v___x_2998_);
lean_dec(v_scopes_2996_);
lean_dec(v_ctx_2995_);
lean_dec(v_imported_2994_);
lean_inc(v_shortName_2916_);
lean_inc(v_currNamespace_2914_);
v___x_3036_ = l_Lean_Name_append(v_currNamespace_2914_, v_shortName_2916_);
v___y_3003_ = v___y_3031_;
v___y_3004_ = v___y_3035_;
v___y_3005_ = v___y_3032_;
v___y_3006_ = v___y_3034_;
v___y_3007_ = v___y_3033_;
v___y_3008_ = v___y_3030_;
v___y_3009_ = v___x_3036_;
goto v___jp_3002_;
}
else
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; 
v___x_3037_ = lean_box(0);
lean_inc(v_name_2993_);
v___x_3038_ = l_Lean_Name_replacePrefix(v_name_2993_, v___x_3000_, v___x_3037_);
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 0, v___x_3038_);
v___x_3040_ = v___x_2998_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_imported_2994_);
lean_ctor_set(v_reuseFailAlloc_3042_, 2, v_ctx_2995_);
lean_ctor_set(v_reuseFailAlloc_3042_, 3, v_scopes_2996_);
v___x_3040_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Lean_MacroScopesView_review(v___x_3040_);
v___y_3003_ = v___y_3031_;
v___y_3004_ = v___y_3035_;
v___y_3005_ = v___y_3032_;
v___y_3006_ = v___y_3034_;
v___y_3007_ = v___y_3033_;
v___y_3008_ = v___y_3030_;
v___y_3009_ = v___x_3041_;
goto v___jp_3002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2___boxed(lean_object* v_currNamespace_3055_, lean_object* v_modifiers_3056_, lean_object* v_shortName_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3055_, v_modifiers_3056_, v_shortName_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec_ref(v_modifiers_3056_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(uint8_t v___x_3066_, lean_object* v_as_3067_, size_t v_i_3068_, size_t v_stop_3069_, lean_object* v_b_3070_){
_start:
{
lean_object* v___y_3072_; uint8_t v___x_3076_; 
v___x_3076_ = lean_usize_dec_eq(v_i_3068_, v_stop_3069_);
if (v___x_3076_ == 0)
{
lean_object* v_fst_3077_; uint8_t v___x_3078_; 
v_fst_3077_ = lean_ctor_get(v_b_3070_, 0);
v___x_3078_ = lean_unbox(v_fst_3077_);
if (v___x_3078_ == 0)
{
lean_object* v_snd_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3088_; 
v_snd_3079_ = lean_ctor_get(v_b_3070_, 1);
v_isSharedCheck_3088_ = !lean_is_exclusive(v_b_3070_);
if (v_isSharedCheck_3088_ == 0)
{
lean_object* v_unused_3089_; 
v_unused_3089_ = lean_ctor_get(v_b_3070_, 0);
lean_dec(v_unused_3089_);
v___x_3081_ = v_b_3070_;
v_isShared_3082_ = v_isSharedCheck_3088_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_snd_3079_);
lean_dec(v_b_3070_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3088_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
uint8_t v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3086_; 
v___x_3083_ = 1;
v___x_3084_ = lean_box(v___x_3083_);
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 0, v___x_3084_);
v___x_3086_ = v___x_3081_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3084_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_snd_3079_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
v___y_3072_ = v___x_3086_;
goto v___jp_3071_;
}
}
}
else
{
lean_object* v_snd_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3100_; 
v_snd_3090_ = lean_ctor_get(v_b_3070_, 1);
v_isSharedCheck_3100_ = !lean_is_exclusive(v_b_3070_);
if (v_isSharedCheck_3100_ == 0)
{
lean_object* v_unused_3101_; 
v_unused_3101_ = lean_ctor_get(v_b_3070_, 0);
lean_dec(v_unused_3101_);
v___x_3092_ = v_b_3070_;
v_isShared_3093_ = v_isSharedCheck_3100_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_snd_3090_);
lean_dec(v_b_3070_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3100_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3094_ = lean_array_uget_borrowed(v_as_3067_, v_i_3068_);
lean_inc(v___x_3094_);
v___x_3095_ = lean_array_push(v_snd_3090_, v___x_3094_);
v___x_3096_ = lean_box(v___x_3066_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 1, v___x_3095_);
lean_ctor_set(v___x_3092_, 0, v___x_3096_);
v___x_3098_ = v___x_3092_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v___x_3095_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
v___y_3072_ = v___x_3098_;
goto v___jp_3071_;
}
}
}
}
else
{
return v_b_3070_;
}
v___jp_3071_:
{
size_t v___x_3073_; size_t v___x_3074_; 
v___x_3073_ = ((size_t)1ULL);
v___x_3074_ = lean_usize_add(v_i_3068_, v___x_3073_);
v_i_3068_ = v___x_3074_;
v_b_3070_ = v___y_3072_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4___boxed(lean_object* v___x_3102_, lean_object* v_as_3103_, lean_object* v_i_3104_, lean_object* v_stop_3105_, lean_object* v_b_3106_){
_start:
{
uint8_t v___x_19313__boxed_3107_; size_t v_i_boxed_3108_; size_t v_stop_boxed_3109_; lean_object* v_res_3110_; 
v___x_19313__boxed_3107_ = lean_unbox(v___x_3102_);
v_i_boxed_3108_ = lean_unbox_usize(v_i_3104_);
lean_dec(v_i_3104_);
v_stop_boxed_3109_ = lean_unbox_usize(v_stop_3105_);
lean_dec(v_stop_3105_);
v_res_3110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_19313__boxed_3107_, v_as_3103_, v_i_boxed_3108_, v_stop_boxed_3109_, v_b_3106_);
lean_dec_ref(v_as_3103_);
return v_res_3110_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(lean_object* v_a_3111_, lean_object* v_x_3112_){
_start:
{
if (lean_obj_tag(v_x_3112_) == 0)
{
uint8_t v___x_3113_; 
v___x_3113_ = 0;
return v___x_3113_;
}
else
{
lean_object* v_head_3114_; lean_object* v_tail_3115_; uint8_t v___x_3116_; 
v_head_3114_ = lean_ctor_get(v_x_3112_, 0);
v_tail_3115_ = lean_ctor_get(v_x_3112_, 1);
v___x_3116_ = lean_name_eq(v_a_3111_, v_head_3114_);
if (v___x_3116_ == 0)
{
v_x_3112_ = v_tail_3115_;
goto _start;
}
else
{
return v___x_3116_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_expandDeclId_spec__0___boxed(lean_object* v_a_3118_, lean_object* v_x_3119_){
_start:
{
uint8_t v_res_3120_; lean_object* v_r_3121_; 
v_res_3120_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_a_3118_, v_x_3119_);
lean_dec(v_x_3119_);
lean_dec(v_a_3118_);
v_r_3121_ = lean_box(v_res_3120_);
return v_r_3121_;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = ((lean_object*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0));
v___x_3124_ = l_Lean_stringToMessageData(v___x_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(lean_object* v_u_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3133_ = lean_obj_once(&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1, &l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1);
v___x_3134_ = l_Lean_MessageData_ofName(v_u_3125_);
v___x_3135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3133_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_3137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3135_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v___x_3138_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3137_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___boxed(lean_object* v_u_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(lean_object* v_as_3148_, size_t v_i_3149_, size_t v_stop_3150_, lean_object* v_b_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_a_3160_; uint8_t v___x_3164_; 
v___x_3164_ = lean_usize_dec_eq(v_i_3149_, v_stop_3150_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; lean_object* v_id_3166_; uint8_t v___x_3167_; 
v___x_3165_ = lean_array_uget_borrowed(v_as_3148_, v_i_3149_);
v_id_3166_ = l_Lean_Syntax_getId(v___x_3165_);
v___x_3167_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_id_3166_, v_b_3151_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3168_; 
v___x_3168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3168_, 0, v_id_3166_);
lean_ctor_set(v___x_3168_, 1, v_b_3151_);
v_a_3160_ = v___x_3168_;
goto v___jp_3159_;
}
else
{
lean_object* v_fileName_3169_; lean_object* v_fileMap_3170_; lean_object* v_options_3171_; lean_object* v_currRecDepth_3172_; lean_object* v_maxRecDepth_3173_; lean_object* v_ref_3174_; lean_object* v_currNamespace_3175_; lean_object* v_openDecls_3176_; lean_object* v_initHeartbeats_3177_; lean_object* v_maxHeartbeats_3178_; lean_object* v_quotContext_3179_; lean_object* v_currMacroScope_3180_; uint8_t v_diag_3181_; lean_object* v_cancelTk_x3f_3182_; uint8_t v_suppressElabErrors_3183_; lean_object* v_inheritedTraceOptions_3184_; lean_object* v_ref_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_dec(v_b_3151_);
v_fileName_3169_ = lean_ctor_get(v___y_3156_, 0);
v_fileMap_3170_ = lean_ctor_get(v___y_3156_, 1);
v_options_3171_ = lean_ctor_get(v___y_3156_, 2);
v_currRecDepth_3172_ = lean_ctor_get(v___y_3156_, 3);
v_maxRecDepth_3173_ = lean_ctor_get(v___y_3156_, 4);
v_ref_3174_ = lean_ctor_get(v___y_3156_, 5);
v_currNamespace_3175_ = lean_ctor_get(v___y_3156_, 6);
v_openDecls_3176_ = lean_ctor_get(v___y_3156_, 7);
v_initHeartbeats_3177_ = lean_ctor_get(v___y_3156_, 8);
v_maxHeartbeats_3178_ = lean_ctor_get(v___y_3156_, 9);
v_quotContext_3179_ = lean_ctor_get(v___y_3156_, 10);
v_currMacroScope_3180_ = lean_ctor_get(v___y_3156_, 11);
v_diag_3181_ = lean_ctor_get_uint8(v___y_3156_, sizeof(void*)*14);
v_cancelTk_x3f_3182_ = lean_ctor_get(v___y_3156_, 12);
v_suppressElabErrors_3183_ = lean_ctor_get_uint8(v___y_3156_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3184_ = lean_ctor_get(v___y_3156_, 13);
v_ref_3185_ = l_Lean_replaceRef(v___x_3165_, v_ref_3174_);
lean_inc_ref(v_inheritedTraceOptions_3184_);
lean_inc(v_cancelTk_x3f_3182_);
lean_inc(v_currMacroScope_3180_);
lean_inc(v_quotContext_3179_);
lean_inc(v_maxHeartbeats_3178_);
lean_inc(v_initHeartbeats_3177_);
lean_inc(v_openDecls_3176_);
lean_inc(v_currNamespace_3175_);
lean_inc(v_maxRecDepth_3173_);
lean_inc(v_currRecDepth_3172_);
lean_inc_ref(v_options_3171_);
lean_inc_ref(v_fileMap_3170_);
lean_inc_ref(v_fileName_3169_);
v___x_3186_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3186_, 0, v_fileName_3169_);
lean_ctor_set(v___x_3186_, 1, v_fileMap_3170_);
lean_ctor_set(v___x_3186_, 2, v_options_3171_);
lean_ctor_set(v___x_3186_, 3, v_currRecDepth_3172_);
lean_ctor_set(v___x_3186_, 4, v_maxRecDepth_3173_);
lean_ctor_set(v___x_3186_, 5, v_ref_3185_);
lean_ctor_set(v___x_3186_, 6, v_currNamespace_3175_);
lean_ctor_set(v___x_3186_, 7, v_openDecls_3176_);
lean_ctor_set(v___x_3186_, 8, v_initHeartbeats_3177_);
lean_ctor_set(v___x_3186_, 9, v_maxHeartbeats_3178_);
lean_ctor_set(v___x_3186_, 10, v_quotContext_3179_);
lean_ctor_set(v___x_3186_, 11, v_currMacroScope_3180_);
lean_ctor_set(v___x_3186_, 12, v_cancelTk_x3f_3182_);
lean_ctor_set(v___x_3186_, 13, v_inheritedTraceOptions_3184_);
lean_ctor_set_uint8(v___x_3186_, sizeof(void*)*14, v_diag_3181_);
lean_ctor_set_uint8(v___x_3186_, sizeof(void*)*14 + 1, v_suppressElabErrors_3183_);
v___x_3187_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_id_3166_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___x_3186_, v___y_3157_);
lean_dec_ref(v___x_3186_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref(v___x_3187_);
v_a_3160_ = v_a_3188_;
goto v___jp_3159_;
}
else
{
return v___x_3187_;
}
}
}
else
{
lean_object* v___x_3189_; 
v___x_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3189_, 0, v_b_3151_);
return v___x_3189_;
}
v___jp_3159_:
{
size_t v___x_3161_; size_t v___x_3162_; 
v___x_3161_ = ((size_t)1ULL);
v___x_3162_ = lean_usize_add(v_i_3149_, v___x_3161_);
v_i_3149_ = v___x_3162_;
v_b_3151_ = v_a_3160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3___boxed(lean_object* v_as_3190_, lean_object* v_i_3191_, lean_object* v_stop_3192_, lean_object* v_b_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
size_t v_i_boxed_3201_; size_t v_stop_boxed_3202_; lean_object* v_res_3203_; 
v_i_boxed_3201_ = lean_unbox_usize(v_i_3191_);
lean_dec(v_i_3191_);
v_stop_boxed_3202_ = lean_unbox_usize(v_stop_3192_);
lean_dec(v_stop_3192_);
v_res_3203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v_as_3190_, v_i_boxed_3201_, v_stop_boxed_3202_, v_b_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec_ref(v_as_3190_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId(lean_object* v_currNamespace_3204_, lean_object* v_currLevelNames_3205_, lean_object* v_declId_3206_, lean_object* v_modifiers_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_){
_start:
{
lean_object* v___x_3215_; lean_object* v_fst_3216_; lean_object* v_snd_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3312_; 
v___x_3215_ = l_Lean_Elab_expandDeclIdCore(v_declId_3206_);
v_fst_3216_ = lean_ctor_get(v___x_3215_, 0);
v_snd_3217_ = lean_ctor_get(v___x_3215_, 1);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3219_ = v___x_3215_;
v_isShared_3220_ = v_isSharedCheck_3312_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_snd_3217_);
lean_inc(v_fst_3216_);
lean_dec(v___x_3215_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3312_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v_levelNames_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3269_; lean_object* v___y_3280_; uint8_t v___x_3291_; 
v___x_3291_ = l_Lean_Syntax_isNone(v_snd_3217_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; 
v___x_3292_ = lean_unsigned_to_nat(1u);
v___x_3293_ = l_Lean_Syntax_getArg(v_snd_3217_, v___x_3292_);
lean_dec(v_snd_3217_);
v___x_3294_ = l_Lean_Syntax_getArgs(v___x_3293_);
lean_dec(v___x_3293_);
v___x_3295_ = lean_unsigned_to_nat(0u);
v___x_3296_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__0));
v___x_3297_ = lean_array_get_size(v___x_3294_);
v___x_3298_ = lean_nat_dec_lt(v___x_3295_, v___x_3297_);
if (v___x_3298_ == 0)
{
lean_dec_ref(v___x_3294_);
lean_del_object(v___x_3219_);
v___y_3280_ = v___x_3296_;
goto v___jp_3279_;
}
else
{
lean_object* v___x_3299_; lean_object* v___x_3301_; 
v___x_3299_ = lean_box(v___x_3298_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 1, v___x_3296_);
lean_ctor_set(v___x_3219_, 0, v___x_3299_);
v___x_3301_ = v___x_3219_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3299_);
lean_ctor_set(v_reuseFailAlloc_3311_, 1, v___x_3296_);
v___x_3301_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
uint8_t v___x_3302_; 
v___x_3302_ = lean_nat_dec_le(v___x_3297_, v___x_3297_);
if (v___x_3302_ == 0)
{
if (v___x_3298_ == 0)
{
lean_dec_ref(v___x_3301_);
lean_dec_ref(v___x_3294_);
v___y_3280_ = v___x_3296_;
goto v___jp_3279_;
}
else
{
size_t v___x_3303_; size_t v___x_3304_; lean_object* v___x_3305_; lean_object* v_snd_3306_; 
v___x_3303_ = ((size_t)0ULL);
v___x_3304_ = lean_usize_of_nat(v___x_3297_);
v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3291_, v___x_3294_, v___x_3303_, v___x_3304_, v___x_3301_);
lean_dec_ref(v___x_3294_);
v_snd_3306_ = lean_ctor_get(v___x_3305_, 1);
lean_inc(v_snd_3306_);
lean_dec_ref(v___x_3305_);
v___y_3280_ = v_snd_3306_;
goto v___jp_3279_;
}
}
else
{
size_t v___x_3307_; size_t v___x_3308_; lean_object* v___x_3309_; lean_object* v_snd_3310_; 
v___x_3307_ = ((size_t)0ULL);
v___x_3308_ = lean_usize_of_nat(v___x_3297_);
v___x_3309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3291_, v___x_3294_, v___x_3307_, v___x_3308_, v___x_3301_);
lean_dec_ref(v___x_3294_);
v_snd_3310_ = lean_ctor_get(v___x_3309_, 1);
lean_inc(v_snd_3310_);
lean_dec_ref(v___x_3309_);
v___y_3280_ = v_snd_3310_;
goto v___jp_3279_;
}
}
}
}
else
{
lean_del_object(v___x_3219_);
lean_dec(v_snd_3217_);
v_levelNames_3222_ = v_currLevelNames_3205_;
v___y_3223_ = v_a_3208_;
v___y_3224_ = v_a_3209_;
v___y_3225_ = v_a_3210_;
v___y_3226_ = v_a_3211_;
v___y_3227_ = v_a_3212_;
v___y_3228_ = v_a_3213_;
goto v___jp_3221_;
}
v___jp_3221_:
{
lean_object* v_fileName_3229_; lean_object* v_fileMap_3230_; lean_object* v_options_3231_; lean_object* v_currRecDepth_3232_; lean_object* v_maxRecDepth_3233_; lean_object* v_ref_3234_; lean_object* v_currNamespace_3235_; lean_object* v_openDecls_3236_; lean_object* v_initHeartbeats_3237_; lean_object* v_maxHeartbeats_3238_; lean_object* v_quotContext_3239_; lean_object* v_currMacroScope_3240_; uint8_t v_diag_3241_; lean_object* v_cancelTk_x3f_3242_; uint8_t v_suppressElabErrors_3243_; lean_object* v_inheritedTraceOptions_3244_; lean_object* v_ref_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v_fileName_3229_ = lean_ctor_get(v___y_3227_, 0);
v_fileMap_3230_ = lean_ctor_get(v___y_3227_, 1);
v_options_3231_ = lean_ctor_get(v___y_3227_, 2);
v_currRecDepth_3232_ = lean_ctor_get(v___y_3227_, 3);
v_maxRecDepth_3233_ = lean_ctor_get(v___y_3227_, 4);
v_ref_3234_ = lean_ctor_get(v___y_3227_, 5);
v_currNamespace_3235_ = lean_ctor_get(v___y_3227_, 6);
v_openDecls_3236_ = lean_ctor_get(v___y_3227_, 7);
v_initHeartbeats_3237_ = lean_ctor_get(v___y_3227_, 8);
v_maxHeartbeats_3238_ = lean_ctor_get(v___y_3227_, 9);
v_quotContext_3239_ = lean_ctor_get(v___y_3227_, 10);
v_currMacroScope_3240_ = lean_ctor_get(v___y_3227_, 11);
v_diag_3241_ = lean_ctor_get_uint8(v___y_3227_, sizeof(void*)*14);
v_cancelTk_x3f_3242_ = lean_ctor_get(v___y_3227_, 12);
v_suppressElabErrors_3243_ = lean_ctor_get_uint8(v___y_3227_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3244_ = lean_ctor_get(v___y_3227_, 13);
v_ref_3245_ = l_Lean_replaceRef(v_declId_3206_, v_ref_3234_);
lean_inc_ref(v_inheritedTraceOptions_3244_);
lean_inc(v_cancelTk_x3f_3242_);
lean_inc(v_currMacroScope_3240_);
lean_inc(v_quotContext_3239_);
lean_inc(v_maxHeartbeats_3238_);
lean_inc(v_initHeartbeats_3237_);
lean_inc(v_openDecls_3236_);
lean_inc(v_currNamespace_3235_);
lean_inc(v_maxRecDepth_3233_);
lean_inc(v_currRecDepth_3232_);
lean_inc_ref(v_options_3231_);
lean_inc_ref(v_fileMap_3230_);
lean_inc_ref(v_fileName_3229_);
v___x_3246_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3246_, 0, v_fileName_3229_);
lean_ctor_set(v___x_3246_, 1, v_fileMap_3230_);
lean_ctor_set(v___x_3246_, 2, v_options_3231_);
lean_ctor_set(v___x_3246_, 3, v_currRecDepth_3232_);
lean_ctor_set(v___x_3246_, 4, v_maxRecDepth_3233_);
lean_ctor_set(v___x_3246_, 5, v_ref_3245_);
lean_ctor_set(v___x_3246_, 6, v_currNamespace_3235_);
lean_ctor_set(v___x_3246_, 7, v_openDecls_3236_);
lean_ctor_set(v___x_3246_, 8, v_initHeartbeats_3237_);
lean_ctor_set(v___x_3246_, 9, v_maxHeartbeats_3238_);
lean_ctor_set(v___x_3246_, 10, v_quotContext_3239_);
lean_ctor_set(v___x_3246_, 11, v_currMacroScope_3240_);
lean_ctor_set(v___x_3246_, 12, v_cancelTk_x3f_3242_);
lean_ctor_set(v___x_3246_, 13, v_inheritedTraceOptions_3244_);
lean_ctor_set_uint8(v___x_3246_, sizeof(void*)*14, v_diag_3241_);
lean_ctor_set_uint8(v___x_3246_, sizeof(void*)*14 + 1, v_suppressElabErrors_3243_);
v___x_3247_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3204_, v_modifiers_3207_, v_fst_3216_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___x_3246_, v___y_3228_);
lean_dec_ref(v___x_3246_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3259_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3250_ = v___x_3247_;
v_isShared_3251_ = v_isSharedCheck_3259_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3247_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3259_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v_fst_3252_; lean_object* v_snd_3253_; lean_object* v_docString_x3f_3254_; lean_object* v___x_3255_; lean_object* v___x_3257_; 
v_fst_3252_ = lean_ctor_get(v_a_3248_, 0);
lean_inc(v_fst_3252_);
v_snd_3253_ = lean_ctor_get(v_a_3248_, 1);
lean_inc(v_snd_3253_);
lean_dec(v_a_3248_);
v_docString_x3f_3254_ = lean_ctor_get(v_modifiers_3207_, 1);
lean_inc(v_docString_x3f_3254_);
v___x_3255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3255_, 0, v_snd_3253_);
lean_ctor_set(v___x_3255_, 1, v_fst_3252_);
lean_ctor_set(v___x_3255_, 2, v_levelNames_3222_);
lean_ctor_set(v___x_3255_, 3, v_docString_x3f_3254_);
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 0, v___x_3255_);
v___x_3257_ = v___x_3250_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec(v_levelNames_3222_);
v_a_3260_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3247_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3247_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
v___jp_3268_:
{
if (lean_obj_tag(v___y_3269_) == 0)
{
lean_object* v_a_3270_; 
v_a_3270_ = lean_ctor_get(v___y_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref(v___y_3269_);
v_levelNames_3222_ = v_a_3270_;
v___y_3223_ = v_a_3208_;
v___y_3224_ = v_a_3209_;
v___y_3225_ = v_a_3210_;
v___y_3226_ = v_a_3211_;
v___y_3227_ = v_a_3212_;
v___y_3228_ = v_a_3213_;
goto v___jp_3221_;
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec(v_fst_3216_);
lean_dec(v_currNamespace_3204_);
v_a_3271_ = lean_ctor_get(v___y_3269_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___y_3269_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___y_3269_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___y_3269_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
v___jp_3279_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; uint8_t v___x_3283_; 
v___x_3281_ = lean_unsigned_to_nat(0u);
v___x_3282_ = lean_array_get_size(v___y_3280_);
v___x_3283_ = lean_nat_dec_lt(v___x_3281_, v___x_3282_);
if (v___x_3283_ == 0)
{
lean_dec_ref(v___y_3280_);
v_levelNames_3222_ = v_currLevelNames_3205_;
v___y_3223_ = v_a_3208_;
v___y_3224_ = v_a_3209_;
v___y_3225_ = v_a_3210_;
v___y_3226_ = v_a_3211_;
v___y_3227_ = v_a_3212_;
v___y_3228_ = v_a_3213_;
goto v___jp_3221_;
}
else
{
uint8_t v___x_3284_; 
v___x_3284_ = lean_nat_dec_le(v___x_3282_, v___x_3282_);
if (v___x_3284_ == 0)
{
if (v___x_3283_ == 0)
{
lean_dec_ref(v___y_3280_);
v_levelNames_3222_ = v_currLevelNames_3205_;
v___y_3223_ = v_a_3208_;
v___y_3224_ = v_a_3209_;
v___y_3225_ = v_a_3210_;
v___y_3226_ = v_a_3211_;
v___y_3227_ = v_a_3212_;
v___y_3228_ = v_a_3213_;
goto v___jp_3221_;
}
else
{
size_t v___x_3285_; size_t v___x_3286_; lean_object* v___x_3287_; 
v___x_3285_ = ((size_t)0ULL);
v___x_3286_ = lean_usize_of_nat(v___x_3282_);
v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3280_, v___x_3285_, v___x_3286_, v_currLevelNames_3205_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_);
lean_dec_ref(v___y_3280_);
v___y_3269_ = v___x_3287_;
goto v___jp_3268_;
}
}
else
{
size_t v___x_3288_; size_t v___x_3289_; lean_object* v___x_3290_; 
v___x_3288_ = ((size_t)0ULL);
v___x_3289_ = lean_usize_of_nat(v___x_3282_);
v___x_3290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3280_, v___x_3288_, v___x_3289_, v_currLevelNames_3205_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_);
lean_dec_ref(v___y_3280_);
v___y_3269_ = v___x_3290_;
goto v___jp_3268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___boxed(lean_object* v_currNamespace_3313_, lean_object* v_currLevelNames_3314_, lean_object* v_declId_3315_, lean_object* v_modifiers_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_Elab_expandDeclId(v_currNamespace_3313_, v_currLevelNames_3314_, v_declId_3315_, v_modifiers_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
lean_dec(v_a_3322_);
lean_dec_ref(v_a_3321_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
lean_dec_ref(v_modifiers_3316_);
lean_dec(v_declId_3315_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(lean_object* v_00_u03b1_3325_, lean_object* v_u_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v___x_3334_; 
v___x_3334_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___boxed(lean_object* v_00_u03b1_3335_, lean_object* v_u_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(v_00_u03b1_3335_, v_u_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(lean_object* v_00_u03b1_3345_, lean_object* v_msg_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3355_, lean_object* v_msg_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(v_00_u03b1_3355_, v_msg_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(lean_object* v_msgData_3365_, lean_object* v_macroStack_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_3365_, v_macroStack_3366_, v___y_3371_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_3375_, lean_object* v_macroStack_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(v_msgData_3375_, v_macroStack_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(lean_object* v_t_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v___x_3393_; 
v___x_3393_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_3385_, v___y_3391_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___boxed(lean_object* v_t_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(v_t_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(lean_object* v_env_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_3403_, v___y_3407_, v___y_3409_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___boxed(lean_object* v_env_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(v_env_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(lean_object* v_00_u03b1_3421_, lean_object* v_env_3422_, lean_object* v_x_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v___x_3431_; 
v___x_3431_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_3422_, v_x_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3432_, lean_object* v_env_3433_, lean_object* v_x_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(v_00_u03b1_3432_, v_env_3433_, v_x_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(lean_object* v_00_u03b1_3443_, lean_object* v_constName_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___boxed(lean_object* v_00_u03b1_3453_, lean_object* v_constName_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(v_00_u03b1_3453_, v_constName_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(lean_object* v_00_u03b1_3463_, lean_object* v_ref_3464_, lean_object* v_constName_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
lean_object* v___x_3473_; 
v___x_3473_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_3464_, v_constName_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___boxed(lean_object* v_00_u03b1_3474_, lean_object* v_ref_3475_, lean_object* v_constName_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(v_00_u03b1_3474_, v_ref_3475_, v_constName_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v_ref_3475_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(lean_object* v_00_u03b1_3485_, lean_object* v_ref_3486_, lean_object* v_msg_3487_, lean_object* v_declHint_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v___x_3496_; 
v___x_3496_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_3486_, v_msg_3487_, v_declHint_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___boxed(lean_object* v_00_u03b1_3497_, lean_object* v_ref_3498_, lean_object* v_msg_3499_, lean_object* v_declHint_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(v_00_u03b1_3497_, v_ref_3498_, v_msg_3499_, v_declHint_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v_ref_3498_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(lean_object* v_msg_3509_, lean_object* v_declHint_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_3509_, v_declHint_3510_, v___y_3516_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___boxed(lean_object* v_msg_3519_, lean_object* v_declHint_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(v_msg_3519_, v_declHint_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(lean_object* v_00_u03b1_3529_, lean_object* v_ref_3530_, lean_object* v_msg_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_3530_, v_msg_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___boxed(lean_object* v_00_u03b1_3540_, lean_object* v_ref_3541_, lean_object* v_msg_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(v_00_u03b1_3540_, v_ref_3541_, v_msg_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v_ref_3541_);
return v_res_3550_;
}
}
lean_object* runtime_initialize_Lean_DocString_Add(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeclModifiers(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_DocString_Add(builtin);
if (lean_io_result_is_error(res)) return res;
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
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeclModifiers(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString_Add(builtin);
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
