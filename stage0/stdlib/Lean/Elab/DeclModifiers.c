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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
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
static const lean_ctor_object l_Lean_Elab_instInhabitedModifiers_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instInhabitedModifiers_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_array_object l_Lean_Elab_Modifiers_filterAttrs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Modifiers_filterAttrs___closed__0 = (const lean_object*)&l_Lean_Elab_Modifiers_filterAttrs___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object* v_modifiers_787_, lean_object* v_p_788_){
_start:
{
lean_object* v_stx_789_; lean_object* v_docString_x3f_790_; uint8_t v_visibility_791_; uint8_t v_isProtected_792_; uint8_t v_computeKind_793_; uint8_t v_recKind_794_; uint8_t v_isUnsafe_795_; lean_object* v_attrs_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_823_; 
v_stx_789_ = lean_ctor_get(v_modifiers_787_, 0);
v_docString_x3f_790_ = lean_ctor_get(v_modifiers_787_, 1);
v_visibility_791_ = lean_ctor_get_uint8(v_modifiers_787_, sizeof(void*)*3);
v_isProtected_792_ = lean_ctor_get_uint8(v_modifiers_787_, sizeof(void*)*3 + 1);
v_computeKind_793_ = lean_ctor_get_uint8(v_modifiers_787_, sizeof(void*)*3 + 2);
v_recKind_794_ = lean_ctor_get_uint8(v_modifiers_787_, sizeof(void*)*3 + 3);
v_isUnsafe_795_ = lean_ctor_get_uint8(v_modifiers_787_, sizeof(void*)*3 + 4);
v_attrs_796_ = lean_ctor_get(v_modifiers_787_, 2);
v_isSharedCheck_823_ = !lean_is_exclusive(v_modifiers_787_);
if (v_isSharedCheck_823_ == 0)
{
v___x_798_ = v_modifiers_787_;
v_isShared_799_ = v_isSharedCheck_823_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_attrs_796_);
lean_inc(v_docString_x3f_790_);
lean_inc(v_stx_789_);
lean_dec(v_modifiers_787_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_823_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_array_get_size(v_attrs_796_);
v___x_802_ = ((lean_object*)(l_Lean_Elab_Modifiers_filterAttrs___closed__0));
v___x_803_ = lean_nat_dec_lt(v___x_800_, v___x_801_);
if (v___x_803_ == 0)
{
lean_object* v___x_805_; 
lean_dec_ref(v_attrs_796_);
lean_dec_ref(v_p_788_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 2, v___x_802_);
v___x_805_ = v___x_798_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_stx_789_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_docString_x3f_790_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v___x_802_);
lean_ctor_set_uint8(v_reuseFailAlloc_806_, sizeof(void*)*3, v_visibility_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_806_, sizeof(void*)*3 + 1, v_isProtected_792_);
lean_ctor_set_uint8(v_reuseFailAlloc_806_, sizeof(void*)*3 + 2, v_computeKind_793_);
lean_ctor_set_uint8(v_reuseFailAlloc_806_, sizeof(void*)*3 + 3, v_recKind_794_);
lean_ctor_set_uint8(v_reuseFailAlloc_806_, sizeof(void*)*3 + 4, v_isUnsafe_795_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
else
{
uint8_t v___x_807_; 
v___x_807_ = lean_nat_dec_le(v___x_801_, v___x_801_);
if (v___x_807_ == 0)
{
if (v___x_803_ == 0)
{
lean_object* v___x_809_; 
lean_dec_ref(v_attrs_796_);
lean_dec_ref(v_p_788_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 2, v___x_802_);
v___x_809_ = v___x_798_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_stx_789_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_docString_x3f_790_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v___x_802_);
lean_ctor_set_uint8(v_reuseFailAlloc_810_, sizeof(void*)*3, v_visibility_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_810_, sizeof(void*)*3 + 1, v_isProtected_792_);
lean_ctor_set_uint8(v_reuseFailAlloc_810_, sizeof(void*)*3 + 2, v_computeKind_793_);
lean_ctor_set_uint8(v_reuseFailAlloc_810_, sizeof(void*)*3 + 3, v_recKind_794_);
lean_ctor_set_uint8(v_reuseFailAlloc_810_, sizeof(void*)*3 + 4, v_isUnsafe_795_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
size_t v___x_811_; size_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_811_ = ((size_t)0ULL);
v___x_812_ = lean_usize_of_nat(v___x_801_);
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_788_, v_attrs_796_, v___x_811_, v___x_812_, v___x_802_);
lean_dec_ref(v_attrs_796_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 2, v___x_813_);
v___x_815_ = v___x_798_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_stx_789_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_docString_x3f_790_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v___x_813_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, sizeof(void*)*3, v_visibility_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, sizeof(void*)*3 + 1, v_isProtected_792_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, sizeof(void*)*3 + 2, v_computeKind_793_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, sizeof(void*)*3 + 3, v_recKind_794_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, sizeof(void*)*3 + 4, v_isUnsafe_795_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
else
{
size_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_817_ = ((size_t)0ULL);
v___x_818_ = lean_usize_of_nat(v___x_801_);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_788_, v_attrs_796_, v___x_817_, v___x_818_, v___x_802_);
lean_dec_ref(v_attrs_796_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 2, v___x_819_);
v___x_821_ = v___x_798_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_stx_789_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_docString_x3f_790_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v___x_819_);
lean_ctor_set_uint8(v_reuseFailAlloc_822_, sizeof(void*)*3, v_visibility_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_822_, sizeof(void*)*3 + 1, v_isProtected_792_);
lean_ctor_set_uint8(v_reuseFailAlloc_822_, sizeof(void*)*3 + 2, v_computeKind_793_);
lean_ctor_set_uint8(v_reuseFailAlloc_822_, sizeof(void*)*3 + 3, v_recKind_794_);
lean_ctor_set_uint8(v_reuseFailAlloc_822_, sizeof(void*)*3 + 4, v_isUnsafe_795_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(lean_object* v_p_824_, lean_object* v_as_825_, size_t v_i_826_, size_t v_stop_827_){
_start:
{
uint8_t v___x_828_; 
v___x_828_ = lean_usize_dec_eq(v_i_826_, v_stop_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_829_ = lean_array_uget_borrowed(v_as_825_, v_i_826_);
lean_inc_ref(v_p_824_);
lean_inc(v___x_829_);
v___x_830_ = lean_apply_1(v_p_824_, v___x_829_);
v___x_831_ = lean_unbox(v___x_830_);
if (v___x_831_ == 0)
{
size_t v___x_832_; size_t v___x_833_; 
v___x_832_ = ((size_t)1ULL);
v___x_833_ = lean_usize_add(v_i_826_, v___x_832_);
v_i_826_ = v___x_833_;
goto _start;
}
else
{
uint8_t v___x_835_; 
lean_dec_ref(v_p_824_);
v___x_835_ = lean_unbox(v___x_830_);
return v___x_835_;
}
}
else
{
uint8_t v___x_836_; 
lean_dec_ref(v_p_824_);
v___x_836_ = 0;
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0___boxed(lean_object* v_p_837_, lean_object* v_as_838_, lean_object* v_i_839_, lean_object* v_stop_840_){
_start:
{
size_t v_i_boxed_841_; size_t v_stop_boxed_842_; uint8_t v_res_843_; lean_object* v_r_844_; 
v_i_boxed_841_ = lean_unbox_usize(v_i_839_);
lean_dec(v_i_839_);
v_stop_boxed_842_ = lean_unbox_usize(v_stop_840_);
lean_dec(v_stop_840_);
v_res_843_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_837_, v_as_838_, v_i_boxed_841_, v_stop_boxed_842_);
lean_dec_ref(v_as_838_);
v_r_844_ = lean_box(v_res_843_);
return v_r_844_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_anyAttr(lean_object* v_modifiers_845_, lean_object* v_p_846_){
_start:
{
lean_object* v_attrs_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v_attrs_847_ = lean_ctor_get(v_modifiers_845_, 2);
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_array_get_size(v_attrs_847_);
v___x_850_ = lean_nat_dec_lt(v___x_848_, v___x_849_);
if (v___x_850_ == 0)
{
lean_dec_ref(v_p_846_);
return v___x_850_;
}
else
{
if (v___x_850_ == 0)
{
lean_dec_ref(v_p_846_);
return v___x_850_;
}
else
{
size_t v___x_851_; size_t v___x_852_; uint8_t v___x_853_; 
v___x_851_ = ((size_t)0ULL);
v___x_852_ = lean_usize_of_nat(v___x_849_);
v___x_853_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_846_, v_attrs_847_, v___x_851_, v___x_852_);
return v___x_853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_anyAttr___boxed(lean_object* v_modifiers_854_, lean_object* v_p_855_){
_start:
{
uint8_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l_Lean_Elab_Modifiers_anyAttr(v_modifiers_854_, v_p_855_);
lean_dec_ref(v_modifiers_854_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__0));
v___x_861_ = lean_string_length(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__2, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__2_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2);
v___x_863_ = lean_nat_to_int(v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__0(lean_object* v_attr_871_){
_start:
{
uint8_t v_kind_872_; lean_object* v_name_873_; lean_object* v_stx_874_; lean_object* v___y_876_; 
v_kind_872_ = lean_ctor_get_uint8(v_attr_871_, sizeof(void*)*2);
v_name_873_ = lean_ctor_get(v_attr_871_, 0);
lean_inc(v_name_873_);
v_stx_874_ = lean_ctor_get(v_attr_871_, 1);
lean_inc(v_stx_874_);
lean_dec_ref(v_attr_871_);
switch(v_kind_872_)
{
case 0:
{
lean_object* v___x_898_; 
v___x_898_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__6));
v___y_876_ = v___x_898_;
goto v___jp_875_;
}
case 1:
{
lean_object* v___x_899_; 
v___x_899_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__7));
v___y_876_ = v___x_899_;
goto v___jp_875_;
}
default: 
{
lean_object* v___x_900_; 
v___x_900_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__8));
v___y_876_ = v___x_900_;
goto v___jp_875_;
}
}
v___jp_875_:
{
lean_object* v___x_877_; uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; 
lean_inc_ref(v___y_876_);
v___x_877_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_877_, 0, v___y_876_);
v___x_878_ = 1;
v___x_879_ = l_Lean_Name_toString(v_name_873_, v___x_878_);
v___x_880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
v___x_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_877_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_box(0);
v___x_883_ = 0;
v___x_884_ = l_Lean_Syntax_formatStx(v_stx_874_, v___x_882_, v___x_883_);
v___x_885_ = l_Std_Format_defWidth;
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = l_Std_Format_pretty(v___x_884_, v___x_885_, v___x_886_, v___x_886_);
v___x_888_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
v___x_889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_881_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__3, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__3_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3);
v___x_891_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__4));
v___x_892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set(v___x_892_, 1, v___x_889_);
v___x_893_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__5));
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_890_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = 0;
v___x_897_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*1, v___x_896_);
return v___x_897_;
}
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__0));
v___x_910_ = lean_string_length(v___x_909_);
return v___x_910_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__5, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__5_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5);
v___x_912_ = lean_nat_to_int(v___x_911_);
return v___x_912_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__35(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__33));
v___x_969_ = lean_string_length(v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__36(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__35, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__35_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__35);
v___x_971_ = lean_nat_to_int(v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__1(lean_object* v___f_981_, lean_object* v___f_982_, lean_object* v_m_983_){
_start:
{
lean_object* v_docString_x3f_984_; uint8_t v_visibility_985_; uint8_t v_isProtected_986_; uint8_t v_computeKind_987_; uint8_t v_recKind_988_; uint8_t v_isUnsafe_989_; lean_object* v_attrs_990_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1036_; 
v_docString_x3f_984_ = lean_ctor_get(v_m_983_, 1);
lean_inc(v_docString_x3f_984_);
v_visibility_985_ = lean_ctor_get_uint8(v_m_983_, sizeof(void*)*3);
v_isProtected_986_ = lean_ctor_get_uint8(v_m_983_, sizeof(void*)*3 + 1);
v_computeKind_987_ = lean_ctor_get_uint8(v_m_983_, sizeof(void*)*3 + 2);
v_recKind_988_ = lean_ctor_get_uint8(v_m_983_, sizeof(void*)*3 + 3);
v_isUnsafe_989_ = lean_ctor_get_uint8(v_m_983_, sizeof(void*)*3 + 4);
v_attrs_990_ = lean_ctor_get(v_m_983_, 2);
lean_inc_ref(v_attrs_990_);
lean_dec_ref(v_m_983_);
if (lean_obj_tag(v_docString_x3f_984_) == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_box(0);
v___y_1036_ = v___x_1040_;
goto v___jp_1035_;
}
else
{
lean_object* v_val_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1083_; 
v_val_1041_ = lean_ctor_get(v_docString_x3f_984_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_docString_x3f_984_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1043_ = v_docString_x3f_984_;
v_isShared_1044_ = v_isSharedCheck_1083_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_val_1041_);
lean_dec(v_docString_x3f_984_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1083_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1082_; 
v_fst_1045_ = lean_ctor_get(v_val_1041_, 0);
v_snd_1046_ = lean_ctor_get(v_val_1041_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_val_1041_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1048_ = v_val_1041_;
v_isShared_1049_ = v_isSharedCheck_1082_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_snd_1046_);
lean_inc(v_fst_1045_);
lean_dec(v_val_1041_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1082_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1050_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__32));
v___x_1051_ = lean_box(0);
v___x_1052_ = 0;
v___x_1053_ = l_Lean_Syntax_formatStx(v_fst_1045_, v___x_1051_, v___x_1052_);
v___x_1054_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__2));
if (v_isShared_1049_ == 0)
{
lean_ctor_set_tag(v___x_1048_, 5);
lean_ctor_set(v___x_1048_, 1, v___x_1054_);
lean_ctor_set(v___x_1048_, 0, v___x_1053_);
v___x_1056_ = v___x_1048_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___y_1060_; uint8_t v___x_1078_; 
v___x_1057_ = lean_box(1);
v___x_1058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1078_ = lean_unbox(v_snd_1046_);
lean_dec(v_snd_1046_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
v___x_1079_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__41));
v___y_1060_ = v___x_1079_;
goto v___jp_1059_;
}
else
{
lean_object* v___x_1080_; 
v___x_1080_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__42));
v___y_1060_ = v___x_1080_;
goto v___jp_1059_;
}
v___jp_1059_:
{
lean_object* v___x_1062_; 
lean_inc_ref(v___y_1060_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 3);
lean_ctor_set(v___x_1043_, 0, v___y_1060_);
v___x_1062_ = v___x_1043_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___y_1060_);
v___x_1062_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1058_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__36, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__36_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__36);
v___x_1065_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__37));
v___x_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v___x_1063_);
v___x_1067_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__38));
v___x_1068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1064_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = 0;
v___x_1071_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*1, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1050_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__40));
v___x_1074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___y_1036_ = v___x_1076_;
goto v___jp_1035_;
}
}
}
}
}
}
v___jp_991_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v_components_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; 
lean_inc(v___y_993_);
v___x_994_ = l_List_appendTR___redArg(v___y_992_, v___y_993_);
v___x_995_ = lean_array_to_list(v_attrs_990_);
v___x_996_ = lean_box(0);
v___x_997_ = l_List_mapTR_loop___redArg(v___f_981_, v___x_995_, v___x_996_);
v_components_998_ = l_List_appendTR___redArg(v___x_994_, v___x_997_);
v___x_999_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__3));
v___x_1000_ = l_Std_Format_joinSep___redArg(v___f_982_, v_components_998_, v___x_999_);
v___x_1001_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__6, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__6_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6);
v___x_1002_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__7));
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_1000_);
v___x_1004_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__8));
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1001_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = 0;
v___x_1008_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*1, v___x_1007_);
return v___x_1008_;
}
v___jp_1009_:
{
lean_object* v___x_1012_; 
lean_inc(v___y_1011_);
v___x_1012_ = l_List_appendTR___redArg(v___y_1010_, v___y_1011_);
if (v_isUnsafe_989_ == 0)
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_box(0);
v___y_992_ = v___x_1012_;
v___y_993_ = v___x_1013_;
goto v___jp_991_;
}
else
{
lean_object* v___x_1014_; 
v___x_1014_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__11));
v___y_992_ = v___x_1012_;
v___y_993_ = v___x_1014_;
goto v___jp_991_;
}
}
v___jp_1015_:
{
lean_object* v___x_1018_; 
lean_inc(v___y_1017_);
v___x_1018_ = l_List_appendTR___redArg(v___y_1016_, v___y_1017_);
switch(v_recKind_988_)
{
case 0:
{
lean_object* v___x_1019_; 
v___x_1019_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__14));
v___y_1010_ = v___x_1018_;
v___y_1011_ = v___x_1019_;
goto v___jp_1009_;
}
case 1:
{
lean_object* v___x_1020_; 
v___x_1020_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__17));
v___y_1010_ = v___x_1018_;
v___y_1011_ = v___x_1020_;
goto v___jp_1009_;
}
default: 
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_box(0);
v___y_1010_ = v___x_1018_;
v___y_1011_ = v___x_1021_;
goto v___jp_1009_;
}
}
}
v___jp_1022_:
{
lean_object* v___x_1025_; 
lean_inc(v___y_1024_);
v___x_1025_ = l_List_appendTR___redArg(v___y_1023_, v___y_1024_);
switch(v_computeKind_987_)
{
case 0:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_box(0);
v___y_1016_ = v___x_1025_;
v___y_1017_ = v___x_1026_;
goto v___jp_1015_;
}
case 1:
{
lean_object* v___x_1027_; 
v___x_1027_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__20));
v___y_1016_ = v___x_1025_;
v___y_1017_ = v___x_1027_;
goto v___jp_1015_;
}
default: 
{
lean_object* v___x_1028_; 
v___x_1028_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__23));
v___y_1016_ = v___x_1025_;
v___y_1017_ = v___x_1028_;
goto v___jp_1015_;
}
}
}
v___jp_1029_:
{
lean_object* v___x_1032_; 
lean_inc(v___y_1031_);
v___x_1032_ = l_List_appendTR___redArg(v___y_1030_, v___y_1031_);
if (v_isProtected_986_ == 0)
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_box(0);
v___y_1023_ = v___x_1032_;
v___y_1024_ = v___x_1033_;
goto v___jp_1022_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__26));
v___y_1023_ = v___x_1032_;
v___y_1024_ = v___x_1034_;
goto v___jp_1022_;
}
}
v___jp_1035_:
{
switch(v_visibility_985_)
{
case 0:
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_box(0);
v___y_1030_ = v___y_1036_;
v___y_1031_ = v___x_1037_;
goto v___jp_1029_;
}
case 1:
{
lean_object* v___x_1038_; 
v___x_1038_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__28));
v___y_1030_ = v___y_1036_;
v___y_1031_ = v___x_1038_;
goto v___jp_1029_;
}
default: 
{
lean_object* v___x_1039_; 
v___x_1039_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__30));
v___y_1030_ = v___y_1036_;
v___y_1031_ = v___x_1039_;
goto v___jp_1029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lam__0(lean_object* v_f_1090_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = l_Std_Format_defWidth;
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = l_Std_Format_pretty(v_f_1090_, v___x_1091_, v___x_1092_, v___x_1092_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg(lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_optDocComment_1104_){
_start:
{
lean_object* v_toApplicative_1105_; lean_object* v_toPure_1106_; lean_object* v___x_1107_; 
v_toApplicative_1105_ = lean_ctor_get(v_inst_1102_, 0);
v_toPure_1106_ = lean_ctor_get(v_toApplicative_1105_, 1);
v___x_1107_ = l_Lean_Syntax_getOptional_x3f(v_optDocComment_1104_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_inc(v_toPure_1106_);
lean_dec_ref(v_inst_1103_);
lean_dec_ref(v_inst_1102_);
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_apply_2(v_toPure_1106_, lean_box(0), v___x_1108_);
return v___x_1109_;
}
else
{
lean_object* v_val_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1131_; 
v_val_1110_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1112_ = v___x_1107_;
v_isShared_1113_ = v_isSharedCheck_1131_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_val_1110_);
lean_dec(v___x_1107_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1131_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_unsigned_to_nat(1u);
v___x_1115_ = l_Lean_Syntax_getArg(v_val_1110_, v___x_1114_);
if (lean_obj_tag(v___x_1115_) == 2)
{
lean_object* v_val_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
lean_inc(v_toPure_1106_);
lean_dec(v_val_1110_);
lean_dec_ref(v_inst_1103_);
lean_dec_ref(v_inst_1102_);
v_val_1116_ = lean_ctor_get(v___x_1115_, 1);
lean_inc_ref(v_val_1116_);
lean_dec_ref(v___x_1115_);
v___x_1117_ = lean_unsigned_to_nat(0u);
v___x_1118_ = lean_string_utf8_byte_size(v_val_1116_);
v___x_1119_ = lean_unsigned_to_nat(2u);
v___x_1120_ = lean_nat_sub(v___x_1118_, v___x_1119_);
v___x_1121_ = lean_string_utf8_extract(v_val_1116_, v___x_1117_, v___x_1120_);
lean_dec(v___x_1120_);
lean_dec_ref(v_val_1116_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1121_);
v___x_1123_ = v___x_1112_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_apply_2(v_toPure_1106_, lean_box(0), v___x_1123_);
return v___x_1124_;
}
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_del_object(v___x_1112_);
v___x_1126_ = lean_obj_once(&l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1, &l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1_once, _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1);
v___x_1127_ = l_Lean_MessageData_ofSyntax(v___x_1115_);
v___x_1128_ = l_Lean_indentD(v___x_1127_);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1126_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = l_Lean_throwErrorAt___redArg(v_inst_1102_, v_inst_1103_, v_val_1110_, v___x_1129_);
return v___x_1130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___boxed(lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_optDocComment_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1132_, v_inst_1133_, v_optDocComment_1134_);
lean_dec(v_optDocComment_1134_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f(lean_object* v_m_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_optDocComment_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1137_, v_inst_1138_, v_optDocComment_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___boxed(lean_object* v_m_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_optDocComment_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_Elab_expandOptDocComment_x3f(v_m_1141_, v_inst_1142_, v_inst_1143_, v_optDocComment_1144_);
lean_dec(v_optDocComment_1144_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0(lean_object* v_stx_1146_, lean_object* v___y_1147_, uint8_t v_visibility_1148_, uint8_t v___y_1149_, uint8_t v___y_1150_, uint8_t v___y_1151_, lean_object* v_toPure_1152_, lean_object* v_unsafeStx_1153_, lean_object* v_attrs_1154_){
_start:
{
uint8_t v___y_1156_; uint8_t v___x_1159_; 
v___x_1159_ = l_Lean_Syntax_isNone(v_unsafeStx_1153_);
if (v___x_1159_ == 0)
{
uint8_t v___x_1160_; 
v___x_1160_ = 1;
v___y_1156_ = v___x_1160_;
goto v___jp_1155_;
}
else
{
uint8_t v___x_1161_; 
v___x_1161_ = 0;
v___y_1156_ = v___x_1161_;
goto v___jp_1155_;
}
v___jp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1157_, 0, v_stx_1146_);
lean_ctor_set(v___x_1157_, 1, v___y_1147_);
lean_ctor_set(v___x_1157_, 2, v_attrs_1154_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*3, v_visibility_1148_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*3 + 1, v___y_1149_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*3 + 2, v___y_1150_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*3 + 3, v___y_1151_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*3 + 4, v___y_1156_);
v___x_1158_ = lean_apply_2(v_toPure_1152_, lean_box(0), v___x_1157_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0___boxed(lean_object* v_stx_1162_, lean_object* v___y_1163_, lean_object* v_visibility_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v_toPure_1168_, lean_object* v_unsafeStx_1169_, lean_object* v_attrs_1170_){
_start:
{
uint8_t v_visibility_boxed_1171_; uint8_t v___y_482__boxed_1172_; uint8_t v___y_483__boxed_1173_; uint8_t v___y_484__boxed_1174_; lean_object* v_res_1175_; 
v_visibility_boxed_1171_ = lean_unbox(v_visibility_1164_);
v___y_482__boxed_1172_ = lean_unbox(v___y_1165_);
v___y_483__boxed_1173_ = lean_unbox(v___y_1166_);
v___y_484__boxed_1174_ = lean_unbox(v___y_1167_);
v_res_1175_ = l_Lean_Elab_elabModifiers___redArg___lam__0(v_stx_1162_, v___y_1163_, v_visibility_boxed_1171_, v___y_482__boxed_1172_, v___y_483__boxed_1173_, v___y_484__boxed_1174_, v_toPure_1168_, v_unsafeStx_1169_, v_attrs_1170_);
lean_dec(v_unsafeStx_1169_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__1(lean_object* v___f_1176_, lean_object* v_attrs_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_apply_1(v___f_1176_, v_attrs_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3(lean_object* v_stx_1179_, lean_object* v___y_1180_, uint8_t v___y_1181_, uint8_t v___y_1182_, lean_object* v_toPure_1183_, lean_object* v_unsafeStx_1184_, lean_object* v_attrsStx_1185_, lean_object* v___x_1186_, lean_object* v_toBind_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_protectedStx_1200_, uint8_t v_visibility_1201_){
_start:
{
uint8_t v___y_1203_; uint8_t v___x_1218_; 
v___x_1218_ = l_Lean_Syntax_isNone(v_protectedStx_1200_);
if (v___x_1218_ == 0)
{
uint8_t v___x_1219_; 
v___x_1219_ = 1;
v___y_1203_ = v___x_1219_;
goto v___jp_1202_;
}
else
{
uint8_t v___x_1220_; 
v___x_1220_ = 0;
v___y_1203_ = v___x_1220_;
goto v___jp_1202_;
}
v___jp_1202_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; 
v___x_1204_ = lean_box(v_visibility_1201_);
v___x_1205_ = lean_box(v___y_1203_);
v___x_1206_ = lean_box(v___y_1181_);
v___x_1207_ = lean_box(v___y_1182_);
lean_inc(v_toPure_1183_);
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_1208_, 0, v_stx_1179_);
lean_closure_set(v___f_1208_, 1, v___y_1180_);
lean_closure_set(v___f_1208_, 2, v___x_1204_);
lean_closure_set(v___f_1208_, 3, v___x_1205_);
lean_closure_set(v___f_1208_, 4, v___x_1206_);
lean_closure_set(v___f_1208_, 5, v___x_1207_);
lean_closure_set(v___f_1208_, 6, v_toPure_1183_);
lean_closure_set(v___f_1208_, 7, v_unsafeStx_1184_);
v___x_1209_ = l_Lean_Syntax_getOptional_x3f(v_attrsStx_1185_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v___f_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
lean_dec(v_inst_1199_);
lean_dec(v_inst_1198_);
lean_dec_ref(v_inst_1197_);
lean_dec(v_inst_1196_);
lean_dec(v_inst_1195_);
lean_dec_ref(v_inst_1194_);
lean_dec_ref(v_inst_1193_);
lean_dec_ref(v_inst_1192_);
lean_dec_ref(v_inst_1191_);
lean_dec_ref(v_inst_1190_);
lean_dec_ref(v_inst_1189_);
lean_dec_ref(v_inst_1188_);
v___f_1210_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1210_, 0, v___f_1208_);
v___x_1211_ = lean_mk_empty_array_with_capacity(v___x_1186_);
v___x_1212_ = lean_apply_2(v_toPure_1183_, lean_box(0), v___x_1211_);
v___x_1213_ = lean_apply_4(v_toBind_1187_, lean_box(0), lean_box(0), v___x_1212_, v___f_1210_);
return v___x_1213_;
}
else
{
lean_object* v_val_1214_; lean_object* v___f_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec(v_toPure_1183_);
v_val_1214_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_val_1214_);
lean_dec_ref(v___x_1209_);
v___f_1215_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1215_, 0, v___f_1208_);
v___x_1216_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_1188_, v_inst_1189_, v_inst_1190_, v_inst_1191_, v_inst_1192_, v_inst_1193_, v_inst_1194_, v_inst_1195_, v_inst_1196_, v_inst_1197_, v_inst_1198_, v_inst_1199_, v_val_1214_);
lean_dec(v_val_1214_);
v___x_1217_ = lean_apply_4(v_toBind_1187_, lean_box(0), lean_box(0), v___x_1216_, v___f_1215_);
return v___x_1217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_stx_1221_ = _args[0];
lean_object* v___y_1222_ = _args[1];
lean_object* v___y_1223_ = _args[2];
lean_object* v___y_1224_ = _args[3];
lean_object* v_toPure_1225_ = _args[4];
lean_object* v_unsafeStx_1226_ = _args[5];
lean_object* v_attrsStx_1227_ = _args[6];
lean_object* v___x_1228_ = _args[7];
lean_object* v_toBind_1229_ = _args[8];
lean_object* v_inst_1230_ = _args[9];
lean_object* v_inst_1231_ = _args[10];
lean_object* v_inst_1232_ = _args[11];
lean_object* v_inst_1233_ = _args[12];
lean_object* v_inst_1234_ = _args[13];
lean_object* v_inst_1235_ = _args[14];
lean_object* v_inst_1236_ = _args[15];
lean_object* v_inst_1237_ = _args[16];
lean_object* v_inst_1238_ = _args[17];
lean_object* v_inst_1239_ = _args[18];
lean_object* v_inst_1240_ = _args[19];
lean_object* v_inst_1241_ = _args[20];
lean_object* v_protectedStx_1242_ = _args[21];
lean_object* v_visibility_1243_ = _args[22];
_start:
{
uint8_t v___y_512__boxed_1244_; uint8_t v___y_513__boxed_1245_; uint8_t v_visibility_boxed_1246_; lean_object* v_res_1247_; 
v___y_512__boxed_1244_ = lean_unbox(v___y_1223_);
v___y_513__boxed_1245_ = lean_unbox(v___y_1224_);
v_visibility_boxed_1246_ = lean_unbox(v_visibility_1243_);
v_res_1247_ = l_Lean_Elab_elabModifiers___redArg___lam__3(v_stx_1221_, v___y_1222_, v___y_512__boxed_1244_, v___y_513__boxed_1245_, v_toPure_1225_, v_unsafeStx_1226_, v_attrsStx_1227_, v___x_1228_, v_toBind_1229_, v_inst_1230_, v_inst_1231_, v_inst_1232_, v_inst_1233_, v_inst_1234_, v_inst_1235_, v_inst_1236_, v_inst_1237_, v_inst_1238_, v_inst_1239_, v_inst_1240_, v_inst_1241_, v_protectedStx_1242_, v_visibility_boxed_1246_);
lean_dec(v_protectedStx_1242_);
lean_dec(v___x_1228_);
lean_dec(v_attrsStx_1227_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2(lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_toBind_1250_, lean_object* v_stx_1251_, uint8_t v___y_1252_, uint8_t v___y_1253_, lean_object* v_toPure_1254_, lean_object* v_unsafeStx_1255_, lean_object* v_attrsStx_1256_, lean_object* v___x_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_protectedStx_1268_, lean_object* v_visibilityStx_1269_, lean_object* v_docCommentStx_1270_, lean_object* v___x_1271_, lean_object* v_____do__lift_1272_){
_start:
{
lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1279_; lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Syntax_getOptional_x3f(v_docCommentStx_1270_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v___x_1294_; 
lean_dec_ref(v___x_1271_);
v___x_1294_ = lean_box(0);
v___y_1279_ = v___x_1294_;
goto v___jp_1278_;
}
else
{
lean_object* v_val_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1305_; 
v_val_1295_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1297_ = v___x_1293_;
v_isShared_1298_ = v_isSharedCheck_1305_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_val_1295_);
lean_dec(v___x_1293_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1305_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1299_ = l_Lean_doc_verso;
v___x_1300_ = l_Lean_Option_get___redArg(v___x_1271_, v_____do__lift_1272_, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v_val_1295_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1301_);
v___x_1303_ = v___x_1297_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
v___y_1279_ = v___x_1303_;
goto v___jp_1278_;
}
}
}
v___jp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = l_Lean_Elab_elabVisibility___redArg(v_inst_1248_, v_inst_1249_, v___y_1275_);
v___x_1277_ = lean_apply_4(v_toBind_1250_, lean_box(0), lean_box(0), v___x_1276_, v___y_1274_);
return v___x_1277_;
}
v___jp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___f_1282_; lean_object* v___x_1283_; 
v___x_1280_ = lean_box(v___y_1252_);
v___x_1281_ = lean_box(v___y_1253_);
lean_inc_ref(v_inst_1249_);
lean_inc_ref(v_inst_1248_);
lean_inc(v_toBind_1250_);
v___f_1282_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__3___boxed), 23, 22);
lean_closure_set(v___f_1282_, 0, v_stx_1251_);
lean_closure_set(v___f_1282_, 1, v___y_1279_);
lean_closure_set(v___f_1282_, 2, v___x_1280_);
lean_closure_set(v___f_1282_, 3, v___x_1281_);
lean_closure_set(v___f_1282_, 4, v_toPure_1254_);
lean_closure_set(v___f_1282_, 5, v_unsafeStx_1255_);
lean_closure_set(v___f_1282_, 6, v_attrsStx_1256_);
lean_closure_set(v___f_1282_, 7, v___x_1257_);
lean_closure_set(v___f_1282_, 8, v_toBind_1250_);
lean_closure_set(v___f_1282_, 9, v_inst_1248_);
lean_closure_set(v___f_1282_, 10, v_inst_1258_);
lean_closure_set(v___f_1282_, 11, v_inst_1259_);
lean_closure_set(v___f_1282_, 12, v_inst_1249_);
lean_closure_set(v___f_1282_, 13, v_inst_1260_);
lean_closure_set(v___f_1282_, 14, v_inst_1261_);
lean_closure_set(v___f_1282_, 15, v_inst_1262_);
lean_closure_set(v___f_1282_, 16, v_inst_1263_);
lean_closure_set(v___f_1282_, 17, v_inst_1264_);
lean_closure_set(v___f_1282_, 18, v_inst_1265_);
lean_closure_set(v___f_1282_, 19, v_inst_1266_);
lean_closure_set(v___f_1282_, 20, v_inst_1267_);
lean_closure_set(v___f_1282_, 21, v_protectedStx_1268_);
v___x_1283_ = l_Lean_Syntax_getOptional_x3f(v_visibilityStx_1269_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_box(0);
v___y_1274_ = v___f_1282_;
v___y_1275_ = v___x_1284_;
goto v___jp_1273_;
}
else
{
lean_object* v_val_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_val_1285_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1283_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_val_1285_);
lean_dec(v___x_1283_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_val_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
v___y_1274_ = v___f_1282_;
v___y_1275_ = v___x_1290_;
goto v___jp_1273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_inst_1306_ = _args[0];
lean_object* v_inst_1307_ = _args[1];
lean_object* v_toBind_1308_ = _args[2];
lean_object* v_stx_1309_ = _args[3];
lean_object* v___y_1310_ = _args[4];
lean_object* v___y_1311_ = _args[5];
lean_object* v_toPure_1312_ = _args[6];
lean_object* v_unsafeStx_1313_ = _args[7];
lean_object* v_attrsStx_1314_ = _args[8];
lean_object* v___x_1315_ = _args[9];
lean_object* v_inst_1316_ = _args[10];
lean_object* v_inst_1317_ = _args[11];
lean_object* v_inst_1318_ = _args[12];
lean_object* v_inst_1319_ = _args[13];
lean_object* v_inst_1320_ = _args[14];
lean_object* v_inst_1321_ = _args[15];
lean_object* v_inst_1322_ = _args[16];
lean_object* v_inst_1323_ = _args[17];
lean_object* v_inst_1324_ = _args[18];
lean_object* v_inst_1325_ = _args[19];
lean_object* v_protectedStx_1326_ = _args[20];
lean_object* v_visibilityStx_1327_ = _args[21];
lean_object* v_docCommentStx_1328_ = _args[22];
lean_object* v___x_1329_ = _args[23];
lean_object* v_____do__lift_1330_ = _args[24];
_start:
{
uint8_t v___y_599__boxed_1331_; uint8_t v___y_600__boxed_1332_; lean_object* v_res_1333_; 
v___y_599__boxed_1331_ = lean_unbox(v___y_1310_);
v___y_600__boxed_1332_ = lean_unbox(v___y_1311_);
v_res_1333_ = l_Lean_Elab_elabModifiers___redArg___lam__2(v_inst_1306_, v_inst_1307_, v_toBind_1308_, v_stx_1309_, v___y_599__boxed_1331_, v___y_600__boxed_1332_, v_toPure_1312_, v_unsafeStx_1313_, v_attrsStx_1314_, v___x_1315_, v_inst_1316_, v_inst_1317_, v_inst_1318_, v_inst_1319_, v_inst_1320_, v_inst_1321_, v_inst_1322_, v_inst_1323_, v_inst_1324_, v_inst_1325_, v_protectedStx_1326_, v_visibilityStx_1327_, v_docCommentStx_1328_, v___x_1329_, v_____do__lift_1330_);
lean_dec_ref(v_____do__lift_1330_);
lean_dec(v_docCommentStx_1328_);
lean_dec(v_visibilityStx_1327_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg(lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_inst_1355_, lean_object* v_stx_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v_toApplicative_1358_; lean_object* v_toBind_1359_; lean_object* v_toPure_1360_; lean_object* v___x_1361_; lean_object* v_docCommentStx_1362_; lean_object* v___x_1363_; lean_object* v_attrsStx_1364_; lean_object* v___x_1365_; lean_object* v_visibilityStx_1366_; lean_object* v___x_1367_; lean_object* v_protectedStx_1368_; lean_object* v___y_1370_; uint8_t v___y_1371_; uint8_t v___y_1372_; uint8_t v___y_1378_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1357_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1358_ = lean_ctor_get(v_inst_1344_, 0);
v_toBind_1359_ = lean_ctor_get(v_inst_1344_, 1);
lean_inc(v_toBind_1359_);
v_toPure_1360_ = lean_ctor_get(v_toApplicative_1358_, 1);
lean_inc(v_toPure_1360_);
v___x_1361_ = lean_unsigned_to_nat(0u);
v_docCommentStx_1362_ = l_Lean_Syntax_getArg(v_stx_1356_, v___x_1361_);
v___x_1363_ = lean_unsigned_to_nat(1u);
v_attrsStx_1364_ = l_Lean_Syntax_getArg(v_stx_1356_, v___x_1363_);
v___x_1365_ = lean_unsigned_to_nat(2u);
v_visibilityStx_1366_ = l_Lean_Syntax_getArg(v_stx_1356_, v___x_1365_);
v___x_1367_ = lean_unsigned_to_nat(3u);
v_protectedStx_1368_ = l_Lean_Syntax_getArg(v_stx_1356_, v___x_1367_);
v___x_1391_ = lean_unsigned_to_nat(4u);
v___x_1392_ = l_Lean_Syntax_getArg(v_stx_1356_, v___x_1391_);
v___x_1393_ = l_Lean_Syntax_isNone(v___x_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1394_ = l_Lean_Syntax_getArg(v___x_1392_, v___x_1361_);
lean_dec(v___x_1392_);
v___x_1395_ = l_Lean_Syntax_getKind(v___x_1394_);
v___x_1396_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__1));
v___x_1397_ = lean_name_eq(v___x_1395_, v___x_1396_);
lean_dec(v___x_1395_);
if (v___x_1397_ == 0)
{
uint8_t v___x_1398_; 
v___x_1398_ = 2;
v___y_1378_ = v___x_1398_;
goto v___jp_1377_;
}
else
{
uint8_t v___x_1399_; 
v___x_1399_ = 1;
v___y_1378_ = v___x_1399_;
goto v___jp_1377_;
}
}
else
{
uint8_t v___x_1400_; 
lean_dec(v___x_1392_);
v___x_1400_ = 0;
v___y_1378_ = v___x_1400_;
goto v___jp_1377_;
}
v___jp_1369_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___f_1375_; lean_object* v___x_1376_; 
v___x_1373_ = lean_box(v___y_1371_);
v___x_1374_ = lean_box(v___y_1372_);
lean_inc(v_inst_1352_);
lean_inc(v_toBind_1359_);
v___f_1375_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__2___boxed), 25, 24);
lean_closure_set(v___f_1375_, 0, v_inst_1344_);
lean_closure_set(v___f_1375_, 1, v_inst_1347_);
lean_closure_set(v___f_1375_, 2, v_toBind_1359_);
lean_closure_set(v___f_1375_, 3, v_stx_1356_);
lean_closure_set(v___f_1375_, 4, v___x_1373_);
lean_closure_set(v___f_1375_, 5, v___x_1374_);
lean_closure_set(v___f_1375_, 6, v_toPure_1360_);
lean_closure_set(v___f_1375_, 7, v___y_1370_);
lean_closure_set(v___f_1375_, 8, v_attrsStx_1364_);
lean_closure_set(v___f_1375_, 9, v___x_1361_);
lean_closure_set(v___f_1375_, 10, v_inst_1345_);
lean_closure_set(v___f_1375_, 11, v_inst_1346_);
lean_closure_set(v___f_1375_, 12, v_inst_1349_);
lean_closure_set(v___f_1375_, 13, v_inst_1350_);
lean_closure_set(v___f_1375_, 14, v_inst_1351_);
lean_closure_set(v___f_1375_, 15, v_inst_1352_);
lean_closure_set(v___f_1375_, 16, v_inst_1353_);
lean_closure_set(v___f_1375_, 17, v_inst_1354_);
lean_closure_set(v___f_1375_, 18, v_inst_1355_);
lean_closure_set(v___f_1375_, 19, v_inst_1348_);
lean_closure_set(v___f_1375_, 20, v_protectedStx_1368_);
lean_closure_set(v___f_1375_, 21, v_visibilityStx_1366_);
lean_closure_set(v___f_1375_, 22, v_docCommentStx_1362_);
lean_closure_set(v___f_1375_, 23, v___x_1357_);
v___x_1376_ = lean_apply_4(v_toBind_1359_, lean_box(0), lean_box(0), v_inst_1352_, v___f_1375_);
return v___x_1376_;
}
v___jp_1377_:
{
lean_object* v___x_1379_; lean_object* v_unsafeStx_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1379_ = lean_unsigned_to_nat(5u);
v_unsafeStx_1380_ = l_Lean_Syntax_getArg(v_stx_1356_, v___x_1379_);
v___x_1381_ = lean_unsigned_to_nat(6u);
v___x_1382_ = l_Lean_Syntax_getArg(v_stx_1356_, v___x_1381_);
v___x_1383_ = l_Lean_Syntax_isNone(v___x_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1384_ = l_Lean_Syntax_getArg(v___x_1382_, v___x_1361_);
lean_dec(v___x_1382_);
v___x_1385_ = l_Lean_Syntax_getKind(v___x_1384_);
v___x_1386_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__0));
v___x_1387_ = lean_name_eq(v___x_1385_, v___x_1386_);
lean_dec(v___x_1385_);
if (v___x_1387_ == 0)
{
uint8_t v___x_1388_; 
v___x_1388_ = 1;
v___y_1370_ = v_unsafeStx_1380_;
v___y_1371_ = v___y_1378_;
v___y_1372_ = v___x_1388_;
goto v___jp_1369_;
}
else
{
uint8_t v___x_1389_; 
v___x_1389_ = 0;
v___y_1370_ = v_unsafeStx_1380_;
v___y_1371_ = v___y_1378_;
v___y_1372_ = v___x_1389_;
goto v___jp_1369_;
}
}
else
{
uint8_t v___x_1390_; 
lean_dec(v___x_1382_);
v___x_1390_ = 2;
v___y_1370_ = v_unsafeStx_1380_;
v___y_1371_ = v___y_1378_;
v___y_1372_ = v___x_1390_;
goto v___jp_1369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object* v_m_1401_, lean_object* v_inst_1402_, lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v_inst_1405_, lean_object* v_inst_1406_, lean_object* v_inst_1407_, lean_object* v_inst_1408_, lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_stx_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_Elab_elabModifiers___redArg(v_inst_1402_, v_inst_1403_, v_inst_1404_, v_inst_1405_, v_inst_1406_, v_inst_1407_, v_inst_1408_, v_inst_1409_, v_inst_1410_, v_inst_1411_, v_inst_1412_, v_inst_1413_, v_stx_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__0(lean_object* v_toPure_1416_, lean_object* v_declName_1417_, lean_object* v_____r_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_apply_2(v_toPure_1416_, lean_box(0), v_declName_1417_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__1(lean_object* v_declName_1420_, lean_object* v_env_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_addProtected(v_env_1421_, v_declName_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2(lean_object* v_modifiers_1423_, lean_object* v_toPure_1424_, lean_object* v_declName_1425_, lean_object* v_modifyEnv_1426_, lean_object* v___f_1427_, lean_object* v_toBind_1428_, lean_object* v___f_1429_, lean_object* v_____r_1430_){
_start:
{
uint8_t v_isProtected_1431_; 
v_isProtected_1431_ = lean_ctor_get_uint8(v_modifiers_1423_, sizeof(void*)*3 + 1);
if (v_isProtected_1431_ == 0)
{
lean_object* v___x_1432_; 
lean_dec(v___f_1429_);
lean_dec(v_toBind_1428_);
lean_dec_ref(v___f_1427_);
lean_dec(v_modifyEnv_1426_);
v___x_1432_ = lean_apply_2(v_toPure_1424_, lean_box(0), v_declName_1425_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec(v_declName_1425_);
lean_dec(v_toPure_1424_);
v___x_1433_ = lean_apply_1(v_modifyEnv_1426_, v___f_1427_);
v___x_1434_ = lean_apply_4(v_toBind_1428_, lean_box(0), lean_box(0), v___x_1433_, v___f_1429_);
return v___x_1434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2___boxed(lean_object* v_modifiers_1435_, lean_object* v_toPure_1436_, lean_object* v_declName_1437_, lean_object* v_modifyEnv_1438_, lean_object* v___f_1439_, lean_object* v_toBind_1440_, lean_object* v___f_1441_, lean_object* v_____r_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Elab_applyVisibility___redArg___lam__2(v_modifiers_1435_, v_toPure_1436_, v_declName_1437_, v_modifyEnv_1438_, v___f_1439_, v_toBind_1440_, v___f_1441_, v_____r_1442_);
lean_dec_ref(v_modifiers_1435_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__3(lean_object* v_toPure_1444_, lean_object* v_modifiers_1445_, lean_object* v_modifyEnv_1446_, lean_object* v_toBind_1447_, lean_object* v_inst_1448_, lean_object* v_inst_1449_, lean_object* v_inst_1450_, lean_object* v_inst_1451_, lean_object* v_inst_1452_, lean_object* v_____r_1453_, lean_object* v_declName_1454_){
_start:
{
lean_object* v___f_1455_; lean_object* v___f_1456_; lean_object* v___f_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_inc_n(v_declName_1454_, 3);
lean_inc(v_toPure_1444_);
v___f_1455_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1455_, 0, v_toPure_1444_);
lean_closure_set(v___f_1455_, 1, v_declName_1454_);
v___f_1456_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1456_, 0, v_declName_1454_);
lean_inc(v_toBind_1447_);
v___f_1457_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1457_, 0, v_modifiers_1445_);
lean_closure_set(v___f_1457_, 1, v_toPure_1444_);
lean_closure_set(v___f_1457_, 2, v_declName_1454_);
lean_closure_set(v___f_1457_, 3, v_modifyEnv_1446_);
lean_closure_set(v___f_1457_, 4, v___f_1456_);
lean_closure_set(v___f_1457_, 5, v_toBind_1447_);
lean_closure_set(v___f_1457_, 6, v___f_1455_);
v___x_1458_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(v_inst_1448_, v_inst_1449_, v_inst_1450_, v_inst_1451_, v_inst_1452_, v_declName_1454_);
v___x_1459_ = lean_apply_4(v_toBind_1447_, lean_box(0), lean_box(0), v___x_1458_, v___f_1457_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4(lean_object* v_declName_1460_, lean_object* v___f_1461_, lean_object* v_____do__lift_1462_){
_start:
{
lean_object* v_declName_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_declName_1463_ = l_Lean_mkPrivateName(v_____do__lift_1462_, v_declName_1460_);
v___x_1464_ = lean_box(0);
v___x_1465_ = lean_apply_2(v___f_1461_, v___x_1464_, v_declName_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4___boxed(lean_object* v_declName_1466_, lean_object* v___f_1467_, lean_object* v_____do__lift_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Elab_applyVisibility___redArg___lam__4(v_declName_1466_, v___f_1467_, v_____do__lift_1468_);
lean_dec_ref(v_____do__lift_1468_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5(lean_object* v_modifiers_1470_, lean_object* v_toBind_1471_, lean_object* v_getEnv_1472_, lean_object* v___f_1473_, lean_object* v___f_1474_, lean_object* v_declName_1475_, lean_object* v_____do__lift_1476_){
_start:
{
uint8_t v_visibility_1477_; uint8_t v___x_1478_; 
v_visibility_1477_ = lean_ctor_get_uint8(v_modifiers_1470_, sizeof(void*)*3);
v___x_1478_ = l_Lean_Elab_Visibility_isInferredPublic(v_____do__lift_1476_, v_visibility_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; 
lean_dec(v_declName_1475_);
lean_dec(v___f_1474_);
v___x_1479_ = lean_apply_4(v_toBind_1471_, lean_box(0), lean_box(0), v_getEnv_1472_, v___f_1473_);
return v___x_1479_;
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec(v___f_1473_);
lean_dec(v_getEnv_1472_);
lean_dec(v_toBind_1471_);
v___x_1480_ = lean_box(0);
v___x_1481_ = lean_apply_2(v___f_1474_, v___x_1480_, v_declName_1475_);
return v___x_1481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5___boxed(lean_object* v_modifiers_1482_, lean_object* v_toBind_1483_, lean_object* v_getEnv_1484_, lean_object* v___f_1485_, lean_object* v___f_1486_, lean_object* v_declName_1487_, lean_object* v_____do__lift_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_Elab_applyVisibility___redArg___lam__5(v_modifiers_1482_, v_toBind_1483_, v_getEnv_1484_, v___f_1485_, v___f_1486_, v_declName_1487_, v_____do__lift_1488_);
lean_dec_ref(v_____do__lift_1488_);
lean_dec_ref(v_modifiers_1482_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg(lean_object* v_inst_1490_, lean_object* v_inst_1491_, lean_object* v_inst_1492_, lean_object* v_inst_1493_, lean_object* v_inst_1494_, lean_object* v_modifiers_1495_, lean_object* v_declName_1496_){
_start:
{
lean_object* v_toApplicative_1497_; lean_object* v_toBind_1498_; lean_object* v_getEnv_1499_; lean_object* v_modifyEnv_1500_; lean_object* v_toPure_1501_; lean_object* v___f_1502_; lean_object* v___f_1503_; lean_object* v___f_1504_; lean_object* v___x_1505_; 
v_toApplicative_1497_ = lean_ctor_get(v_inst_1490_, 0);
v_toBind_1498_ = lean_ctor_get(v_inst_1490_, 1);
lean_inc_n(v_toBind_1498_, 3);
v_getEnv_1499_ = lean_ctor_get(v_inst_1491_, 0);
lean_inc_n(v_getEnv_1499_, 2);
v_modifyEnv_1500_ = lean_ctor_get(v_inst_1491_, 1);
lean_inc(v_modifyEnv_1500_);
v_toPure_1501_ = lean_ctor_get(v_toApplicative_1497_, 1);
lean_inc(v_toPure_1501_);
lean_inc_ref(v_modifiers_1495_);
v___f_1502_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__3), 11, 9);
lean_closure_set(v___f_1502_, 0, v_toPure_1501_);
lean_closure_set(v___f_1502_, 1, v_modifiers_1495_);
lean_closure_set(v___f_1502_, 2, v_modifyEnv_1500_);
lean_closure_set(v___f_1502_, 3, v_toBind_1498_);
lean_closure_set(v___f_1502_, 4, v_inst_1490_);
lean_closure_set(v___f_1502_, 5, v_inst_1491_);
lean_closure_set(v___f_1502_, 6, v_inst_1492_);
lean_closure_set(v___f_1502_, 7, v_inst_1493_);
lean_closure_set(v___f_1502_, 8, v_inst_1494_);
lean_inc_ref(v___f_1502_);
lean_inc(v_declName_1496_);
v___f_1503_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_1503_, 0, v_declName_1496_);
lean_closure_set(v___f_1503_, 1, v___f_1502_);
v___f_1504_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1504_, 0, v_modifiers_1495_);
lean_closure_set(v___f_1504_, 1, v_toBind_1498_);
lean_closure_set(v___f_1504_, 2, v_getEnv_1499_);
lean_closure_set(v___f_1504_, 3, v___f_1503_);
lean_closure_set(v___f_1504_, 4, v___f_1502_);
lean_closure_set(v___f_1504_, 5, v_declName_1496_);
v___x_1505_ = lean_apply_4(v_toBind_1498_, lean_box(0), lean_box(0), v_getEnv_1499_, v___f_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility(lean_object* v_m_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_modifiers_1512_, lean_object* v_declName_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1507_, v_inst_1508_, v_inst_1509_, v_inst_1510_, v_inst_1511_, v_modifiers_1512_, v_declName_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0(lean_object* v_toPure_1515_, lean_object* v_____s_1516_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = lean_box(0);
v___x_1518_ = lean_apply_2(v_toPure_1515_, lean_box(0), v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1(lean_object* v___x_1519_, lean_object* v_toPure_1520_, lean_object* v_r_1521_){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1519_);
v___x_1523_ = lean_apply_2(v_toPure_1520_, lean_box(0), v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0));
v___x_1526_ = l_Lean_stringToMessageData(v___x_1525_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2));
v___x_1529_ = l_Lean_stringToMessageData(v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4));
v___x_1532_ = l_Lean_stringToMessageData(v___x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2(lean_object* v_pre_1533_, lean_object* v_declName_1534_, lean_object* v___x_1535_, lean_object* v_toPure_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_toBind_1539_, lean_object* v___f_1540_, lean_object* v_a_1541_, lean_object* v_x_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1544_; uint8_t v___x_1545_; 
lean_inc(v_a_1541_);
lean_inc(v_pre_1533_);
v___x_1544_ = l_Lean_Name_append(v_pre_1533_, v_a_1541_);
v___x_1545_ = lean_name_eq(v___x_1544_, v_declName_1534_);
lean_dec(v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_dec(v_a_1541_);
lean_dec(v___f_1540_);
lean_dec(v_toBind_1539_);
lean_dec_ref(v_inst_1538_);
lean_dec_ref(v_inst_1537_);
lean_dec(v_declName_1534_);
lean_dec(v_pre_1533_);
v___x_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1535_);
v___x_1547_ = lean_apply_2(v_toPure_1536_, lean_box(0), v___x_1546_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec(v_toPure_1536_);
v___x_1548_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1549_ = 0;
v___x_1550_ = l_Lean_MessageData_ofConstName(v_declName_1534_, v___x_1549_);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1548_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = l_Lean_MessageData_ofName(v_pre_1533_);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = l_Lean_MessageData_ofName(v_a_1541_);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = l_Lean_throwError___redArg(v_inst_1537_, v_inst_1538_, v___x_1561_);
v___x_1563_ = lean_apply_4(v_toBind_1539_, lean_box(0), lean_box(0), v___x_1562_, v___f_1540_);
return v___x_1563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(lean_object* v_pre_1564_, uint8_t v___x_1565_, lean_object* v_toPure_1566_, lean_object* v_declName_1567_, lean_object* v_inst_1568_, lean_object* v_inst_1569_, lean_object* v_toBind_1570_, lean_object* v___f_1571_, lean_object* v_____do__lift_1572_){
_start:
{
lean_object* v_fieldNames_1573_; lean_object* v___x_1574_; lean_object* v___f_1575_; lean_object* v___f_1576_; size_t v_sz_1577_; size_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_inc(v_pre_1564_);
v_fieldNames_1573_ = l_Lean_getStructureFieldsFlattened(v_____do__lift_1572_, v_pre_1564_, v___x_1565_);
v___x_1574_ = lean_box(0);
lean_inc(v_toPure_1566_);
v___f_1575_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1575_, 0, v___x_1574_);
lean_closure_set(v___f_1575_, 1, v_toPure_1566_);
lean_inc(v_toBind_1570_);
lean_inc_ref(v_inst_1568_);
v___f_1576_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2), 11, 8);
lean_closure_set(v___f_1576_, 0, v_pre_1564_);
lean_closure_set(v___f_1576_, 1, v_declName_1567_);
lean_closure_set(v___f_1576_, 2, v___x_1574_);
lean_closure_set(v___f_1576_, 3, v_toPure_1566_);
lean_closure_set(v___f_1576_, 4, v_inst_1568_);
lean_closure_set(v___f_1576_, 5, v_inst_1569_);
lean_closure_set(v___f_1576_, 6, v_toBind_1570_);
lean_closure_set(v___f_1576_, 7, v___f_1575_);
v_sz_1577_ = lean_array_size(v_fieldNames_1573_);
v___x_1578_ = ((size_t)0ULL);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1568_, v_fieldNames_1573_, v___f_1576_, v_sz_1577_, v___x_1578_, v___x_1574_);
v___x_1580_ = lean_apply_4(v_toBind_1570_, lean_box(0), lean_box(0), v___x_1579_, v___f_1571_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed(lean_object* v_pre_1581_, lean_object* v___x_1582_, lean_object* v_toPure_1583_, lean_object* v_declName_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_toBind_1587_, lean_object* v___f_1588_, lean_object* v_____do__lift_1589_){
_start:
{
uint8_t v___x_671__boxed_1590_; lean_object* v_res_1591_; 
v___x_671__boxed_1590_ = lean_unbox(v___x_1582_);
v_res_1591_ = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(v_pre_1581_, v___x_671__boxed_1590_, v_toPure_1583_, v_declName_1584_, v_inst_1585_, v_inst_1586_, v_toBind_1587_, v___f_1588_, v_____do__lift_1589_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4(lean_object* v_pre_1592_, lean_object* v_toPure_1593_, lean_object* v_declName_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_toBind_1597_, lean_object* v___f_1598_, lean_object* v_getEnv_1599_, lean_object* v_____do__lift_1600_){
_start:
{
uint8_t v___x_1601_; 
lean_inc(v_pre_1592_);
v___x_1601_ = l_Lean_isStructure(v_____do__lift_1600_, v_pre_1592_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec(v_getEnv_1599_);
lean_dec(v___f_1598_);
lean_dec(v_toBind_1597_);
lean_dec_ref(v_inst_1596_);
lean_dec_ref(v_inst_1595_);
lean_dec(v_declName_1594_);
lean_dec(v_pre_1592_);
v___x_1602_ = lean_box(0);
v___x_1603_ = lean_apply_2(v_toPure_1593_, lean_box(0), v___x_1602_);
return v___x_1603_;
}
else
{
lean_object* v___x_1604_; lean_object* v___f_1605_; lean_object* v___x_1606_; 
v___x_1604_ = lean_box(v___x_1601_);
lean_inc(v_toBind_1597_);
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1605_, 0, v_pre_1592_);
lean_closure_set(v___f_1605_, 1, v___x_1604_);
lean_closure_set(v___f_1605_, 2, v_toPure_1593_);
lean_closure_set(v___f_1605_, 3, v_declName_1594_);
lean_closure_set(v___f_1605_, 4, v_inst_1595_);
lean_closure_set(v___f_1605_, 5, v_inst_1596_);
lean_closure_set(v___f_1605_, 6, v_toBind_1597_);
lean_closure_set(v___f_1605_, 7, v___f_1598_);
v___x_1606_ = lean_apply_4(v_toBind_1597_, lean_box(0), lean_box(0), v_getEnv_1599_, v___f_1605_);
return v___x_1606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg(lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_declName_1610_){
_start:
{
if (lean_obj_tag(v_declName_1610_) == 1)
{
lean_object* v_toApplicative_1611_; lean_object* v_toBind_1612_; lean_object* v_toPure_1613_; lean_object* v_pre_1614_; lean_object* v_getEnv_1615_; lean_object* v___f_1616_; lean_object* v___f_1617_; lean_object* v___x_1618_; 
v_toApplicative_1611_ = lean_ctor_get(v_inst_1607_, 0);
v_toBind_1612_ = lean_ctor_get(v_inst_1607_, 1);
lean_inc_n(v_toBind_1612_, 2);
v_toPure_1613_ = lean_ctor_get(v_toApplicative_1611_, 1);
lean_inc_n(v_toPure_1613_, 2);
v_pre_1614_ = lean_ctor_get(v_declName_1610_, 0);
lean_inc(v_pre_1614_);
v_getEnv_1615_ = lean_ctor_get(v_inst_1608_, 0);
lean_inc_n(v_getEnv_1615_, 2);
lean_dec_ref(v_inst_1608_);
v___f_1616_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1616_, 0, v_toPure_1613_);
v___f_1617_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1617_, 0, v_pre_1614_);
lean_closure_set(v___f_1617_, 1, v_toPure_1613_);
lean_closure_set(v___f_1617_, 2, v_declName_1610_);
lean_closure_set(v___f_1617_, 3, v_inst_1607_);
lean_closure_set(v___f_1617_, 4, v_inst_1609_);
lean_closure_set(v___f_1617_, 5, v_toBind_1612_);
lean_closure_set(v___f_1617_, 6, v___f_1616_);
lean_closure_set(v___f_1617_, 7, v_getEnv_1615_);
v___x_1618_ = lean_apply_4(v_toBind_1612_, lean_box(0), lean_box(0), v_getEnv_1615_, v___f_1617_);
return v___x_1618_;
}
else
{
lean_object* v_toApplicative_1619_; lean_object* v_toPure_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v_toApplicative_1619_ = lean_ctor_get(v_inst_1607_, 0);
lean_inc_ref(v_toApplicative_1619_);
lean_dec(v_declName_1610_);
lean_dec_ref(v_inst_1609_);
lean_dec_ref(v_inst_1608_);
lean_dec_ref(v_inst_1607_);
v_toPure_1620_ = lean_ctor_get(v_toApplicative_1619_, 1);
lean_inc(v_toPure_1620_);
lean_dec_ref(v_toApplicative_1619_);
v___x_1621_ = lean_box(0);
v___x_1622_ = lean_apply_2(v_toPure_1620_, lean_box(0), v___x_1621_);
return v___x_1622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField(lean_object* v_m_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_inst_1626_, lean_object* v_declName_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1624_, v_inst_1625_, v_inst_1626_, v_declName_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__0(lean_object* v_toApplicative_1629_, lean_object* v_declName_1630_, lean_object* v_shortName_1631_, lean_object* v_____r_1632_){
_start:
{
lean_object* v_toPure_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v_toPure_1633_ = lean_ctor_get(v_toApplicative_1629_, 1);
lean_inc(v_toPure_1633_);
lean_dec_ref(v_toApplicative_1629_);
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v_declName_1630_);
lean_ctor_set(v___x_1634_, 1, v_shortName_1631_);
v___x_1635_ = lean_apply_2(v_toPure_1633_, lean_box(0), v___x_1634_);
return v___x_1635_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0));
v___x_1638_ = l_Lean_stringToMessageData(v___x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2(lean_object* v_modifiers_1639_, lean_object* v_toApplicative_1640_, lean_object* v_shortName_1641_, lean_object* v_currNamespace_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_toBind_1645_, lean_object* v_declName_1646_){
_start:
{
uint8_t v_isProtected_1647_; 
v_isProtected_1647_ = lean_ctor_get_uint8(v_modifiers_1639_, sizeof(void*)*3 + 1);
if (v_isProtected_1647_ == 0)
{
lean_object* v_toPure_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec(v_toBind_1645_);
lean_dec_ref(v_inst_1644_);
lean_dec_ref(v_inst_1643_);
lean_dec(v_currNamespace_1642_);
v_toPure_1648_ = lean_ctor_get(v_toApplicative_1640_, 1);
lean_inc(v_toPure_1648_);
lean_dec_ref(v_toApplicative_1640_);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v_declName_1646_);
lean_ctor_set(v___x_1649_, 1, v_shortName_1641_);
v___x_1650_ = lean_apply_2(v_toPure_1648_, lean_box(0), v___x_1649_);
return v___x_1650_;
}
else
{
if (lean_obj_tag(v_currNamespace_1642_) == 1)
{
lean_object* v_str_1651_; lean_object* v_toPure_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec(v_toBind_1645_);
lean_dec_ref(v_inst_1644_);
lean_dec_ref(v_inst_1643_);
v_str_1651_ = lean_ctor_get(v_currNamespace_1642_, 1);
lean_inc_ref(v_str_1651_);
lean_dec_ref(v_currNamespace_1642_);
v_toPure_1652_ = lean_ctor_get(v_toApplicative_1640_, 1);
lean_inc(v_toPure_1652_);
lean_dec_ref(v_toApplicative_1640_);
v___x_1653_ = lean_box(0);
v___x_1654_ = l_Lean_Name_str___override(v___x_1653_, v_str_1651_);
v___x_1655_ = l_Lean_Name_append(v___x_1654_, v_shortName_1641_);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v_declName_1646_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = lean_apply_2(v_toPure_1652_, lean_box(0), v___x_1656_);
return v___x_1657_;
}
else
{
lean_object* v___f_1658_; uint8_t v___x_1659_; 
lean_dec(v_currNamespace_1642_);
lean_inc(v_shortName_1641_);
lean_inc(v_declName_1646_);
lean_inc_ref(v_toApplicative_1640_);
v___f_1658_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1658_, 0, v_toApplicative_1640_);
lean_closure_set(v___f_1658_, 1, v_declName_1646_);
lean_closure_set(v___f_1658_, 2, v_shortName_1641_);
v___x_1659_ = l_Lean_Name_isAtomic(v_shortName_1641_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
lean_dec_ref(v___f_1658_);
lean_dec(v_toBind_1645_);
lean_dec_ref(v_inst_1644_);
lean_dec_ref(v_inst_1643_);
v___x_1660_ = lean_box(0);
v___x_1661_ = l_Lean_Elab_mkDeclName___redArg___lam__0(v_toApplicative_1640_, v_declName_1646_, v_shortName_1641_, v___x_1660_);
return v___x_1661_;
}
else
{
lean_object* v___f_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec(v_declName_1646_);
lean_dec(v_shortName_1641_);
lean_dec_ref(v_toApplicative_1640_);
v___f_1662_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1662_, 0, v___f_1658_);
v___x_1663_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_1664_ = l_Lean_throwError___redArg(v_inst_1643_, v_inst_1644_, v___x_1663_);
v___x_1665_ = lean_apply_4(v_toBind_1645_, lean_box(0), lean_box(0), v___x_1664_, v___f_1662_);
return v___x_1665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2___boxed(lean_object* v_modifiers_1666_, lean_object* v_toApplicative_1667_, lean_object* v_shortName_1668_, lean_object* v_currNamespace_1669_, lean_object* v_inst_1670_, lean_object* v_inst_1671_, lean_object* v_toBind_1672_, lean_object* v_declName_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Elab_mkDeclName___redArg___lam__2(v_modifiers_1666_, v_toApplicative_1667_, v_shortName_1668_, v_currNamespace_1669_, v_inst_1670_, v_inst_1671_, v_toBind_1672_, v_declName_1673_);
lean_dec_ref(v_modifiers_1666_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__1(lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_modifiers_1680_, lean_object* v___y_1681_, lean_object* v_toBind_1682_, lean_object* v___f_1683_, lean_object* v_____r_1684_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1675_, v_inst_1676_, v_inst_1677_, v_inst_1678_, v_inst_1679_, v_modifiers_1680_, v___y_1681_);
v___x_1686_ = lean_apply_4(v_toBind_1682_, lean_box(0), lean_box(0), v___x_1685_, v___f_1683_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3(lean_object* v_modifiers_1687_, lean_object* v_toApplicative_1688_, lean_object* v_inst_1689_, lean_object* v_inst_1690_, lean_object* v_toBind_1691_, lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v___y_1695_, lean_object* v_____r_1696_, lean_object* v_shortName_1697_, lean_object* v_currNamespace_1698_){
_start:
{
lean_object* v___f_1699_; lean_object* v___f_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_inc_n(v_toBind_1691_, 2);
lean_inc_ref_n(v_inst_1690_, 2);
lean_inc_ref_n(v_inst_1689_, 2);
lean_inc_ref(v_modifiers_1687_);
v___f_1699_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1699_, 0, v_modifiers_1687_);
lean_closure_set(v___f_1699_, 1, v_toApplicative_1688_);
lean_closure_set(v___f_1699_, 2, v_shortName_1697_);
lean_closure_set(v___f_1699_, 3, v_currNamespace_1698_);
lean_closure_set(v___f_1699_, 4, v_inst_1689_);
lean_closure_set(v___f_1699_, 5, v_inst_1690_);
lean_closure_set(v___f_1699_, 6, v_toBind_1691_);
lean_inc(v___y_1695_);
lean_inc_ref(v_inst_1692_);
v___f_1700_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1700_, 0, v_inst_1689_);
lean_closure_set(v___f_1700_, 1, v_inst_1692_);
lean_closure_set(v___f_1700_, 2, v_inst_1690_);
lean_closure_set(v___f_1700_, 3, v_inst_1693_);
lean_closure_set(v___f_1700_, 4, v_inst_1694_);
lean_closure_set(v___f_1700_, 5, v_modifiers_1687_);
lean_closure_set(v___f_1700_, 6, v___y_1695_);
lean_closure_set(v___f_1700_, 7, v_toBind_1691_);
lean_closure_set(v___f_1700_, 8, v___f_1699_);
v___x_1701_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1689_, v_inst_1692_, v_inst_1690_, v___y_1695_);
v___x_1702_ = lean_apply_4(v_toBind_1691_, lean_box(0), lean_box(0), v___x_1701_, v___f_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__4(lean_object* v___f_1703_, lean_object* v_shortName_1704_, lean_object* v_currNamespace_1705_, lean_object* v_____r_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_apply_3(v___f_1703_, v_____r_1706_, v_shortName_1704_, v_currNamespace_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5(lean_object* v_modifiers_1708_, lean_object* v_toApplicative_1709_, lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_toBind_1712_, lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_inst_1715_, uint8_t v_isRootName_1716_, lean_object* v_shortName_1717_, lean_object* v_currNamespace_1718_, lean_object* v_name_1719_, lean_object* v___x_1720_, lean_object* v_imported_1721_, lean_object* v_ctx_1722_, lean_object* v_scopes_1723_, lean_object* v_____r_1724_){
_start:
{
lean_object* v___y_1726_; 
if (v_isRootName_1716_ == 0)
{
lean_object* v___x_1745_; 
lean_dec(v_scopes_1723_);
lean_dec(v_ctx_1722_);
lean_dec(v_imported_1721_);
lean_inc(v_shortName_1717_);
lean_inc(v_currNamespace_1718_);
v___x_1745_ = l_Lean_Name_append(v_currNamespace_1718_, v_shortName_1717_);
v___y_1726_ = v___x_1745_;
goto v___jp_1725_;
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1746_ = lean_box(0);
lean_inc(v_name_1719_);
v___x_1747_ = l_Lean_Name_replacePrefix(v_name_1719_, v___x_1720_, v___x_1746_);
v___x_1748_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v_imported_1721_);
lean_ctor_set(v___x_1748_, 2, v_ctx_1722_);
lean_ctor_set(v___x_1748_, 3, v_scopes_1723_);
v___x_1749_ = l_Lean_MacroScopesView_review(v___x_1748_);
v___y_1726_ = v___x_1749_;
goto v___jp_1725_;
}
v___jp_1725_:
{
lean_object* v___f_1727_; 
lean_inc(v___y_1726_);
lean_inc_ref(v_inst_1715_);
lean_inc(v_inst_1714_);
lean_inc_ref(v_inst_1713_);
lean_inc(v_toBind_1712_);
lean_inc_ref(v_inst_1711_);
lean_inc_ref(v_inst_1710_);
lean_inc_ref(v_toApplicative_1709_);
lean_inc_ref(v_modifiers_1708_);
v___f_1727_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__3), 12, 9);
lean_closure_set(v___f_1727_, 0, v_modifiers_1708_);
lean_closure_set(v___f_1727_, 1, v_toApplicative_1709_);
lean_closure_set(v___f_1727_, 2, v_inst_1710_);
lean_closure_set(v___f_1727_, 3, v_inst_1711_);
lean_closure_set(v___f_1727_, 4, v_toBind_1712_);
lean_closure_set(v___f_1727_, 5, v_inst_1713_);
lean_closure_set(v___f_1727_, 6, v_inst_1714_);
lean_closure_set(v___f_1727_, 7, v_inst_1715_);
lean_closure_set(v___f_1727_, 8, v___y_1726_);
if (v_isRootName_1716_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec_ref(v___f_1727_);
lean_dec(v_name_1719_);
v___x_1728_ = lean_box(0);
v___x_1729_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1708_, v_toApplicative_1709_, v_inst_1710_, v_inst_1711_, v_toBind_1712_, v_inst_1713_, v_inst_1714_, v_inst_1715_, v___y_1726_, v___x_1728_, v_shortName_1717_, v_currNamespace_1718_);
return v___x_1729_;
}
else
{
if (lean_obj_tag(v_name_1719_) == 1)
{
lean_object* v_pre_1730_; lean_object* v_str_1731_; lean_object* v___x_1732_; lean_object* v_shortName_1733_; lean_object* v_currNamespace_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
lean_dec_ref(v___f_1727_);
lean_dec(v_currNamespace_1718_);
lean_dec(v_shortName_1717_);
v_pre_1730_ = lean_ctor_get(v_name_1719_, 0);
lean_inc(v_pre_1730_);
v_str_1731_ = lean_ctor_get(v_name_1719_, 1);
lean_inc_ref(v_str_1731_);
lean_dec_ref(v_name_1719_);
v___x_1732_ = lean_box(0);
v_shortName_1733_ = l_Lean_Name_str___override(v___x_1732_, v_str_1731_);
v_currNamespace_1734_ = l_Lean_Name_replacePrefix(v_pre_1730_, v___x_1720_, v___x_1732_);
v___x_1735_ = lean_box(0);
v___x_1736_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1708_, v_toApplicative_1709_, v_inst_1710_, v_inst_1711_, v_toBind_1712_, v_inst_1713_, v_inst_1714_, v_inst_1715_, v___y_1726_, v___x_1735_, v_shortName_1733_, v_currNamespace_1734_);
return v___x_1736_;
}
else
{
lean_object* v___f_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec(v___y_1726_);
lean_dec_ref(v_inst_1715_);
lean_dec(v_inst_1714_);
lean_dec_ref(v_inst_1713_);
lean_dec_ref(v_toApplicative_1709_);
lean_dec_ref(v_modifiers_1708_);
v___f_1737_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__4), 4, 3);
lean_closure_set(v___f_1737_, 0, v___f_1727_);
lean_closure_set(v___f_1737_, 1, v_shortName_1717_);
lean_closure_set(v___f_1737_, 2, v_currNamespace_1718_);
v___x_1738_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1739_ = l_Lean_MessageData_ofName(v_name_1719_);
v___x_1740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1738_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = l_Lean_throwError___redArg(v_inst_1710_, v_inst_1711_, v___x_1742_);
v___x_1744_ = lean_apply_4(v_toBind_1712_, lean_box(0), lean_box(0), v___x_1743_, v___f_1737_);
return v___x_1744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_modifiers_1750_ = _args[0];
lean_object* v_toApplicative_1751_ = _args[1];
lean_object* v_inst_1752_ = _args[2];
lean_object* v_inst_1753_ = _args[3];
lean_object* v_toBind_1754_ = _args[4];
lean_object* v_inst_1755_ = _args[5];
lean_object* v_inst_1756_ = _args[6];
lean_object* v_inst_1757_ = _args[7];
lean_object* v_isRootName_1758_ = _args[8];
lean_object* v_shortName_1759_ = _args[9];
lean_object* v_currNamespace_1760_ = _args[10];
lean_object* v_name_1761_ = _args[11];
lean_object* v___x_1762_ = _args[12];
lean_object* v_imported_1763_ = _args[13];
lean_object* v_ctx_1764_ = _args[14];
lean_object* v_scopes_1765_ = _args[15];
lean_object* v_____r_1766_ = _args[16];
_start:
{
uint8_t v_isRootName_boxed_1767_; lean_object* v_res_1768_; 
v_isRootName_boxed_1767_ = lean_unbox(v_isRootName_1758_);
v_res_1768_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1750_, v_toApplicative_1751_, v_inst_1752_, v_inst_1753_, v_toBind_1754_, v_inst_1755_, v_inst_1756_, v_inst_1757_, v_isRootName_boxed_1767_, v_shortName_1759_, v_currNamespace_1760_, v_name_1761_, v___x_1762_, v_imported_1763_, v_ctx_1764_, v_scopes_1765_, v_____r_1766_);
lean_dec(v___x_1762_);
return v_res_1768_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___closed__3(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__2));
v___x_1774_ = l_Lean_stringToMessageData(v___x_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg(lean_object* v_inst_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_currNamespace_1780_, lean_object* v_modifiers_1781_, lean_object* v_shortName_1782_){
_start:
{
lean_object* v_view_1783_; lean_object* v_name_1784_; lean_object* v_imported_1785_; lean_object* v_ctx_1786_; lean_object* v_scopes_1787_; lean_object* v_toApplicative_1788_; lean_object* v_toBind_1789_; lean_object* v___x_1790_; uint8_t v_isRootName_1791_; lean_object* v___x_1792_; lean_object* v___f_1793_; uint8_t v___x_1794_; 
lean_inc_n(v_shortName_1782_, 2);
v_view_1783_ = l_Lean_extractMacroScopes(v_shortName_1782_);
v_name_1784_ = lean_ctor_get(v_view_1783_, 0);
lean_inc_n(v_name_1784_, 2);
v_imported_1785_ = lean_ctor_get(v_view_1783_, 1);
lean_inc_n(v_imported_1785_, 2);
v_ctx_1786_ = lean_ctor_get(v_view_1783_, 2);
lean_inc_n(v_ctx_1786_, 2);
v_scopes_1787_ = lean_ctor_get(v_view_1783_, 3);
lean_inc_n(v_scopes_1787_, 2);
lean_dec_ref(v_view_1783_);
v_toApplicative_1788_ = lean_ctor_get(v_inst_1775_, 0);
v_toBind_1789_ = lean_ctor_get(v_inst_1775_, 1);
lean_inc_n(v_toBind_1789_, 2);
v___x_1790_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_1791_ = l_Lean_Name_isPrefixOf(v___x_1790_, v_name_1784_);
v___x_1792_ = lean_box(v_isRootName_1791_);
lean_inc(v_currNamespace_1780_);
lean_inc_ref(v_inst_1779_);
lean_inc(v_inst_1778_);
lean_inc_ref(v_inst_1776_);
lean_inc_ref(v_inst_1777_);
lean_inc_ref(v_inst_1775_);
lean_inc_ref(v_toApplicative_1788_);
lean_inc_ref(v_modifiers_1781_);
v___f_1793_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1793_, 0, v_modifiers_1781_);
lean_closure_set(v___f_1793_, 1, v_toApplicative_1788_);
lean_closure_set(v___f_1793_, 2, v_inst_1775_);
lean_closure_set(v___f_1793_, 3, v_inst_1777_);
lean_closure_set(v___f_1793_, 4, v_toBind_1789_);
lean_closure_set(v___f_1793_, 5, v_inst_1776_);
lean_closure_set(v___f_1793_, 6, v_inst_1778_);
lean_closure_set(v___f_1793_, 7, v_inst_1779_);
lean_closure_set(v___f_1793_, 8, v___x_1792_);
lean_closure_set(v___f_1793_, 9, v_shortName_1782_);
lean_closure_set(v___f_1793_, 10, v_currNamespace_1780_);
lean_closure_set(v___f_1793_, 11, v_name_1784_);
lean_closure_set(v___f_1793_, 12, v___x_1790_);
lean_closure_set(v___f_1793_, 13, v_imported_1785_);
lean_closure_set(v___f_1793_, 14, v_ctx_1786_);
lean_closure_set(v___f_1793_, 15, v_scopes_1787_);
v___x_1794_ = lean_name_eq(v_name_1784_, v___x_1790_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_inc_ref(v_toApplicative_1788_);
lean_dec_ref(v___f_1793_);
v___x_1795_ = lean_box(0);
v___x_1796_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1781_, v_toApplicative_1788_, v_inst_1775_, v_inst_1777_, v_toBind_1789_, v_inst_1776_, v_inst_1778_, v_inst_1779_, v_isRootName_1791_, v_shortName_1782_, v_currNamespace_1780_, v_name_1784_, v___x_1790_, v_imported_1785_, v_ctx_1786_, v_scopes_1787_, v___x_1795_);
return v___x_1796_;
}
else
{
lean_object* v___f_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
lean_dec(v_scopes_1787_);
lean_dec(v_ctx_1786_);
lean_dec(v_imported_1785_);
lean_dec(v_name_1784_);
lean_dec(v_shortName_1782_);
lean_dec_ref(v_modifiers_1781_);
lean_dec(v_currNamespace_1780_);
lean_dec_ref(v_inst_1779_);
lean_dec(v_inst_1778_);
lean_dec_ref(v_inst_1776_);
v___f_1797_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1797_, 0, v___f_1793_);
v___x_1798_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_1799_ = l_Lean_throwError___redArg(v_inst_1775_, v_inst_1777_, v___x_1798_);
v___x_1800_ = lean_apply_4(v_toBind_1789_, lean_box(0), lean_box(0), v___x_1799_, v___f_1797_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName(lean_object* v_m_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_inst_1804_, lean_object* v_inst_1805_, lean_object* v_inst_1806_, lean_object* v_currNamespace_1807_, lean_object* v_modifiers_1808_, lean_object* v_shortName_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_Elab_mkDeclName___redArg(v_inst_1802_, v_inst_1803_, v_inst_1804_, v_inst_1805_, v_inst_1806_, v_currNamespace_1807_, v_modifiers_1808_, v_shortName_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore(lean_object* v_declId_1820_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = l_Lean_Syntax_isIdent(v_declId_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v_id_1824_; lean_object* v___x_1825_; lean_object* v_optUnivDeclStx_1826_; lean_object* v___x_1827_; 
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = l_Lean_Syntax_getArg(v_declId_1820_, v___x_1822_);
v_id_1824_ = l_Lean_Syntax_getId(v___x_1823_);
lean_dec(v___x_1823_);
v___x_1825_ = lean_unsigned_to_nat(1u);
v_optUnivDeclStx_1826_ = l_Lean_Syntax_getArg(v_declId_1820_, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v_id_1824_);
lean_ctor_set(v___x_1827_, 1, v_optUnivDeclStx_1826_);
return v___x_1827_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1828_ = l_Lean_Syntax_getId(v_declId_1820_);
v___x_1829_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__3));
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1828_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
return v___x_1830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore___boxed(lean_object* v_declId_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_Elab_expandDeclIdCore(v_declId_1831_);
lean_dec(v_declId_1831_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(lean_object* v_msgData_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v_env_1840_; lean_object* v___x_1841_; lean_object* v_mctx_1842_; lean_object* v_lctx_1843_; lean_object* v_options_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1839_ = lean_st_ref_get(v___y_1837_);
v_env_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc_ref(v_env_1840_);
lean_dec(v___x_1839_);
v___x_1841_ = lean_st_ref_get(v___y_1835_);
v_mctx_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc_ref(v_mctx_1842_);
lean_dec(v___x_1841_);
v_lctx_1843_ = lean_ctor_get(v___y_1834_, 2);
v_options_1844_ = lean_ctor_get(v___y_1836_, 2);
lean_inc_ref(v_options_1844_);
lean_inc_ref(v_lctx_1843_);
v___x_1845_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1845_, 0, v_env_1840_);
lean_ctor_set(v___x_1845_, 1, v_mctx_1842_);
lean_ctor_set(v___x_1845_, 2, v_lctx_1843_);
lean_ctor_set(v___x_1845_, 3, v_options_1844_);
v___x_1846_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
lean_ctor_set(v___x_1846_, 1, v_msgData_1833_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msgData_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
return v_res_1854_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(lean_object* v_opts_1855_, lean_object* v_opt_1856_){
_start:
{
lean_object* v_name_1857_; lean_object* v_defValue_1858_; lean_object* v_map_1859_; lean_object* v___x_1860_; 
v_name_1857_ = lean_ctor_get(v_opt_1856_, 0);
v_defValue_1858_ = lean_ctor_get(v_opt_1856_, 1);
v_map_1859_ = lean_ctor_get(v_opts_1855_, 0);
v___x_1860_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1859_, v_name_1857_);
if (lean_obj_tag(v___x_1860_) == 0)
{
uint8_t v___x_1861_; 
v___x_1861_ = lean_unbox(v_defValue_1858_);
return v___x_1861_;
}
else
{
lean_object* v_val_1862_; 
v_val_1862_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_val_1862_);
lean_dec_ref(v___x_1860_);
if (lean_obj_tag(v_val_1862_) == 1)
{
uint8_t v_v_1863_; 
v_v_1863_ = lean_ctor_get_uint8(v_val_1862_, 0);
lean_dec_ref(v_val_1862_);
return v_v_1863_;
}
else
{
uint8_t v___x_1864_; 
lean_dec(v_val_1862_);
v___x_1864_ = lean_unbox(v_defValue_1858_);
return v___x_1864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_opts_1865_, lean_object* v_opt_1866_){
_start:
{
uint8_t v_res_1867_; lean_object* v_r_1868_; 
v_res_1867_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_opts_1865_, v_opt_1866_);
lean_dec_ref(v_opt_1866_);
lean_dec_ref(v_opts_1865_);
v_r_1868_ = lean_box(v_res_1867_);
return v_r_1868_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_box(1);
v___x_1870_ = l_Lean_MessageData_ofFormat(v___x_1869_);
return v___x_1870_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2));
v___x_1875_ = l_Lean_MessageData_ofFormat(v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(lean_object* v_x_1876_, lean_object* v_x_1877_){
_start:
{
if (lean_obj_tag(v_x_1877_) == 0)
{
return v_x_1876_;
}
else
{
lean_object* v_head_1878_; lean_object* v_tail_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1901_; 
v_head_1878_ = lean_ctor_get(v_x_1877_, 0);
v_tail_1879_ = lean_ctor_get(v_x_1877_, 1);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_x_1877_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1881_ = v_x_1877_;
v_isShared_1882_ = v_isSharedCheck_1901_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_tail_1879_);
lean_inc(v_head_1878_);
lean_dec(v_x_1877_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1901_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v_before_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1899_; 
v_before_1883_ = lean_ctor_get(v_head_1878_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_head_1878_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v_head_1878_, 1);
lean_dec(v_unused_1900_);
v___x_1885_ = v_head_1878_;
v_isShared_1886_ = v_isSharedCheck_1899_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_before_1883_);
lean_dec(v_head_1878_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1899_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_1886_ == 0)
{
lean_ctor_set_tag(v___x_1885_, 7);
lean_ctor_set(v___x_1885_, 1, v___x_1887_);
lean_ctor_set(v___x_1885_, 0, v_x_1876_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_x_1876_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3);
if (v_isShared_1882_ == 0)
{
lean_ctor_set_tag(v___x_1881_, 7);
lean_ctor_set(v___x_1881_, 1, v___x_1890_);
lean_ctor_set(v___x_1881_, 0, v___x_1889_);
v___x_1892_ = v___x_1881_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = l_Lean_MessageData_ofSyntax(v_before_1883_);
v___x_1894_ = l_Lean_indentD(v___x_1893_);
v___x_1895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1892_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v_x_1876_ = v___x_1895_;
v_x_1877_ = v_tail_1879_;
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
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1));
v___x_1906_ = l_Lean_MessageData_ofFormat(v___x_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_1907_, lean_object* v_macroStack_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_options_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v_options_1911_ = lean_ctor_get(v___y_1909_, 2);
v___x_1912_ = l_Lean_Elab_pp_macroStack;
v___x_1913_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_options_1911_, v___x_1912_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
lean_dec(v_macroStack_1908_);
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_msgData_1907_);
return v___x_1914_;
}
else
{
if (lean_obj_tag(v_macroStack_1908_) == 0)
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_msgData_1907_);
return v___x_1915_;
}
else
{
lean_object* v_head_1916_; lean_object* v_after_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1932_; 
v_head_1916_ = lean_ctor_get(v_macroStack_1908_, 0);
lean_inc(v_head_1916_);
v_after_1917_ = lean_ctor_get(v_head_1916_, 1);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_head_1916_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v_head_1916_, 0);
lean_dec(v_unused_1933_);
v___x_1919_ = v_head_1916_;
v_isShared_1920_ = v_isSharedCheck_1932_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_after_1917_);
lean_dec(v_head_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1932_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1921_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_1920_ == 0)
{
lean_ctor_set_tag(v___x_1919_, 7);
lean_ctor_set(v___x_1919_, 1, v___x_1921_);
lean_ctor_set(v___x_1919_, 0, v_msgData_1907_);
v___x_1923_ = v___x_1919_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_msgData_1907_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v_msgData_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1924_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = l_Lean_MessageData_ofSyntax(v_after_1917_);
v___x_1927_ = l_Lean_indentD(v___x_1926_);
v_msgData_1928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1928_, 0, v___x_1925_);
lean_ctor_set(v_msgData_1928_, 1, v___x_1927_);
v___x_1929_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(v_msgData_1928_, v_macroStack_1908_);
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
return v___x_1930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_1934_, lean_object* v_macroStack_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_1934_, v_macroStack_1935_, v___y_1936_);
lean_dec_ref(v___y_1936_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(lean_object* v_msg_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_ref_1947_; lean_object* v___x_1948_; lean_object* v_a_1949_; lean_object* v_macroStack_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1961_; 
v_ref_1947_ = lean_ctor_get(v___y_1944_, 5);
v___x_1948_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msg_1939_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref(v___x_1948_);
v_macroStack_1950_ = lean_ctor_get(v___y_1940_, 1);
lean_inc_n(v_macroStack_1950_, 2);
v___x_1951_ = l_Lean_Elab_getBetterRef(v_ref_1947_, v_macroStack_1950_);
v___x_1952_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_a_1949_, v_macroStack_1950_, v___y_1944_);
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1955_ = v___x_1952_;
v_isShared_1956_ = v_isSharedCheck_1961_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1952_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1961_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1951_);
lean_ctor_set(v___x_1957_, 1, v_a_1953_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set_tag(v___x_1955_, 1);
lean_ctor_set(v___x_1955_, 0, v___x_1957_);
v___x_1959_ = v___x_1955_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(lean_object* v_env_1971_, lean_object* v_declName_1972_, lean_object* v___f_1973_, lean_object* v_addInfo_1974_, lean_object* v_____r_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v___x_1983_; uint8_t v___x_1984_; uint8_t v___x_1985_; 
lean_inc(v_declName_1972_);
v___x_1983_ = l_Lean_mkPrivateName(v_env_1971_, v_declName_1972_);
v___x_1984_ = 1;
lean_inc(v___x_1983_);
v___x_1985_ = l_Lean_Environment_contains(v_env_1971_, v___x_1983_, v___x_1984_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
lean_dec(v___x_1983_);
lean_dec_ref(v_addInfo_1974_);
lean_dec(v_declName_1972_);
v___x_1986_ = lean_box(0);
lean_inc(v___y_1981_);
lean_inc_ref(v___y_1980_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
v___x_1987_ = lean_apply_8(v___f_1973_, v___x_1986_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, lean_box(0));
return v___x_1987_;
}
else
{
lean_object* v___x_1988_; 
lean_dec_ref(v___f_1973_);
lean_inc(v___y_1981_);
lean_inc_ref(v___y_1980_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
v___x_1988_ = lean_apply_8(v_addInfo_1974_, v___x_1983_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, lean_box(0));
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_dec_ref(v___x_1988_);
v___x_1989_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1);
v___x_1990_ = l_Lean_MessageData_ofConstName(v_declName_1972_, v___x_1984_);
v___x_1991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_1993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_1993_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
return v___x_1994_;
}
else
{
lean_dec(v_declName_1972_);
return v___x_1988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed(lean_object* v_env_1995_, lean_object* v_declName_1996_, lean_object* v___f_1997_, lean_object* v_addInfo_1998_, lean_object* v_____r_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(v_env_1995_, v_declName_1996_, v___f_1997_, v_addInfo_1998_, v_____r_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(lean_object* v___f_2008_, lean_object* v_declName_2009_, uint8_t v___x_2010_, lean_object* v_env_2011_, lean_object* v_____do__lift_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
uint8_t v___y_2021_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
lean_inc(v_declName_2009_);
v___x_2030_ = l_Lean_privateToUserName(v_declName_2009_);
lean_inc_ref(v_env_2011_);
v___x_2031_ = lean_is_reserved_name(v_env_2011_, v___x_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; uint8_t v___x_2033_; 
lean_inc(v_declName_2009_);
v___x_2032_ = l_Lean_mkPrivateName(v_____do__lift_2012_, v_declName_2009_);
v___x_2033_ = lean_is_reserved_name(v_env_2011_, v___x_2032_);
v___y_2021_ = v___x_2033_;
goto v___jp_2020_;
}
else
{
lean_dec_ref(v_env_2011_);
v___y_2021_ = v___x_2031_;
goto v___jp_2020_;
}
v___jp_2020_:
{
if (v___y_2021_ == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec(v_declName_2009_);
v___x_2022_ = lean_box(0);
lean_inc(v___y_2018_);
lean_inc_ref(v___y_2017_);
lean_inc(v___y_2016_);
lean_inc_ref(v___y_2015_);
lean_inc(v___y_2014_);
lean_inc_ref(v___y_2013_);
v___x_2023_ = lean_apply_8(v___f_2008_, v___x_2022_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, lean_box(0));
return v___x_2023_;
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_dec_ref(v___f_2008_);
v___x_2024_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2025_ = l_Lean_MessageData_ofConstName(v_declName_2009_, v___x_2010_);
v___x_2026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2024_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3);
v___x_2028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2026_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2028_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
return v___x_2029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed(lean_object* v___f_2034_, lean_object* v_declName_2035_, lean_object* v___x_2036_, lean_object* v_env_2037_, lean_object* v_____do__lift_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
uint8_t v___x_17521__boxed_2046_; lean_object* v_res_2047_; 
v___x_17521__boxed_2046_ = lean_unbox(v___x_2036_);
v_res_2047_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(v___f_2034_, v_declName_2035_, v___x_17521__boxed_2046_, v_env_2037_, v_____do__lift_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec_ref(v_____do__lift_2038_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(lean_object* v_t_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v___x_2051_; lean_object* v_infoState_2052_; uint8_t v_enabled_2053_; 
v___x_2051_ = lean_st_ref_get(v___y_2049_);
v_infoState_2052_ = lean_ctor_get(v___x_2051_, 7);
lean_inc_ref(v_infoState_2052_);
lean_dec(v___x_2051_);
v_enabled_2053_ = lean_ctor_get_uint8(v_infoState_2052_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2052_);
if (v_enabled_2053_ == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec_ref(v_t_2048_);
v___x_2054_ = lean_box(0);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
else
{
lean_object* v___x_2056_; lean_object* v_infoState_2057_; lean_object* v_env_2058_; lean_object* v_nextMacroScope_2059_; lean_object* v_ngen_2060_; lean_object* v_auxDeclNGen_2061_; lean_object* v_traceState_2062_; lean_object* v_cache_2063_; lean_object* v_messages_2064_; lean_object* v_snapshotTasks_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2087_; 
v___x_2056_ = lean_st_ref_take(v___y_2049_);
v_infoState_2057_ = lean_ctor_get(v___x_2056_, 7);
v_env_2058_ = lean_ctor_get(v___x_2056_, 0);
v_nextMacroScope_2059_ = lean_ctor_get(v___x_2056_, 1);
v_ngen_2060_ = lean_ctor_get(v___x_2056_, 2);
v_auxDeclNGen_2061_ = lean_ctor_get(v___x_2056_, 3);
v_traceState_2062_ = lean_ctor_get(v___x_2056_, 4);
v_cache_2063_ = lean_ctor_get(v___x_2056_, 5);
v_messages_2064_ = lean_ctor_get(v___x_2056_, 6);
v_snapshotTasks_2065_ = lean_ctor_get(v___x_2056_, 8);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2067_ = v___x_2056_;
v_isShared_2068_ = v_isSharedCheck_2087_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_snapshotTasks_2065_);
lean_inc(v_infoState_2057_);
lean_inc(v_messages_2064_);
lean_inc(v_cache_2063_);
lean_inc(v_traceState_2062_);
lean_inc(v_auxDeclNGen_2061_);
lean_inc(v_ngen_2060_);
lean_inc(v_nextMacroScope_2059_);
lean_inc(v_env_2058_);
lean_dec(v___x_2056_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2087_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
uint8_t v_enabled_2069_; lean_object* v_assignment_2070_; lean_object* v_lazyAssignment_2071_; lean_object* v_trees_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2086_; 
v_enabled_2069_ = lean_ctor_get_uint8(v_infoState_2057_, sizeof(void*)*3);
v_assignment_2070_ = lean_ctor_get(v_infoState_2057_, 0);
v_lazyAssignment_2071_ = lean_ctor_get(v_infoState_2057_, 1);
v_trees_2072_ = lean_ctor_get(v_infoState_2057_, 2);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_infoState_2057_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2074_ = v_infoState_2057_;
v_isShared_2075_ = v_isSharedCheck_2086_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_trees_2072_);
lean_inc(v_lazyAssignment_2071_);
lean_inc(v_assignment_2070_);
lean_dec(v_infoState_2057_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2086_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = l_Lean_PersistentArray_push___redArg(v_trees_2072_, v_t_2048_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 2, v___x_2076_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_assignment_2070_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_lazyAssignment_2071_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v___x_2076_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*3, v_enabled_2069_);
v___x_2078_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2080_; 
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 7, v___x_2078_);
v___x_2080_ = v___x_2067_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_env_2058_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_nextMacroScope_2059_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_ngen_2060_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v_auxDeclNGen_2061_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v_traceState_2062_);
lean_ctor_set(v_reuseFailAlloc_2084_, 5, v_cache_2063_);
lean_ctor_set(v_reuseFailAlloc_2084_, 6, v_messages_2064_);
lean_ctor_set(v_reuseFailAlloc_2084_, 7, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2084_, 8, v_snapshotTasks_2065_);
v___x_2080_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = lean_st_ref_set(v___y_2049_, v___x_2080_);
v___x_2082_ = lean_box(0);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg___boxed(lean_object* v_t_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_2088_, v___y_2089_);
lean_dec(v___y_2089_);
return v_res_2091_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = lean_unsigned_to_nat(32u);
v___x_2093_ = lean_mk_empty_array_with_capacity(v___x_2092_);
v___x_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
return v___x_2094_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1(void){
_start:
{
size_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2095_ = ((size_t)5ULL);
v___x_2096_ = lean_unsigned_to_nat(0u);
v___x_2097_ = lean_unsigned_to_nat(32u);
v___x_2098_ = lean_mk_empty_array_with_capacity(v___x_2097_);
v___x_2099_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0);
v___x_2100_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
lean_ctor_set(v___x_2100_, 1, v___x_2098_);
lean_ctor_set(v___x_2100_, 2, v___x_2096_);
lean_ctor_set(v___x_2100_, 3, v___x_2096_);
lean_ctor_set_usize(v___x_2100_, 4, v___x_2095_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(lean_object* v_t_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2109_; lean_object* v_infoState_2110_; uint8_t v_enabled_2111_; 
v___x_2109_ = lean_st_ref_get(v___y_2107_);
v_infoState_2110_ = lean_ctor_get(v___x_2109_, 7);
lean_inc_ref(v_infoState_2110_);
lean_dec(v___x_2109_);
v_enabled_2111_ = lean_ctor_get_uint8(v_infoState_2110_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2110_);
if (v_enabled_2111_ == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec_ref(v_t_2101_);
v___x_2112_ = lean_box(0);
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
return v___x_2113_;
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1);
v___x_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2115_, 0, v_t_2101_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v___x_2115_, v___y_2107_);
return v___x_2116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___boxed(lean_object* v_t_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v_t_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
if (lean_obj_tag(v_a_2126_) == 0)
{
lean_object* v___x_2128_; 
v___x_2128_ = l_List_reverse___redArg(v_a_2127_);
return v___x_2128_;
}
else
{
lean_object* v_head_2129_; lean_object* v_tail_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2139_; 
v_head_2129_ = lean_ctor_get(v_a_2126_, 0);
v_tail_2130_ = lean_ctor_get(v_a_2126_, 1);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_a_2126_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2132_ = v_a_2126_;
v_isShared_2133_ = v_isSharedCheck_2139_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_tail_2130_);
lean_inc(v_head_2129_);
lean_dec(v_a_2126_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2139_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2134_ = l_Lean_mkLevelParam(v_head_2129_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 1, v_a_2127_);
lean_ctor_set(v___x_2132_, 0, v___x_2134_);
v___x_2136_ = v___x_2132_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_a_2127_);
v___x_2136_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
v_a_2126_ = v_tail_2130_;
v_a_2127_ = v___x_2136_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0(void){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2140_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0);
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
return v___x_2142_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
lean_ctor_set(v___x_2145_, 2, v___x_2144_);
lean_ctor_set(v___x_2145_, 3, v___x_2144_);
lean_ctor_set(v___x_2145_, 4, v___x_2143_);
lean_ctor_set(v___x_2145_, 5, v___x_2143_);
lean_ctor_set(v___x_2145_, 6, v___x_2143_);
lean_ctor_set(v___x_2145_, 7, v___x_2143_);
lean_ctor_set(v___x_2145_, 8, v___x_2143_);
lean_ctor_set(v___x_2145_, 9, v___x_2143_);
return v___x_2145_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2146_ = lean_box(1);
v___x_2147_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3);
v___x_2148_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
v___x_2149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
lean_ctor_set(v___x_2149_, 1, v___x_2147_);
lean_ctor_set(v___x_2149_, 2, v___x_2146_);
return v___x_2149_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4));
v___x_2152_ = l_Lean_stringToMessageData(v___x_2151_);
return v___x_2152_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6));
v___x_2155_ = l_Lean_stringToMessageData(v___x_2154_);
return v___x_2155_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8));
v___x_2158_ = l_Lean_stringToMessageData(v___x_2157_);
return v___x_2158_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10));
v___x_2161_ = l_Lean_stringToMessageData(v___x_2160_);
return v___x_2161_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12));
v___x_2164_ = l_Lean_stringToMessageData(v___x_2163_);
return v___x_2164_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14));
v___x_2167_ = l_Lean_stringToMessageData(v___x_2166_);
return v___x_2167_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16));
v___x_2170_ = l_Lean_stringToMessageData(v___x_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(lean_object* v_msg_2171_, lean_object* v_declHint_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v___x_2175_; lean_object* v_env_2176_; uint8_t v___x_2177_; 
v___x_2175_ = lean_st_ref_get(v___y_2173_);
v_env_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc_ref(v_env_2176_);
lean_dec(v___x_2175_);
v___x_2177_ = l_Lean_Name_isAnonymous(v_declHint_2172_);
if (v___x_2177_ == 0)
{
uint8_t v_isExporting_2178_; 
v_isExporting_2178_ = lean_ctor_get_uint8(v_env_2176_, sizeof(void*)*8);
if (v_isExporting_2178_ == 0)
{
lean_object* v___x_2179_; 
lean_dec_ref(v_env_2176_);
lean_dec(v_declHint_2172_);
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v_msg_2171_);
return v___x_2179_;
}
else
{
lean_object* v___x_2180_; uint8_t v___x_2181_; 
lean_inc_ref(v_env_2176_);
v___x_2180_ = l_Lean_Environment_setExporting(v_env_2176_, v___x_2177_);
lean_inc(v_declHint_2172_);
lean_inc_ref(v___x_2180_);
v___x_2181_ = l_Lean_Environment_contains(v___x_2180_, v_declHint_2172_, v_isExporting_2178_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; 
lean_dec_ref(v___x_2180_);
lean_dec_ref(v_env_2176_);
lean_dec(v_declHint_2172_);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v_msg_2171_);
return v___x_2182_;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v_c_2188_; lean_object* v___x_2189_; 
v___x_2183_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2);
v___x_2184_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3);
v___x_2185_ = l_Lean_Options_empty;
v___x_2186_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2180_);
lean_ctor_set(v___x_2186_, 1, v___x_2183_);
lean_ctor_set(v___x_2186_, 2, v___x_2184_);
lean_ctor_set(v___x_2186_, 3, v___x_2185_);
lean_inc(v_declHint_2172_);
v___x_2187_ = l_Lean_MessageData_ofConstName(v_declHint_2172_, v___x_2177_);
v_c_2188_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2188_, 0, v___x_2186_);
lean_ctor_set(v_c_2188_, 1, v___x_2187_);
v___x_2189_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2176_, v_declHint_2172_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_dec_ref(v_env_2176_);
lean_dec(v_declHint_2172_);
v___x_2190_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v_c_2188_);
v___x_2192_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7);
v___x_2193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2191_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = l_Lean_MessageData_note(v___x_2193_);
v___x_2195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2195_, 0, v_msg_2171_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
return v___x_2196_;
}
else
{
lean_object* v_val_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2232_; 
v_val_2197_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2199_ = v___x_2189_;
v_isShared_2200_ = v_isSharedCheck_2232_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_val_2197_);
lean_dec(v___x_2189_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2232_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v_mod_2204_; uint8_t v___x_2205_; 
v___x_2201_ = lean_box(0);
v___x_2202_ = l_Lean_Environment_header(v_env_2176_);
lean_dec_ref(v_env_2176_);
v___x_2203_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2202_);
v_mod_2204_ = lean_array_get(v___x_2201_, v___x_2203_, v_val_2197_);
lean_dec(v_val_2197_);
lean_dec_ref(v___x_2203_);
v___x_2205_ = l_Lean_isPrivateName(v_declHint_2172_);
lean_dec(v_declHint_2172_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2206_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9);
v___x_2207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set(v___x_2207_, 1, v_c_2188_);
v___x_2208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11);
v___x_2209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = l_Lean_MessageData_ofName(v_mod_2204_);
v___x_2211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2209_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13);
v___x_2213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2211_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = l_Lean_MessageData_note(v___x_2213_);
v___x_2215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2215_, 0, v_msg_2171_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set_tag(v___x_2199_, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2215_);
v___x_2217_ = v___x_2199_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2219_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5);
v___x_2220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set(v___x_2220_, 1, v_c_2188_);
v___x_2221_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = l_Lean_MessageData_ofName(v_mod_2204_);
v___x_2224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17);
v___x_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2224_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
v___x_2227_ = l_Lean_MessageData_note(v___x_2226_);
v___x_2228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2228_, 0, v_msg_2171_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set_tag(v___x_2199_, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2228_);
v___x_2230_ = v___x_2199_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2233_; 
lean_dec_ref(v_env_2176_);
lean_dec(v_declHint_2172_);
v___x_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2233_, 0, v_msg_2171_);
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___boxed(lean_object* v_msg_2234_, lean_object* v_declHint_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2234_, v_declHint_2235_, v___y_2236_);
lean_dec(v___y_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(lean_object* v_msg_2239_, lean_object* v_declHint_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2258_; 
v___x_2248_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2239_, v_declHint_2240_, v___y_2246_);
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2251_ = v___x_2248_;
v_isShared_2252_ = v_isSharedCheck_2258_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2258_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2253_ = l_Lean_unknownIdentifierMessageTag;
v___x_2254_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
lean_ctor_set(v___x_2254_, 1, v_a_2249_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2254_);
v___x_2256_ = v___x_2251_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23___boxed(lean_object* v_msg_2259_, lean_object* v_declHint_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2259_, v_declHint_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(lean_object* v_ref_2269_, lean_object* v_msg_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_fileName_2278_; lean_object* v_fileMap_2279_; lean_object* v_options_2280_; lean_object* v_currRecDepth_2281_; lean_object* v_maxRecDepth_2282_; lean_object* v_ref_2283_; lean_object* v_currNamespace_2284_; lean_object* v_openDecls_2285_; lean_object* v_initHeartbeats_2286_; lean_object* v_maxHeartbeats_2287_; lean_object* v_quotContext_2288_; lean_object* v_currMacroScope_2289_; uint8_t v_diag_2290_; lean_object* v_cancelTk_x3f_2291_; uint8_t v_suppressElabErrors_2292_; lean_object* v_inheritedTraceOptions_2293_; lean_object* v_ref_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v_fileName_2278_ = lean_ctor_get(v___y_2275_, 0);
v_fileMap_2279_ = lean_ctor_get(v___y_2275_, 1);
v_options_2280_ = lean_ctor_get(v___y_2275_, 2);
v_currRecDepth_2281_ = lean_ctor_get(v___y_2275_, 3);
v_maxRecDepth_2282_ = lean_ctor_get(v___y_2275_, 4);
v_ref_2283_ = lean_ctor_get(v___y_2275_, 5);
v_currNamespace_2284_ = lean_ctor_get(v___y_2275_, 6);
v_openDecls_2285_ = lean_ctor_get(v___y_2275_, 7);
v_initHeartbeats_2286_ = lean_ctor_get(v___y_2275_, 8);
v_maxHeartbeats_2287_ = lean_ctor_get(v___y_2275_, 9);
v_quotContext_2288_ = lean_ctor_get(v___y_2275_, 10);
v_currMacroScope_2289_ = lean_ctor_get(v___y_2275_, 11);
v_diag_2290_ = lean_ctor_get_uint8(v___y_2275_, sizeof(void*)*14);
v_cancelTk_x3f_2291_ = lean_ctor_get(v___y_2275_, 12);
v_suppressElabErrors_2292_ = lean_ctor_get_uint8(v___y_2275_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2293_ = lean_ctor_get(v___y_2275_, 13);
v_ref_2294_ = l_Lean_replaceRef(v_ref_2269_, v_ref_2283_);
lean_inc_ref(v_inheritedTraceOptions_2293_);
lean_inc(v_cancelTk_x3f_2291_);
lean_inc(v_currMacroScope_2289_);
lean_inc(v_quotContext_2288_);
lean_inc(v_maxHeartbeats_2287_);
lean_inc(v_initHeartbeats_2286_);
lean_inc(v_openDecls_2285_);
lean_inc(v_currNamespace_2284_);
lean_inc(v_maxRecDepth_2282_);
lean_inc(v_currRecDepth_2281_);
lean_inc_ref(v_options_2280_);
lean_inc_ref(v_fileMap_2279_);
lean_inc_ref(v_fileName_2278_);
v___x_2295_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2295_, 0, v_fileName_2278_);
lean_ctor_set(v___x_2295_, 1, v_fileMap_2279_);
lean_ctor_set(v___x_2295_, 2, v_options_2280_);
lean_ctor_set(v___x_2295_, 3, v_currRecDepth_2281_);
lean_ctor_set(v___x_2295_, 4, v_maxRecDepth_2282_);
lean_ctor_set(v___x_2295_, 5, v_ref_2294_);
lean_ctor_set(v___x_2295_, 6, v_currNamespace_2284_);
lean_ctor_set(v___x_2295_, 7, v_openDecls_2285_);
lean_ctor_set(v___x_2295_, 8, v_initHeartbeats_2286_);
lean_ctor_set(v___x_2295_, 9, v_maxHeartbeats_2287_);
lean_ctor_set(v___x_2295_, 10, v_quotContext_2288_);
lean_ctor_set(v___x_2295_, 11, v_currMacroScope_2289_);
lean_ctor_set(v___x_2295_, 12, v_cancelTk_x3f_2291_);
lean_ctor_set(v___x_2295_, 13, v_inheritedTraceOptions_2293_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*14, v_diag_2290_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*14 + 1, v_suppressElabErrors_2292_);
v___x_2296_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___x_2295_, v___y_2276_);
lean_dec_ref(v___x_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg___boxed(lean_object* v_ref_2297_, lean_object* v_msg_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2297_, v_msg_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v_ref_2297_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(lean_object* v_ref_2307_, lean_object* v_msg_2308_, lean_object* v_declHint_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v___x_2317_; lean_object* v_a_2318_; lean_object* v___x_2319_; 
v___x_2317_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2308_, v_declHint_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref(v___x_2317_);
v___x_2319_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2307_, v_a_2318_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg___boxed(lean_object* v_ref_2320_, lean_object* v_msg_2321_, lean_object* v_declHint_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2320_, v_msg_2321_, v_declHint_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v_ref_2320_);
return v_res_2330_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0));
v___x_2333_ = l_Lean_stringToMessageData(v___x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(lean_object* v_ref_2334_, lean_object* v_constName_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v___x_2343_; uint8_t v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2343_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1);
v___x_2344_ = 0;
lean_inc(v_constName_2335_);
v___x_2345_ = l_Lean_MessageData_ofConstName(v_constName_2335_, v___x_2344_);
v___x_2346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2343_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
v___x_2347_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2346_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2334_, v___x_2348_, v_constName_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___boxed(lean_object* v_ref_2350_, lean_object* v_constName_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2350_, v_constName_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v_ref_2350_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(lean_object* v_constName_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_ref_2368_; lean_object* v___x_2369_; 
v_ref_2368_ = lean_ctor_get(v___y_2365_, 5);
v___x_2369_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2368_, v_constName_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_constName_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(lean_object* v_constName_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v___x_2387_; lean_object* v_env_2388_; uint8_t v___x_2389_; lean_object* v___x_2390_; 
v___x_2387_ = lean_st_ref_get(v___y_2385_);
v_env_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc_ref(v_env_2388_);
lean_dec(v___x_2387_);
v___x_2389_ = 0;
lean_inc(v_constName_2379_);
v___x_2390_ = l_Lean_Environment_findConstVal_x3f(v_env_2388_, v_constName_2379_, v___x_2389_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2391_;
}
else
{
lean_object* v_val_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec(v_constName_2379_);
v_val_2392_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2390_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_val_2392_);
lean_dec(v___x_2390_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
lean_ctor_set_tag(v___x_2394_, 0);
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_val_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14___boxed(lean_object* v_constName_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(lean_object* v_constName_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v___x_2417_; 
lean_inc(v_constName_2409_);
v___x_2417_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2429_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2429_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2429_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v_levelParams_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
v_levelParams_2422_ = lean_ctor_get(v_a_2418_, 1);
lean_inc(v_levelParams_2422_);
lean_dec(v_a_2418_);
v___x_2423_ = lean_box(0);
v___x_2424_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(v_levelParams_2422_, v___x_2423_);
v___x_2425_ = l_Lean_mkConst(v_constName_2409_, v___x_2424_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2425_);
v___x_2427_ = v___x_2420_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v_constName_2409_);
v_a_2430_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2417_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2417_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_constName_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_constName_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(uint8_t v___x_2447_, lean_object* v_declName_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_ref_2456_; lean_object* v___x_2457_; 
v_ref_2456_ = lean_ctor_get(v___y_2453_, 5);
v___x_2457_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_declName_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref(v___x_2457_);
v___x_2459_ = lean_box(0);
lean_inc(v_ref_2456_);
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
lean_ctor_set(v___x_2460_, 1, v_ref_2456_);
v___x_2461_ = lean_unsigned_to_nat(32u);
v___x_2462_ = lean_mk_empty_array_with_capacity(v___x_2461_);
lean_dec_ref(v___x_2462_);
v___x_2463_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4);
v___x_2464_ = lean_box(0);
v___x_2465_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2465_, 0, v___x_2460_);
lean_ctor_set(v___x_2465_, 1, v___x_2463_);
lean_ctor_set(v___x_2465_, 2, v___x_2464_);
lean_ctor_set(v___x_2465_, 3, v_a_2458_);
lean_ctor_set_uint8(v___x_2465_, sizeof(void*)*4, v___x_2447_);
lean_ctor_set_uint8(v___x_2465_, sizeof(void*)*4 + 1, v___x_2447_);
v___x_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
v___x_2467_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v___x_2466_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
return v___x_2467_;
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
v_a_2468_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2457_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2457_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v___x_2476_, lean_object* v_declName_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
uint8_t v___x_18250__boxed_2485_; lean_object* v_res_2486_; 
v___x_18250__boxed_2485_ = lean_unbox(v___x_2476_);
v_res_2486_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(v___x_18250__boxed_2485_, v_declName_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(lean_object* v___f_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; lean_object* v_env_2496_; lean_object* v___x_2497_; 
v___x_2495_ = lean_st_ref_get(v___y_2493_);
v_env_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc_ref(v_env_2496_);
lean_dec(v___x_2495_);
v___x_2497_ = lean_apply_8(v___f_2487_, v_env_2496_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, lean_box(0));
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed(lean_object* v___f_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(v___f_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v_res_2506_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2507_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
return v___x_2511_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
v___x_2513_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
lean_ctor_set(v___x_2513_, 2, v___x_2512_);
lean_ctor_set(v___x_2513_, 3, v___x_2512_);
lean_ctor_set(v___x_2513_, 4, v___x_2512_);
lean_ctor_set(v___x_2513_, 5, v___x_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(lean_object* v_env_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; lean_object* v_nextMacroScope_2519_; lean_object* v_ngen_2520_; lean_object* v_auxDeclNGen_2521_; lean_object* v_traceState_2522_; lean_object* v_messages_2523_; lean_object* v_infoState_2524_; lean_object* v_snapshotTasks_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2551_; 
v___x_2518_ = lean_st_ref_take(v___y_2516_);
v_nextMacroScope_2519_ = lean_ctor_get(v___x_2518_, 1);
v_ngen_2520_ = lean_ctor_get(v___x_2518_, 2);
v_auxDeclNGen_2521_ = lean_ctor_get(v___x_2518_, 3);
v_traceState_2522_ = lean_ctor_get(v___x_2518_, 4);
v_messages_2523_ = lean_ctor_get(v___x_2518_, 6);
v_infoState_2524_ = lean_ctor_get(v___x_2518_, 7);
v_snapshotTasks_2525_ = lean_ctor_get(v___x_2518_, 8);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2551_ == 0)
{
lean_object* v_unused_2552_; lean_object* v_unused_2553_; 
v_unused_2552_ = lean_ctor_get(v___x_2518_, 5);
lean_dec(v_unused_2552_);
v_unused_2553_ = lean_ctor_get(v___x_2518_, 0);
lean_dec(v_unused_2553_);
v___x_2527_ = v___x_2518_;
v_isShared_2528_ = v_isSharedCheck_2551_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_snapshotTasks_2525_);
lean_inc(v_infoState_2524_);
lean_inc(v_messages_2523_);
lean_inc(v_traceState_2522_);
lean_inc(v_auxDeclNGen_2521_);
lean_inc(v_ngen_2520_);
lean_inc(v_nextMacroScope_2519_);
lean_dec(v___x_2518_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2551_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2529_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 5, v___x_2529_);
lean_ctor_set(v___x_2527_, 0, v_env_2514_);
v___x_2531_ = v___x_2527_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_env_2514_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_nextMacroScope_2519_);
lean_ctor_set(v_reuseFailAlloc_2550_, 2, v_ngen_2520_);
lean_ctor_set(v_reuseFailAlloc_2550_, 3, v_auxDeclNGen_2521_);
lean_ctor_set(v_reuseFailAlloc_2550_, 4, v_traceState_2522_);
lean_ctor_set(v_reuseFailAlloc_2550_, 5, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2550_, 6, v_messages_2523_);
lean_ctor_set(v_reuseFailAlloc_2550_, 7, v_infoState_2524_);
lean_ctor_set(v_reuseFailAlloc_2550_, 8, v_snapshotTasks_2525_);
v___x_2531_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v_mctx_2534_; lean_object* v_zetaDeltaFVarIds_2535_; lean_object* v_postponed_2536_; lean_object* v_diag_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2548_; 
v___x_2532_ = lean_st_ref_set(v___y_2516_, v___x_2531_);
v___x_2533_ = lean_st_ref_take(v___y_2515_);
v_mctx_2534_ = lean_ctor_get(v___x_2533_, 0);
v_zetaDeltaFVarIds_2535_ = lean_ctor_get(v___x_2533_, 2);
v_postponed_2536_ = lean_ctor_get(v___x_2533_, 3);
v_diag_2537_ = lean_ctor_get(v___x_2533_, 4);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2548_ == 0)
{
lean_object* v_unused_2549_; 
v_unused_2549_ = lean_ctor_get(v___x_2533_, 1);
lean_dec(v_unused_2549_);
v___x_2539_ = v___x_2533_;
v_isShared_2540_ = v_isSharedCheck_2548_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_diag_2537_);
lean_inc(v_postponed_2536_);
lean_inc(v_zetaDeltaFVarIds_2535_);
lean_inc(v_mctx_2534_);
lean_dec(v___x_2533_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2548_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2541_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 1, v___x_2541_);
v___x_2543_ = v___x_2539_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_mctx_2534_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2547_, 2, v_zetaDeltaFVarIds_2535_);
lean_ctor_set(v_reuseFailAlloc_2547_, 3, v_postponed_2536_);
lean_ctor_set(v_reuseFailAlloc_2547_, 4, v_diag_2537_);
v___x_2543_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = lean_st_ref_set(v___y_2515_, v___x_2543_);
v___x_2545_ = lean_box(0);
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
return v___x_2546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___boxed(lean_object* v_env_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec(v___y_2555_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(lean_object* v_env_2559_, lean_object* v_x_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v___x_2568_; lean_object* v_env_2569_; lean_object* v_a_2571_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2568_ = lean_st_ref_get(v___y_2566_);
v_env_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc_ref(v_env_2569_);
lean_dec(v___x_2568_);
v___x_2581_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2559_, v___y_2564_, v___y_2566_);
lean_dec_ref(v___x_2581_);
lean_inc(v___y_2566_);
lean_inc_ref(v___y_2565_);
lean_inc(v___y_2564_);
lean_inc_ref(v___y_2563_);
lean_inc(v___y_2562_);
lean_inc_ref(v___y_2561_);
v___x_2582_ = lean_apply_7(v_x_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, lean_box(0));
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref(v___x_2582_);
v___x_2584_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2569_, v___y_2564_, v___y_2566_);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2591_ == 0)
{
lean_object* v_unused_2592_; 
v_unused_2592_ = lean_ctor_get(v___x_2584_, 0);
lean_dec(v_unused_2592_);
v___x_2586_ = v___x_2584_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_dec(v___x_2584_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v_a_2583_);
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2583_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
else
{
lean_object* v_a_2593_; 
v_a_2593_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2593_);
lean_dec_ref(v___x_2582_);
v_a_2571_ = v_a_2593_;
goto v___jp_2570_;
}
v___jp_2570_:
{
lean_object* v___x_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
v___x_2572_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2569_, v___y_2564_, v___y_2566_);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; 
v_unused_2580_ = lean_ctor_get(v___x_2572_, 0);
lean_dec(v_unused_2580_);
v___x_2574_ = v___x_2572_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_dec(v___x_2572_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
lean_ctor_set_tag(v___x_2574_, 1);
lean_ctor_set(v___x_2574_, 0, v_a_2571_);
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2571_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_env_2594_, lean_object* v_x_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2594_, v_x_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(lean_object* v_declName_2604_, lean_object* v_env_2605_, lean_object* v_addInfo_2606_, lean_object* v_____r_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = lean_private_to_user_name(v_declName_2604_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_dec_ref(v_addInfo_2606_);
lean_dec_ref(v_env_2605_);
v___x_2616_ = lean_box(0);
v___x_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
return v___x_2617_;
}
else
{
lean_object* v_val_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2635_; 
v_val_2618_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2620_ = v___x_2615_;
v_isShared_2621_ = v_isSharedCheck_2635_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_val_2618_);
lean_dec(v___x_2615_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2635_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
uint8_t v___x_2622_; uint8_t v___x_2623_; 
v___x_2622_ = 1;
lean_inc(v_val_2618_);
v___x_2623_ = l_Lean_Environment_contains(v_env_2605_, v_val_2618_, v___x_2622_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
lean_dec(v_val_2618_);
lean_dec_ref(v_addInfo_2606_);
v___x_2624_ = lean_box(0);
if (v_isShared_2621_ == 0)
{
lean_ctor_set_tag(v___x_2620_, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2624_);
v___x_2626_ = v___x_2620_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
else
{
lean_object* v___x_2628_; 
lean_del_object(v___x_2620_);
lean_inc(v___y_2613_);
lean_inc_ref(v___y_2612_);
lean_inc(v___y_2611_);
lean_inc_ref(v___y_2610_);
lean_inc(v___y_2609_);
lean_inc_ref(v___y_2608_);
lean_inc(v_val_2618_);
v___x_2628_ = lean_apply_8(v_addInfo_2606_, v_val_2618_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, lean_box(0));
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
lean_dec_ref(v___x_2628_);
v___x_2629_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
v___x_2630_ = l_Lean_MessageData_ofConstName(v_val_2618_, v___x_2622_);
v___x_2631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2629_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2631_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2633_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
return v___x_2634_;
}
else
{
lean_dec(v_val_2618_);
return v___x_2628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed(lean_object* v_declName_2636_, lean_object* v_env_2637_, lean_object* v_addInfo_2638_, lean_object* v_____r_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(v_declName_2636_, v_env_2637_, v_addInfo_2638_, v_____r_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(lean_object* v_addInfo_2648_, lean_object* v_declName_2649_, uint8_t v___x_2650_, lean_object* v___f_2651_, uint8_t v___x_2652_, lean_object* v_env_2653_, lean_object* v___f_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v___x_2662_; 
lean_inc(v___y_2660_);
lean_inc_ref(v___y_2659_);
lean_inc(v___y_2658_);
lean_inc_ref(v___y_2657_);
lean_inc(v___y_2656_);
lean_inc_ref(v___y_2655_);
lean_inc(v_declName_2649_);
v___x_2662_ = lean_apply_8(v_addInfo_2648_, v_declName_2649_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, lean_box(0));
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v___x_2663_; 
lean_dec_ref(v___x_2662_);
lean_inc(v_declName_2649_);
v___x_2663_ = lean_private_to_user_name(v_declName_2649_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2664_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2665_ = l_Lean_MessageData_ofConstName(v_declName_2649_, v___x_2650_);
v___x_2666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2666_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2668_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
return v___x_2669_;
}
else
{
lean_object* v_val_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
lean_dec(v_declName_2649_);
v_val_2670_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_val_2670_);
lean_dec_ref(v___x_2663_);
v___x_2671_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1);
v___x_2672_ = l_Lean_MessageData_ofConstName(v_val_2670_, v___x_2650_);
v___x_2673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2671_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2673_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
v___x_2676_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2675_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
return v___x_2676_;
}
}
else
{
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v_declName_2649_);
return v___x_2662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed(lean_object* v_addInfo_2677_, lean_object* v_declName_2678_, lean_object* v___x_2679_, lean_object* v___f_2680_, lean_object* v___x_2681_, lean_object* v_env_2682_, lean_object* v___f_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v___x_18604__boxed_2691_; uint8_t v___x_18606__boxed_2692_; lean_object* v_res_2693_; 
v___x_18604__boxed_2691_ = lean_unbox(v___x_2679_);
v___x_18606__boxed_2692_ = lean_unbox(v___x_2681_);
v_res_2693_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(v_addInfo_2677_, v_declName_2678_, v___x_18604__boxed_2691_, v___f_2680_, v___x_18606__boxed_2692_, v_env_2682_, v___f_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec_ref(v___f_2683_);
lean_dec_ref(v_env_2682_);
lean_dec_ref(v___f_2680_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(lean_object* v_declName_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v___x_2705_; lean_object* v_env_2706_; uint8_t v___x_2707_; lean_object* v_addInfo_2708_; lean_object* v_env_2709_; lean_object* v___f_2710_; lean_object* v___f_2711_; lean_object* v___x_2712_; lean_object* v___f_2713_; uint8_t v___x_2714_; uint8_t v___x_2715_; 
v___x_2705_ = lean_st_ref_get(v___y_2703_);
v_env_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc_ref(v_env_2706_);
lean_dec(v___x_2705_);
v___x_2707_ = 0;
v_addInfo_2708_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0));
v_env_2709_ = l_Lean_Environment_setExporting(v_env_2706_, v___x_2707_);
lean_inc_ref_n(v_env_2709_, 4);
lean_inc_n(v_declName_2697_, 4);
v___f_2710_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed), 11, 3);
lean_closure_set(v___f_2710_, 0, v_declName_2697_);
lean_closure_set(v___f_2710_, 1, v_env_2709_);
lean_closure_set(v___f_2710_, 2, v_addInfo_2708_);
v___f_2711_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2711_, 0, v_env_2709_);
lean_closure_set(v___f_2711_, 1, v_declName_2697_);
lean_closure_set(v___f_2711_, 2, v___f_2710_);
lean_closure_set(v___f_2711_, 3, v_addInfo_2708_);
v___x_2712_ = lean_box(v___x_2707_);
lean_inc_ref(v___f_2711_);
v___f_2713_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed), 12, 4);
lean_closure_set(v___f_2713_, 0, v___f_2711_);
lean_closure_set(v___f_2713_, 1, v_declName_2697_);
lean_closure_set(v___f_2713_, 2, v___x_2712_);
lean_closure_set(v___f_2713_, 3, v_env_2709_);
v___x_2714_ = 1;
v___x_2715_ = l_Lean_Environment_contains(v_env_2709_, v_declName_2697_, v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___f_2716_; lean_object* v___x_2717_; 
lean_dec_ref(v___f_2711_);
lean_dec(v_declName_2697_);
v___f_2716_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed), 8, 1);
lean_closure_set(v___f_2716_, 0, v___f_2713_);
v___x_2717_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2709_, v___f_2716_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
return v___x_2717_;
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___f_2720_; lean_object* v___x_2721_; 
v___x_2718_ = lean_box(v___x_2714_);
v___x_2719_ = lean_box(v___x_2707_);
lean_inc_ref(v_env_2709_);
v___f_2720_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed), 14, 7);
lean_closure_set(v___f_2720_, 0, v_addInfo_2708_);
lean_closure_set(v___f_2720_, 1, v_declName_2697_);
lean_closure_set(v___f_2720_, 2, v___x_2718_);
lean_closure_set(v___f_2720_, 3, v___f_2711_);
lean_closure_set(v___f_2720_, 4, v___x_2719_);
lean_closure_set(v___f_2720_, 5, v_env_2709_);
lean_closure_set(v___f_2720_, 6, v___f_2713_);
v___x_2721_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2709_, v___f_2720_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
return v___x_2721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___boxed(lean_object* v_declName_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(lean_object* v_modifiers_2731_, lean_object* v_declName_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; lean_object* v_env_2741_; uint8_t v_visibility_2742_; uint8_t v_isProtected_2743_; lean_object* v_declName_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; uint8_t v___x_2807_; 
v___x_2740_ = lean_st_ref_get(v___y_2738_);
v_env_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc_ref(v_env_2741_);
lean_dec(v___x_2740_);
v_visibility_2742_ = lean_ctor_get_uint8(v_modifiers_2731_, sizeof(void*)*3);
v_isProtected_2743_ = lean_ctor_get_uint8(v_modifiers_2731_, sizeof(void*)*3 + 1);
v___x_2807_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_2741_, v_visibility_2742_);
lean_dec_ref(v_env_2741_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; lean_object* v_env_2809_; lean_object* v_declName_2810_; 
v___x_2808_ = lean_st_ref_get(v___y_2738_);
v_env_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc_ref(v_env_2809_);
lean_dec(v___x_2808_);
v_declName_2810_ = l_Lean_mkPrivateName(v_env_2809_, v_declName_2732_);
lean_dec_ref(v_env_2809_);
v_declName_2745_ = v_declName_2810_;
v___y_2746_ = v___y_2733_;
v___y_2747_ = v___y_2734_;
v___y_2748_ = v___y_2735_;
v___y_2749_ = v___y_2736_;
v___y_2750_ = v___y_2737_;
v___y_2751_ = v___y_2738_;
goto v___jp_2744_;
}
else
{
v_declName_2745_ = v_declName_2732_;
v___y_2746_ = v___y_2733_;
v___y_2747_ = v___y_2734_;
v___y_2748_ = v___y_2735_;
v___y_2749_ = v___y_2736_;
v___y_2750_ = v___y_2737_;
v___y_2751_ = v___y_2738_;
goto v___jp_2744_;
}
v___jp_2744_:
{
lean_object* v___x_2752_; 
lean_inc(v_declName_2745_);
v___x_2752_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2797_; 
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2797_ == 0)
{
lean_object* v_unused_2798_; 
v_unused_2798_ = lean_ctor_get(v___x_2752_, 0);
lean_dec(v_unused_2798_);
v___x_2754_ = v___x_2752_;
v_isShared_2755_ = v_isSharedCheck_2797_;
goto v_resetjp_2753_;
}
else
{
lean_dec(v___x_2752_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2797_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
if (v_isProtected_2743_ == 0)
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v_declName_2745_);
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_declName_2745_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
else
{
lean_object* v___x_2759_; lean_object* v_env_2760_; lean_object* v_nextMacroScope_2761_; lean_object* v_ngen_2762_; lean_object* v_auxDeclNGen_2763_; lean_object* v_traceState_2764_; lean_object* v_messages_2765_; lean_object* v_infoState_2766_; lean_object* v_snapshotTasks_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2795_; 
v___x_2759_ = lean_st_ref_take(v___y_2751_);
v_env_2760_ = lean_ctor_get(v___x_2759_, 0);
v_nextMacroScope_2761_ = lean_ctor_get(v___x_2759_, 1);
v_ngen_2762_ = lean_ctor_get(v___x_2759_, 2);
v_auxDeclNGen_2763_ = lean_ctor_get(v___x_2759_, 3);
v_traceState_2764_ = lean_ctor_get(v___x_2759_, 4);
v_messages_2765_ = lean_ctor_get(v___x_2759_, 6);
v_infoState_2766_ = lean_ctor_get(v___x_2759_, 7);
v_snapshotTasks_2767_ = lean_ctor_get(v___x_2759_, 8);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2795_ == 0)
{
lean_object* v_unused_2796_; 
v_unused_2796_ = lean_ctor_get(v___x_2759_, 5);
lean_dec(v_unused_2796_);
v___x_2769_ = v___x_2759_;
v_isShared_2770_ = v_isSharedCheck_2795_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_snapshotTasks_2767_);
lean_inc(v_infoState_2766_);
lean_inc(v_messages_2765_);
lean_inc(v_traceState_2764_);
lean_inc(v_auxDeclNGen_2763_);
lean_inc(v_ngen_2762_);
lean_inc(v_nextMacroScope_2761_);
lean_inc(v_env_2760_);
lean_dec(v___x_2759_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2795_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
lean_inc(v_declName_2745_);
v___x_2771_ = l_Lean_addProtected(v_env_2760_, v_declName_2745_);
v___x_2772_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 5, v___x_2772_);
lean_ctor_set(v___x_2769_, 0, v___x_2771_);
v___x_2774_ = v___x_2769_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_nextMacroScope_2761_);
lean_ctor_set(v_reuseFailAlloc_2794_, 2, v_ngen_2762_);
lean_ctor_set(v_reuseFailAlloc_2794_, 3, v_auxDeclNGen_2763_);
lean_ctor_set(v_reuseFailAlloc_2794_, 4, v_traceState_2764_);
lean_ctor_set(v_reuseFailAlloc_2794_, 5, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2794_, 6, v_messages_2765_);
lean_ctor_set(v_reuseFailAlloc_2794_, 7, v_infoState_2766_);
lean_ctor_set(v_reuseFailAlloc_2794_, 8, v_snapshotTasks_2767_);
v___x_2774_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v_mctx_2777_; lean_object* v_zetaDeltaFVarIds_2778_; lean_object* v_postponed_2779_; lean_object* v_diag_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2792_; 
v___x_2775_ = lean_st_ref_set(v___y_2751_, v___x_2774_);
v___x_2776_ = lean_st_ref_take(v___y_2749_);
v_mctx_2777_ = lean_ctor_get(v___x_2776_, 0);
v_zetaDeltaFVarIds_2778_ = lean_ctor_get(v___x_2776_, 2);
v_postponed_2779_ = lean_ctor_get(v___x_2776_, 3);
v_diag_2780_ = lean_ctor_get(v___x_2776_, 4);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2792_ == 0)
{
lean_object* v_unused_2793_; 
v_unused_2793_ = lean_ctor_get(v___x_2776_, 1);
lean_dec(v_unused_2793_);
v___x_2782_ = v___x_2776_;
v_isShared_2783_ = v_isSharedCheck_2792_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_diag_2780_);
lean_inc(v_postponed_2779_);
lean_inc(v_zetaDeltaFVarIds_2778_);
lean_inc(v_mctx_2777_);
lean_dec(v___x_2776_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2792_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2784_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 1, v___x_2784_);
v___x_2786_ = v___x_2782_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_mctx_2777_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2791_, 2, v_zetaDeltaFVarIds_2778_);
lean_ctor_set(v_reuseFailAlloc_2791_, 3, v_postponed_2779_);
lean_ctor_set(v_reuseFailAlloc_2791_, 4, v_diag_2780_);
v___x_2786_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2787_ = lean_st_ref_set(v___y_2749_, v___x_2786_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v_declName_2745_);
v___x_2789_ = v___x_2754_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_declName_2745_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
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
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_declName_2745_);
v_a_2799_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2752_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2752_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4___boxed(lean_object* v_modifiers_2811_, lean_object* v_declName_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2811_, v_declName_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec_ref(v_modifiers_2811_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(lean_object* v_pre_2821_, lean_object* v_declName_2822_, lean_object* v_as_2823_, size_t v_sz_2824_, size_t v_i_2825_, lean_object* v_b_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_a_2835_; uint8_t v___x_2839_; 
v___x_2839_ = lean_usize_dec_lt(v_i_2825_, v_sz_2824_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; 
lean_dec(v_declName_2822_);
lean_dec(v_pre_2821_);
v___x_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2840_, 0, v_b_2826_);
return v___x_2840_;
}
else
{
lean_object* v___x_2841_; lean_object* v_a_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2841_ = lean_box(0);
v_a_2842_ = lean_array_uget_borrowed(v_as_2823_, v_i_2825_);
lean_inc(v_a_2842_);
lean_inc(v_pre_2821_);
v___x_2843_ = l_Lean_Name_append(v_pre_2821_, v_a_2842_);
v___x_2844_ = lean_name_eq(v___x_2843_, v_declName_2822_);
lean_dec(v___x_2843_);
if (v___x_2844_ == 0)
{
v_a_2835_ = v___x_2841_;
goto v___jp_2834_;
}
else
{
lean_object* v___x_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2845_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_2846_ = 0;
lean_inc(v_declName_2822_);
v___x_2847_ = l_Lean_MessageData_ofConstName(v_declName_2822_, v___x_2846_);
v___x_2848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2845_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
v___x_2849_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_2850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2848_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
lean_inc(v_pre_2821_);
v___x_2851_ = l_Lean_MessageData_ofName(v_pre_2821_);
v___x_2852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2850_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
v___x_2853_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_2854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2852_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
lean_inc(v_a_2842_);
v___x_2855_ = l_Lean_MessageData_ofName(v_a_2842_);
v___x_2856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2858_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_dec_ref(v___x_2859_);
v_a_2835_ = v___x_2841_;
goto v___jp_2834_;
}
else
{
lean_dec(v_declName_2822_);
lean_dec(v_pre_2821_);
return v___x_2859_;
}
}
}
v___jp_2834_:
{
size_t v___x_2836_; size_t v___x_2837_; 
v___x_2836_ = ((size_t)1ULL);
v___x_2837_ = lean_usize_add(v_i_2825_, v___x_2836_);
v_i_2825_ = v___x_2837_;
v_b_2826_ = v_a_2835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6___boxed(lean_object* v_pre_2860_, lean_object* v_declName_2861_, lean_object* v_as_2862_, lean_object* v_sz_2863_, lean_object* v_i_2864_, lean_object* v_b_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
size_t v_sz_boxed_2873_; size_t v_i_boxed_2874_; lean_object* v_res_2875_; 
v_sz_boxed_2873_ = lean_unbox_usize(v_sz_2863_);
lean_dec(v_sz_2863_);
v_i_boxed_2874_ = lean_unbox_usize(v_i_2864_);
lean_dec(v_i_2864_);
v_res_2875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2860_, v_declName_2861_, v_as_2862_, v_sz_boxed_2873_, v_i_boxed_2874_, v_b_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec_ref(v_as_2862_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(lean_object* v_declName_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
if (lean_obj_tag(v_declName_2876_) == 1)
{
lean_object* v_pre_2884_; lean_object* v___x_2885_; lean_object* v_env_2886_; uint8_t v___x_2887_; 
v_pre_2884_ = lean_ctor_get(v_declName_2876_, 0);
lean_inc_n(v_pre_2884_, 2);
v___x_2885_ = lean_st_ref_get(v___y_2882_);
v_env_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc_ref(v_env_2886_);
lean_dec(v___x_2885_);
v___x_2887_ = l_Lean_isStructure(v_env_2886_, v_pre_2884_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
lean_dec_ref(v_declName_2876_);
lean_dec(v_pre_2884_);
v___x_2888_ = lean_box(0);
v___x_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
return v___x_2889_;
}
else
{
lean_object* v___x_2890_; lean_object* v_env_2891_; lean_object* v_fieldNames_2892_; lean_object* v___x_2893_; size_t v_sz_2894_; size_t v___x_2895_; lean_object* v___x_2896_; 
v___x_2890_ = lean_st_ref_get(v___y_2882_);
v_env_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc_ref(v_env_2891_);
lean_dec(v___x_2890_);
lean_inc(v_pre_2884_);
v_fieldNames_2892_ = l_Lean_getStructureFieldsFlattened(v_env_2891_, v_pre_2884_, v___x_2887_);
v___x_2893_ = lean_box(0);
v_sz_2894_ = lean_array_size(v_fieldNames_2892_);
v___x_2895_ = ((size_t)0ULL);
v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2884_, v_declName_2876_, v_fieldNames_2892_, v_sz_2894_, v___x_2895_, v___x_2893_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec_ref(v_fieldNames_2892_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2903_ == 0)
{
lean_object* v_unused_2904_; 
v_unused_2904_ = lean_ctor_get(v___x_2896_, 0);
lean_dec(v_unused_2904_);
v___x_2898_ = v___x_2896_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_dec(v___x_2896_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2893_);
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2893_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
else
{
return v___x_2896_;
}
}
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
lean_dec(v_declName_2876_);
v___x_2905_ = lean_box(0);
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
return v___x_2906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3___boxed(lean_object* v_declName_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v_declName_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(lean_object* v_currNamespace_2916_, lean_object* v_modifiers_2917_, lean_object* v_shortName_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2932_; lean_object* v_shortName_2933_; lean_object* v_currNamespace_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v_view_2994_; lean_object* v_name_2995_; lean_object* v_imported_2996_; lean_object* v_ctx_2997_; lean_object* v_scopes_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3056_; 
lean_inc(v_shortName_2918_);
v_view_2994_ = l_Lean_extractMacroScopes(v_shortName_2918_);
v_name_2995_ = lean_ctor_get(v_view_2994_, 0);
v_imported_2996_ = lean_ctor_get(v_view_2994_, 1);
v_ctx_2997_ = lean_ctor_get(v_view_2994_, 2);
v_scopes_2998_ = lean_ctor_get(v_view_2994_, 3);
v_isSharedCheck_3056_ = !lean_is_exclusive(v_view_2994_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3000_ = v_view_2994_;
v_isShared_3001_ = v_isSharedCheck_3056_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_scopes_2998_);
lean_inc(v_ctx_2997_);
lean_inc(v_imported_2996_);
lean_inc(v_name_2995_);
lean_dec(v_view_2994_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3056_;
goto v_resetjp_2999_;
}
v___jp_2926_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___y_2927_);
lean_ctor_set(v___x_2929_, 1, v___y_2928_);
v___x_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
return v___x_2930_;
}
v___jp_2931_:
{
lean_object* v___x_2941_; 
lean_inc(v___y_2932_);
v___x_2941_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v___y_2932_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v___x_2942_; 
lean_dec_ref(v___x_2941_);
v___x_2942_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2917_, v___y_2932_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
if (lean_obj_tag(v___x_2942_) == 0)
{
uint8_t v_isProtected_2943_; 
v_isProtected_2943_ = lean_ctor_get_uint8(v_modifiers_2917_, sizeof(void*)*3 + 1);
if (v_isProtected_2943_ == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v_currNamespace_2934_);
v_a_2944_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2946_ = v___x_2942_;
v_isShared_2947_ = v_isSharedCheck_2952_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2942_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2952_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v_a_2944_);
lean_ctor_set(v___x_2948_, 1, v_shortName_2933_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_2948_);
v___x_2950_ = v___x_2946_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
else
{
if (lean_obj_tag(v_currNamespace_2934_) == 1)
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2965_; 
v_a_2953_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2955_ = v___x_2942_;
v_isShared_2956_ = v_isSharedCheck_2965_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2942_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2965_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_str_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2963_; 
v_str_2957_ = lean_ctor_get(v_currNamespace_2934_, 1);
lean_inc_ref(v_str_2957_);
lean_dec_ref(v_currNamespace_2934_);
v___x_2958_ = lean_box(0);
v___x_2959_ = l_Lean_Name_str___override(v___x_2958_, v_str_2957_);
v___x_2960_ = l_Lean_Name_append(v___x_2959_, v_shortName_2933_);
v___x_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2961_, 0, v_a_2953_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2961_);
v___x_2963_ = v___x_2955_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2961_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
else
{
lean_object* v_a_2966_; uint8_t v___x_2967_; 
lean_dec(v_currNamespace_2934_);
v_a_2966_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2966_);
lean_dec_ref(v___x_2942_);
v___x_2967_ = l_Lean_Name_isAtomic(v_shortName_2933_);
if (v___x_2967_ == 0)
{
v___y_2927_ = v_a_2966_;
v___y_2928_ = v_shortName_2933_;
goto v___jp_2926_;
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec(v_a_2966_);
lean_dec(v_shortName_2933_);
v___x_2968_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_2969_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2968_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2969_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2969_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec(v_currNamespace_2934_);
lean_dec(v_shortName_2933_);
v_a_2978_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2942_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2942_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_dec(v_currNamespace_2934_);
lean_dec(v_shortName_2933_);
lean_dec(v___y_2932_);
v_a_2986_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2941_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2941_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; uint8_t v_isRootName_3003_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; uint8_t v___x_3045_; 
v___x_3002_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_3003_ = l_Lean_Name_isPrefixOf(v___x_3002_, v_name_2995_);
v___x_3045_ = lean_name_eq(v_name_2995_, v___x_3002_);
if (v___x_3045_ == 0)
{
v___y_3032_ = v___y_2919_;
v___y_3033_ = v___y_2920_;
v___y_3034_ = v___y_2921_;
v___y_3035_ = v___y_2922_;
v___y_3036_ = v___y_2923_;
v___y_3037_ = v___y_2924_;
goto v___jp_3031_;
}
else
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_del_object(v___x_3000_);
lean_dec(v_scopes_2998_);
lean_dec(v_ctx_2997_);
lean_dec(v_imported_2996_);
lean_dec(v_name_2995_);
lean_dec(v_shortName_2918_);
lean_dec(v_currNamespace_2916_);
v___x_3046_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_3047_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3046_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
v___jp_3004_:
{
if (v_isRootName_3003_ == 0)
{
lean_dec(v_name_2995_);
v___y_2932_ = v___y_3011_;
v_shortName_2933_ = v_shortName_2918_;
v_currNamespace_2934_ = v_currNamespace_2916_;
v___y_2935_ = v___y_3006_;
v___y_2936_ = v___y_3009_;
v___y_2937_ = v___y_3008_;
v___y_2938_ = v___y_3007_;
v___y_2939_ = v___y_3010_;
v___y_2940_ = v___y_3005_;
goto v___jp_2931_;
}
else
{
lean_dec(v_shortName_2918_);
lean_dec(v_currNamespace_2916_);
if (lean_obj_tag(v_name_2995_) == 1)
{
lean_object* v_pre_3012_; lean_object* v_str_3013_; lean_object* v___x_3014_; lean_object* v_shortName_3015_; lean_object* v_currNamespace_3016_; 
v_pre_3012_ = lean_ctor_get(v_name_2995_, 0);
lean_inc(v_pre_3012_);
v_str_3013_ = lean_ctor_get(v_name_2995_, 1);
lean_inc_ref(v_str_3013_);
lean_dec_ref(v_name_2995_);
v___x_3014_ = lean_box(0);
v_shortName_3015_ = l_Lean_Name_str___override(v___x_3014_, v_str_3013_);
v_currNamespace_3016_ = l_Lean_Name_replacePrefix(v_pre_3012_, v___x_3002_, v___x_3014_);
v___y_2932_ = v___y_3011_;
v_shortName_2933_ = v_shortName_3015_;
v_currNamespace_2934_ = v_currNamespace_3016_;
v___y_2935_ = v___y_3006_;
v___y_2936_ = v___y_3009_;
v___y_2937_ = v___y_3008_;
v___y_2938_ = v___y_3007_;
v___y_2939_ = v___y_3010_;
v___y_2940_ = v___y_3005_;
goto v___jp_2931_;
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec(v___y_3011_);
v___x_3017_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_3018_ = l_Lean_MessageData_ofName(v_name_2995_);
v___x_3019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3017_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_3021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3019_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
v___x_3022_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3021_, v___y_3006_, v___y_3009_, v___y_3008_, v___y_3007_, v___y_3010_, v___y_3005_);
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3022_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3022_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
v___jp_3031_:
{
if (v_isRootName_3003_ == 0)
{
lean_object* v___x_3038_; 
lean_del_object(v___x_3000_);
lean_dec(v_scopes_2998_);
lean_dec(v_ctx_2997_);
lean_dec(v_imported_2996_);
lean_inc(v_shortName_2918_);
lean_inc(v_currNamespace_2916_);
v___x_3038_ = l_Lean_Name_append(v_currNamespace_2916_, v_shortName_2918_);
v___y_3005_ = v___y_3037_;
v___y_3006_ = v___y_3032_;
v___y_3007_ = v___y_3035_;
v___y_3008_ = v___y_3034_;
v___y_3009_ = v___y_3033_;
v___y_3010_ = v___y_3036_;
v___y_3011_ = v___x_3038_;
goto v___jp_3004_;
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3039_ = lean_box(0);
lean_inc(v_name_2995_);
v___x_3040_ = l_Lean_Name_replacePrefix(v_name_2995_, v___x_3002_, v___x_3039_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3040_);
v___x_3042_ = v___x_3000_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v_imported_2996_);
lean_ctor_set(v_reuseFailAlloc_3044_, 2, v_ctx_2997_);
lean_ctor_set(v_reuseFailAlloc_3044_, 3, v_scopes_2998_);
v___x_3042_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_MacroScopesView_review(v___x_3042_);
v___y_3005_ = v___y_3037_;
v___y_3006_ = v___y_3032_;
v___y_3007_ = v___y_3035_;
v___y_3008_ = v___y_3034_;
v___y_3009_ = v___y_3033_;
v___y_3010_ = v___y_3036_;
v___y_3011_ = v___x_3043_;
goto v___jp_3004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2___boxed(lean_object* v_currNamespace_3057_, lean_object* v_modifiers_3058_, lean_object* v_shortName_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3057_, v_modifiers_3058_, v_shortName_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec_ref(v_modifiers_3058_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(uint8_t v___x_3068_, lean_object* v_as_3069_, size_t v_i_3070_, size_t v_stop_3071_, lean_object* v_b_3072_){
_start:
{
lean_object* v___y_3074_; uint8_t v___x_3078_; 
v___x_3078_ = lean_usize_dec_eq(v_i_3070_, v_stop_3071_);
if (v___x_3078_ == 0)
{
lean_object* v_fst_3079_; uint8_t v___x_3080_; 
v_fst_3079_ = lean_ctor_get(v_b_3072_, 0);
v___x_3080_ = lean_unbox(v_fst_3079_);
if (v___x_3080_ == 0)
{
lean_object* v_snd_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3090_; 
v_snd_3081_ = lean_ctor_get(v_b_3072_, 1);
v_isSharedCheck_3090_ = !lean_is_exclusive(v_b_3072_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v_b_3072_, 0);
lean_dec(v_unused_3091_);
v___x_3083_ = v_b_3072_;
v_isShared_3084_ = v_isSharedCheck_3090_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_snd_3081_);
lean_dec(v_b_3072_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3090_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
uint8_t v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3085_ = 1;
v___x_3086_ = lean_box(v___x_3085_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v___x_3086_);
v___x_3088_ = v___x_3083_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3086_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_snd_3081_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
v___y_3074_ = v___x_3088_;
goto v___jp_3073_;
}
}
}
else
{
lean_object* v_snd_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3102_; 
v_snd_3092_ = lean_ctor_get(v_b_3072_, 1);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_b_3072_);
if (v_isSharedCheck_3102_ == 0)
{
lean_object* v_unused_3103_; 
v_unused_3103_ = lean_ctor_get(v_b_3072_, 0);
lean_dec(v_unused_3103_);
v___x_3094_ = v_b_3072_;
v_isShared_3095_ = v_isSharedCheck_3102_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_snd_3092_);
lean_dec(v_b_3072_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3102_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3096_ = lean_array_uget_borrowed(v_as_3069_, v_i_3070_);
lean_inc(v___x_3096_);
v___x_3097_ = lean_array_push(v_snd_3092_, v___x_3096_);
v___x_3098_ = lean_box(v___x_3068_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 1, v___x_3097_);
lean_ctor_set(v___x_3094_, 0, v___x_3098_);
v___x_3100_ = v___x_3094_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3098_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3097_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
v___y_3074_ = v___x_3100_;
goto v___jp_3073_;
}
}
}
}
else
{
return v_b_3072_;
}
v___jp_3073_:
{
size_t v___x_3075_; size_t v___x_3076_; 
v___x_3075_ = ((size_t)1ULL);
v___x_3076_ = lean_usize_add(v_i_3070_, v___x_3075_);
v_i_3070_ = v___x_3076_;
v_b_3072_ = v___y_3074_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4___boxed(lean_object* v___x_3104_, lean_object* v_as_3105_, lean_object* v_i_3106_, lean_object* v_stop_3107_, lean_object* v_b_3108_){
_start:
{
uint8_t v___x_19313__boxed_3109_; size_t v_i_boxed_3110_; size_t v_stop_boxed_3111_; lean_object* v_res_3112_; 
v___x_19313__boxed_3109_ = lean_unbox(v___x_3104_);
v_i_boxed_3110_ = lean_unbox_usize(v_i_3106_);
lean_dec(v_i_3106_);
v_stop_boxed_3111_ = lean_unbox_usize(v_stop_3107_);
lean_dec(v_stop_3107_);
v_res_3112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_19313__boxed_3109_, v_as_3105_, v_i_boxed_3110_, v_stop_boxed_3111_, v_b_3108_);
lean_dec_ref(v_as_3105_);
return v_res_3112_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(lean_object* v_a_3113_, lean_object* v_x_3114_){
_start:
{
if (lean_obj_tag(v_x_3114_) == 0)
{
uint8_t v___x_3115_; 
v___x_3115_ = 0;
return v___x_3115_;
}
else
{
lean_object* v_head_3116_; lean_object* v_tail_3117_; uint8_t v___x_3118_; 
v_head_3116_ = lean_ctor_get(v_x_3114_, 0);
v_tail_3117_ = lean_ctor_get(v_x_3114_, 1);
v___x_3118_ = lean_name_eq(v_a_3113_, v_head_3116_);
if (v___x_3118_ == 0)
{
v_x_3114_ = v_tail_3117_;
goto _start;
}
else
{
return v___x_3118_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_expandDeclId_spec__0___boxed(lean_object* v_a_3120_, lean_object* v_x_3121_){
_start:
{
uint8_t v_res_3122_; lean_object* v_r_3123_; 
v_res_3122_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_a_3120_, v_x_3121_);
lean_dec(v_x_3121_);
lean_dec(v_a_3120_);
v_r_3123_ = lean_box(v_res_3122_);
return v_r_3123_;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = ((lean_object*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0));
v___x_3126_ = l_Lean_stringToMessageData(v___x_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(lean_object* v_u_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3135_ = lean_obj_once(&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1, &l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1);
v___x_3136_ = l_Lean_MessageData_ofName(v_u_3127_);
v___x_3137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3135_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v___x_3138_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_3139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3137_);
lean_ctor_set(v___x_3139_, 1, v___x_3138_);
v___x_3140_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3139_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___boxed(lean_object* v_u_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(lean_object* v_as_3150_, size_t v_i_3151_, size_t v_stop_3152_, lean_object* v_b_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_a_3162_; uint8_t v___x_3166_; 
v___x_3166_ = lean_usize_dec_eq(v_i_3151_, v_stop_3152_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3167_; lean_object* v_id_3168_; uint8_t v___x_3169_; 
v___x_3167_ = lean_array_uget_borrowed(v_as_3150_, v_i_3151_);
v_id_3168_ = l_Lean_Syntax_getId(v___x_3167_);
v___x_3169_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_id_3168_, v_b_3153_);
if (v___x_3169_ == 0)
{
lean_object* v___x_3170_; 
v___x_3170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3170_, 0, v_id_3168_);
lean_ctor_set(v___x_3170_, 1, v_b_3153_);
v_a_3162_ = v___x_3170_;
goto v___jp_3161_;
}
else
{
lean_object* v_fileName_3171_; lean_object* v_fileMap_3172_; lean_object* v_options_3173_; lean_object* v_currRecDepth_3174_; lean_object* v_maxRecDepth_3175_; lean_object* v_ref_3176_; lean_object* v_currNamespace_3177_; lean_object* v_openDecls_3178_; lean_object* v_initHeartbeats_3179_; lean_object* v_maxHeartbeats_3180_; lean_object* v_quotContext_3181_; lean_object* v_currMacroScope_3182_; uint8_t v_diag_3183_; lean_object* v_cancelTk_x3f_3184_; uint8_t v_suppressElabErrors_3185_; lean_object* v_inheritedTraceOptions_3186_; lean_object* v_ref_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
lean_dec(v_b_3153_);
v_fileName_3171_ = lean_ctor_get(v___y_3158_, 0);
v_fileMap_3172_ = lean_ctor_get(v___y_3158_, 1);
v_options_3173_ = lean_ctor_get(v___y_3158_, 2);
v_currRecDepth_3174_ = lean_ctor_get(v___y_3158_, 3);
v_maxRecDepth_3175_ = lean_ctor_get(v___y_3158_, 4);
v_ref_3176_ = lean_ctor_get(v___y_3158_, 5);
v_currNamespace_3177_ = lean_ctor_get(v___y_3158_, 6);
v_openDecls_3178_ = lean_ctor_get(v___y_3158_, 7);
v_initHeartbeats_3179_ = lean_ctor_get(v___y_3158_, 8);
v_maxHeartbeats_3180_ = lean_ctor_get(v___y_3158_, 9);
v_quotContext_3181_ = lean_ctor_get(v___y_3158_, 10);
v_currMacroScope_3182_ = lean_ctor_get(v___y_3158_, 11);
v_diag_3183_ = lean_ctor_get_uint8(v___y_3158_, sizeof(void*)*14);
v_cancelTk_x3f_3184_ = lean_ctor_get(v___y_3158_, 12);
v_suppressElabErrors_3185_ = lean_ctor_get_uint8(v___y_3158_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3186_ = lean_ctor_get(v___y_3158_, 13);
v_ref_3187_ = l_Lean_replaceRef(v___x_3167_, v_ref_3176_);
lean_inc_ref(v_inheritedTraceOptions_3186_);
lean_inc(v_cancelTk_x3f_3184_);
lean_inc(v_currMacroScope_3182_);
lean_inc(v_quotContext_3181_);
lean_inc(v_maxHeartbeats_3180_);
lean_inc(v_initHeartbeats_3179_);
lean_inc(v_openDecls_3178_);
lean_inc(v_currNamespace_3177_);
lean_inc(v_maxRecDepth_3175_);
lean_inc(v_currRecDepth_3174_);
lean_inc_ref(v_options_3173_);
lean_inc_ref(v_fileMap_3172_);
lean_inc_ref(v_fileName_3171_);
v___x_3188_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3188_, 0, v_fileName_3171_);
lean_ctor_set(v___x_3188_, 1, v_fileMap_3172_);
lean_ctor_set(v___x_3188_, 2, v_options_3173_);
lean_ctor_set(v___x_3188_, 3, v_currRecDepth_3174_);
lean_ctor_set(v___x_3188_, 4, v_maxRecDepth_3175_);
lean_ctor_set(v___x_3188_, 5, v_ref_3187_);
lean_ctor_set(v___x_3188_, 6, v_currNamespace_3177_);
lean_ctor_set(v___x_3188_, 7, v_openDecls_3178_);
lean_ctor_set(v___x_3188_, 8, v_initHeartbeats_3179_);
lean_ctor_set(v___x_3188_, 9, v_maxHeartbeats_3180_);
lean_ctor_set(v___x_3188_, 10, v_quotContext_3181_);
lean_ctor_set(v___x_3188_, 11, v_currMacroScope_3182_);
lean_ctor_set(v___x_3188_, 12, v_cancelTk_x3f_3184_);
lean_ctor_set(v___x_3188_, 13, v_inheritedTraceOptions_3186_);
lean_ctor_set_uint8(v___x_3188_, sizeof(void*)*14, v_diag_3183_);
lean_ctor_set_uint8(v___x_3188_, sizeof(void*)*14 + 1, v_suppressElabErrors_3185_);
v___x_3189_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_id_3168_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___x_3188_, v___y_3159_);
lean_dec_ref(v___x_3188_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc(v_a_3190_);
lean_dec_ref(v___x_3189_);
v_a_3162_ = v_a_3190_;
goto v___jp_3161_;
}
else
{
return v___x_3189_;
}
}
}
else
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v_b_3153_);
return v___x_3191_;
}
v___jp_3161_:
{
size_t v___x_3163_; size_t v___x_3164_; 
v___x_3163_ = ((size_t)1ULL);
v___x_3164_ = lean_usize_add(v_i_3151_, v___x_3163_);
v_i_3151_ = v___x_3164_;
v_b_3153_ = v_a_3162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3___boxed(lean_object* v_as_3192_, lean_object* v_i_3193_, lean_object* v_stop_3194_, lean_object* v_b_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
size_t v_i_boxed_3203_; size_t v_stop_boxed_3204_; lean_object* v_res_3205_; 
v_i_boxed_3203_ = lean_unbox_usize(v_i_3193_);
lean_dec(v_i_3193_);
v_stop_boxed_3204_ = lean_unbox_usize(v_stop_3194_);
lean_dec(v_stop_3194_);
v_res_3205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v_as_3192_, v_i_boxed_3203_, v_stop_boxed_3204_, v_b_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec_ref(v_as_3192_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId(lean_object* v_currNamespace_3206_, lean_object* v_currLevelNames_3207_, lean_object* v_declId_3208_, lean_object* v_modifiers_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_){
_start:
{
lean_object* v___x_3217_; lean_object* v_fst_3218_; lean_object* v_snd_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3314_; 
v___x_3217_ = l_Lean_Elab_expandDeclIdCore(v_declId_3208_);
v_fst_3218_ = lean_ctor_get(v___x_3217_, 0);
v_snd_3219_ = lean_ctor_get(v___x_3217_, 1);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3221_ = v___x_3217_;
v_isShared_3222_ = v_isSharedCheck_3314_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_snd_3219_);
lean_inc(v_fst_3218_);
lean_dec(v___x_3217_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3314_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v_levelNames_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3271_; lean_object* v___y_3282_; uint8_t v___x_3293_; 
v___x_3293_ = l_Lean_Syntax_isNone(v_snd_3219_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3294_ = lean_unsigned_to_nat(1u);
v___x_3295_ = l_Lean_Syntax_getArg(v_snd_3219_, v___x_3294_);
lean_dec(v_snd_3219_);
v___x_3296_ = l_Lean_Syntax_getArgs(v___x_3295_);
lean_dec(v___x_3295_);
v___x_3297_ = lean_unsigned_to_nat(0u);
v___x_3298_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__0));
v___x_3299_ = lean_array_get_size(v___x_3296_);
v___x_3300_ = lean_nat_dec_lt(v___x_3297_, v___x_3299_);
if (v___x_3300_ == 0)
{
lean_dec_ref(v___x_3296_);
lean_del_object(v___x_3221_);
v___y_3282_ = v___x_3298_;
goto v___jp_3281_;
}
else
{
lean_object* v___x_3301_; lean_object* v___x_3303_; 
v___x_3301_ = lean_box(v___x_3300_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 1, v___x_3298_);
lean_ctor_set(v___x_3221_, 0, v___x_3301_);
v___x_3303_ = v___x_3221_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3301_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v___x_3298_);
v___x_3303_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
uint8_t v___x_3304_; 
v___x_3304_ = lean_nat_dec_le(v___x_3299_, v___x_3299_);
if (v___x_3304_ == 0)
{
if (v___x_3300_ == 0)
{
lean_dec_ref(v___x_3303_);
lean_dec_ref(v___x_3296_);
v___y_3282_ = v___x_3298_;
goto v___jp_3281_;
}
else
{
size_t v___x_3305_; size_t v___x_3306_; lean_object* v___x_3307_; lean_object* v_snd_3308_; 
v___x_3305_ = ((size_t)0ULL);
v___x_3306_ = lean_usize_of_nat(v___x_3299_);
v___x_3307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3293_, v___x_3296_, v___x_3305_, v___x_3306_, v___x_3303_);
lean_dec_ref(v___x_3296_);
v_snd_3308_ = lean_ctor_get(v___x_3307_, 1);
lean_inc(v_snd_3308_);
lean_dec_ref(v___x_3307_);
v___y_3282_ = v_snd_3308_;
goto v___jp_3281_;
}
}
else
{
size_t v___x_3309_; size_t v___x_3310_; lean_object* v___x_3311_; lean_object* v_snd_3312_; 
v___x_3309_ = ((size_t)0ULL);
v___x_3310_ = lean_usize_of_nat(v___x_3299_);
v___x_3311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3293_, v___x_3296_, v___x_3309_, v___x_3310_, v___x_3303_);
lean_dec_ref(v___x_3296_);
v_snd_3312_ = lean_ctor_get(v___x_3311_, 1);
lean_inc(v_snd_3312_);
lean_dec_ref(v___x_3311_);
v___y_3282_ = v_snd_3312_;
goto v___jp_3281_;
}
}
}
}
else
{
lean_del_object(v___x_3221_);
lean_dec(v_snd_3219_);
v_levelNames_3224_ = v_currLevelNames_3207_;
v___y_3225_ = v_a_3210_;
v___y_3226_ = v_a_3211_;
v___y_3227_ = v_a_3212_;
v___y_3228_ = v_a_3213_;
v___y_3229_ = v_a_3214_;
v___y_3230_ = v_a_3215_;
goto v___jp_3223_;
}
v___jp_3223_:
{
lean_object* v_fileName_3231_; lean_object* v_fileMap_3232_; lean_object* v_options_3233_; lean_object* v_currRecDepth_3234_; lean_object* v_maxRecDepth_3235_; lean_object* v_ref_3236_; lean_object* v_currNamespace_3237_; lean_object* v_openDecls_3238_; lean_object* v_initHeartbeats_3239_; lean_object* v_maxHeartbeats_3240_; lean_object* v_quotContext_3241_; lean_object* v_currMacroScope_3242_; uint8_t v_diag_3243_; lean_object* v_cancelTk_x3f_3244_; uint8_t v_suppressElabErrors_3245_; lean_object* v_inheritedTraceOptions_3246_; lean_object* v_ref_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v_fileName_3231_ = lean_ctor_get(v___y_3229_, 0);
v_fileMap_3232_ = lean_ctor_get(v___y_3229_, 1);
v_options_3233_ = lean_ctor_get(v___y_3229_, 2);
v_currRecDepth_3234_ = lean_ctor_get(v___y_3229_, 3);
v_maxRecDepth_3235_ = lean_ctor_get(v___y_3229_, 4);
v_ref_3236_ = lean_ctor_get(v___y_3229_, 5);
v_currNamespace_3237_ = lean_ctor_get(v___y_3229_, 6);
v_openDecls_3238_ = lean_ctor_get(v___y_3229_, 7);
v_initHeartbeats_3239_ = lean_ctor_get(v___y_3229_, 8);
v_maxHeartbeats_3240_ = lean_ctor_get(v___y_3229_, 9);
v_quotContext_3241_ = lean_ctor_get(v___y_3229_, 10);
v_currMacroScope_3242_ = lean_ctor_get(v___y_3229_, 11);
v_diag_3243_ = lean_ctor_get_uint8(v___y_3229_, sizeof(void*)*14);
v_cancelTk_x3f_3244_ = lean_ctor_get(v___y_3229_, 12);
v_suppressElabErrors_3245_ = lean_ctor_get_uint8(v___y_3229_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3246_ = lean_ctor_get(v___y_3229_, 13);
v_ref_3247_ = l_Lean_replaceRef(v_declId_3208_, v_ref_3236_);
lean_inc_ref(v_inheritedTraceOptions_3246_);
lean_inc(v_cancelTk_x3f_3244_);
lean_inc(v_currMacroScope_3242_);
lean_inc(v_quotContext_3241_);
lean_inc(v_maxHeartbeats_3240_);
lean_inc(v_initHeartbeats_3239_);
lean_inc(v_openDecls_3238_);
lean_inc(v_currNamespace_3237_);
lean_inc(v_maxRecDepth_3235_);
lean_inc(v_currRecDepth_3234_);
lean_inc_ref(v_options_3233_);
lean_inc_ref(v_fileMap_3232_);
lean_inc_ref(v_fileName_3231_);
v___x_3248_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3248_, 0, v_fileName_3231_);
lean_ctor_set(v___x_3248_, 1, v_fileMap_3232_);
lean_ctor_set(v___x_3248_, 2, v_options_3233_);
lean_ctor_set(v___x_3248_, 3, v_currRecDepth_3234_);
lean_ctor_set(v___x_3248_, 4, v_maxRecDepth_3235_);
lean_ctor_set(v___x_3248_, 5, v_ref_3247_);
lean_ctor_set(v___x_3248_, 6, v_currNamespace_3237_);
lean_ctor_set(v___x_3248_, 7, v_openDecls_3238_);
lean_ctor_set(v___x_3248_, 8, v_initHeartbeats_3239_);
lean_ctor_set(v___x_3248_, 9, v_maxHeartbeats_3240_);
lean_ctor_set(v___x_3248_, 10, v_quotContext_3241_);
lean_ctor_set(v___x_3248_, 11, v_currMacroScope_3242_);
lean_ctor_set(v___x_3248_, 12, v_cancelTk_x3f_3244_);
lean_ctor_set(v___x_3248_, 13, v_inheritedTraceOptions_3246_);
lean_ctor_set_uint8(v___x_3248_, sizeof(void*)*14, v_diag_3243_);
lean_ctor_set_uint8(v___x_3248_, sizeof(void*)*14 + 1, v_suppressElabErrors_3245_);
v___x_3249_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3206_, v_modifiers_3209_, v_fst_3218_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___x_3248_, v___y_3230_);
lean_dec_ref(v___x_3248_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3261_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3252_ = v___x_3249_;
v_isShared_3253_ = v_isSharedCheck_3261_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3249_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3261_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v_fst_3254_; lean_object* v_snd_3255_; lean_object* v_docString_x3f_3256_; lean_object* v___x_3257_; lean_object* v___x_3259_; 
v_fst_3254_ = lean_ctor_get(v_a_3250_, 0);
lean_inc(v_fst_3254_);
v_snd_3255_ = lean_ctor_get(v_a_3250_, 1);
lean_inc(v_snd_3255_);
lean_dec(v_a_3250_);
v_docString_x3f_3256_ = lean_ctor_get(v_modifiers_3209_, 1);
lean_inc(v_docString_x3f_3256_);
v___x_3257_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3257_, 0, v_snd_3255_);
lean_ctor_set(v___x_3257_, 1, v_fst_3254_);
lean_ctor_set(v___x_3257_, 2, v_levelNames_3224_);
lean_ctor_set(v___x_3257_, 3, v_docString_x3f_3256_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3257_);
v___x_3259_ = v___x_3252_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3257_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec(v_levelNames_3224_);
v_a_3262_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3249_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3249_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
v___jp_3270_:
{
if (lean_obj_tag(v___y_3271_) == 0)
{
lean_object* v_a_3272_; 
v_a_3272_ = lean_ctor_get(v___y_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref(v___y_3271_);
v_levelNames_3224_ = v_a_3272_;
v___y_3225_ = v_a_3210_;
v___y_3226_ = v_a_3211_;
v___y_3227_ = v_a_3212_;
v___y_3228_ = v_a_3213_;
v___y_3229_ = v_a_3214_;
v___y_3230_ = v_a_3215_;
goto v___jp_3223_;
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_dec(v_fst_3218_);
lean_dec(v_currNamespace_3206_);
v_a_3273_ = lean_ctor_get(v___y_3271_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___y_3271_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___y_3271_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___y_3271_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
v___jp_3281_:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v___x_3283_ = lean_unsigned_to_nat(0u);
v___x_3284_ = lean_array_get_size(v___y_3282_);
v___x_3285_ = lean_nat_dec_lt(v___x_3283_, v___x_3284_);
if (v___x_3285_ == 0)
{
lean_dec_ref(v___y_3282_);
v_levelNames_3224_ = v_currLevelNames_3207_;
v___y_3225_ = v_a_3210_;
v___y_3226_ = v_a_3211_;
v___y_3227_ = v_a_3212_;
v___y_3228_ = v_a_3213_;
v___y_3229_ = v_a_3214_;
v___y_3230_ = v_a_3215_;
goto v___jp_3223_;
}
else
{
uint8_t v___x_3286_; 
v___x_3286_ = lean_nat_dec_le(v___x_3284_, v___x_3284_);
if (v___x_3286_ == 0)
{
if (v___x_3285_ == 0)
{
lean_dec_ref(v___y_3282_);
v_levelNames_3224_ = v_currLevelNames_3207_;
v___y_3225_ = v_a_3210_;
v___y_3226_ = v_a_3211_;
v___y_3227_ = v_a_3212_;
v___y_3228_ = v_a_3213_;
v___y_3229_ = v_a_3214_;
v___y_3230_ = v_a_3215_;
goto v___jp_3223_;
}
else
{
size_t v___x_3287_; size_t v___x_3288_; lean_object* v___x_3289_; 
v___x_3287_ = ((size_t)0ULL);
v___x_3288_ = lean_usize_of_nat(v___x_3284_);
v___x_3289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3282_, v___x_3287_, v___x_3288_, v_currLevelNames_3207_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
lean_dec_ref(v___y_3282_);
v___y_3271_ = v___x_3289_;
goto v___jp_3270_;
}
}
else
{
size_t v___x_3290_; size_t v___x_3291_; lean_object* v___x_3292_; 
v___x_3290_ = ((size_t)0ULL);
v___x_3291_ = lean_usize_of_nat(v___x_3284_);
v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3282_, v___x_3290_, v___x_3291_, v_currLevelNames_3207_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
lean_dec_ref(v___y_3282_);
v___y_3271_ = v___x_3292_;
goto v___jp_3270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___boxed(lean_object* v_currNamespace_3315_, lean_object* v_currLevelNames_3316_, lean_object* v_declId_3317_, lean_object* v_modifiers_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Lean_Elab_expandDeclId(v_currNamespace_3315_, v_currLevelNames_3316_, v_declId_3317_, v_modifiers_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_);
lean_dec(v_a_3324_);
lean_dec_ref(v_a_3323_);
lean_dec(v_a_3322_);
lean_dec_ref(v_a_3321_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec_ref(v_modifiers_3318_);
lean_dec(v_declId_3317_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(lean_object* v_00_u03b1_3327_, lean_object* v_u_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___boxed(lean_object* v_00_u03b1_3337_, lean_object* v_u_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(v_00_u03b1_3337_, v_u_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(lean_object* v_00_u03b1_3347_, lean_object* v_msg_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3357_, lean_object* v_msg_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(v_00_u03b1_3357_, v_msg_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(lean_object* v_msgData_3367_, lean_object* v_macroStack_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v___x_3376_; 
v___x_3376_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_3367_, v_macroStack_3368_, v___y_3373_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_3377_, lean_object* v_macroStack_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(v_msgData_3377_, v_macroStack_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(lean_object* v_t_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_3387_, v___y_3393_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___boxed(lean_object* v_t_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(v_t_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(lean_object* v_env_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_3405_, v___y_3409_, v___y_3411_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___boxed(lean_object* v_env_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(v_env_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(lean_object* v_00_u03b1_3423_, lean_object* v_env_3424_, lean_object* v_x_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_3424_, v_x_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3434_, lean_object* v_env_3435_, lean_object* v_x_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(v_00_u03b1_3434_, v_env_3435_, v_x_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(lean_object* v_00_u03b1_3445_, lean_object* v_constName_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___boxed(lean_object* v_00_u03b1_3455_, lean_object* v_constName_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(v_00_u03b1_3455_, v_constName_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(lean_object* v_00_u03b1_3465_, lean_object* v_ref_3466_, lean_object* v_constName_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_3466_, v_constName_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___boxed(lean_object* v_00_u03b1_3476_, lean_object* v_ref_3477_, lean_object* v_constName_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(v_00_u03b1_3476_, v_ref_3477_, v_constName_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v_ref_3477_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(lean_object* v_00_u03b1_3487_, lean_object* v_ref_3488_, lean_object* v_msg_3489_, lean_object* v_declHint_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_3488_, v_msg_3489_, v_declHint_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___boxed(lean_object* v_00_u03b1_3499_, lean_object* v_ref_3500_, lean_object* v_msg_3501_, lean_object* v_declHint_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(v_00_u03b1_3499_, v_ref_3500_, v_msg_3501_, v_declHint_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v_ref_3500_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(lean_object* v_msg_3511_, lean_object* v_declHint_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_3511_, v_declHint_3512_, v___y_3518_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___boxed(lean_object* v_msg_3521_, lean_object* v_declHint_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(v_msg_3521_, v_declHint_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(lean_object* v_00_u03b1_3531_, lean_object* v_ref_3532_, lean_object* v_msg_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_3532_, v_msg_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___boxed(lean_object* v_00_u03b1_3542_, lean_object* v_ref_3543_, lean_object* v_msg_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(v_00_u03b1_3542_, v_ref_3543_, v_msg_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v_ref_3543_);
return v_res_3552_;
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
