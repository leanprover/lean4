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
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Elab_elabDeclAttrs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_doc_verso;
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_nat_to_int(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabModifiers___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_elabModifiers___redArg___lam__7___closed__0 = (const lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__0_value;
static const lean_string_object l_Lean_Elab_elabModifiers___redArg___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_elabModifiers___redArg___lam__7___closed__1 = (const lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__1_value;
static const lean_string_object l_Lean_Elab_elabModifiers___redArg___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_elabModifiers___redArg___lam__7___closed__2 = (const lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__2_value;
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___lam__7___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___lam__7___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___lam__7___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___lam__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_instToStringVisibility___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(213, 248, 16, 228, 25, 227, 72, 143)}};
static const lean_object* l_Lean_Elab_elabModifiers___redArg___lam__7___closed__3 = (const lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__3_value;
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___lam__7___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___lam__7___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___lam__7___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___lam__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_instToStringVisibility___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 134, 241, 204, 211, 206, 124, 144)}};
static const lean_object* l_Lean_Elab_elabModifiers___redArg___lam__7___closed__4 = (const lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__4_value;
static const lean_string_object l_Lean_Elab_elabModifiers___redArg___lam__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unexpected visibility modifier"};
static const lean_object* l_Lean_Elab_elabModifiers___redArg___lam__7___closed__5 = (const lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__5_value;
static lean_once_cell_t l_Lean_Elab_elabModifiers___redArg___lam__7___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabModifiers___redArg___lam__7___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__7(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__7___boxed(lean_object**);
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_instToFormatModifiers___lam__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l_Lean_Elab_elabModifiers___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
uint8_t v___x_877__boxed_34_; lean_object* v_res_35_; 
v___x_877__boxed_34_ = lean_unbox(v___x_30_);
v_res_35_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(v_____do__lift_29_, v___x_877__boxed_34_, v_inst_31_, v_inst_32_, v_____do__lift_33_);
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
uint8_t v___x_921__boxed_56_; lean_object* v_res_57_; 
v___x_921__boxed_56_ = lean_unbox(v___x_48_);
v_res_57_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(v___x_921__boxed_56_, v_inst_49_, v_inst_50_, v_inst_51_, v_inst_52_, v_declName_53_, v_toBind_54_, v_____do__lift_55_);
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
uint8_t v___x_947__boxed_78_; lean_object* v_res_79_; 
v___x_947__boxed_78_ = lean_unbox(v___x_71_);
v_res_79_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(v_toMonadRef_70_, v___x_947__boxed_78_, v_inst_72_, v_inst_73_, v_inst_74_, v_inst_75_, v_toBind_76_, v_declName_77_);
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
uint8_t v___x_981__boxed_102_; lean_object* v_res_103_; 
v___x_981__boxed_102_ = lean_unbox(v___x_98_);
v_res_103_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(v_val_97_, v___x_981__boxed_102_, v_inst_99_, v_inst_100_, v_____r_101_);
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
lean_inc(v_val_115_);
lean_dec_ref(v___x_112_);
v___x_116_ = 1;
lean_inc(v_val_115_);
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
uint8_t v___x_1058__boxed_151_; lean_object* v_res_152_; 
v___x_1058__boxed_151_ = lean_unbox(v___x_145_);
v_res_152_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(v_declName_144_, v___x_1058__boxed_151_, v_inst_146_, v_inst_147_, v_toBind_148_, v___f_149_, v_____r_150_);
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
uint8_t v___x_1131__boxed_210_; lean_object* v_res_211_; 
v___x_1131__boxed_210_ = lean_unbox(v___x_203_);
v_res_211_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(v___f_201_, v_declName_202_, v___x_1131__boxed_210_, v_inst_204_, v_inst_205_, v_toBind_206_, v___f_207_, v_env_208_, v_____do__lift_209_);
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
uint8_t v___x_1205__boxed_252_; lean_object* v_res_253_; 
v___x_1205__boxed_252_ = lean_unbox(v___x_245_);
v_res_253_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(v_declName_244_, v___x_1205__boxed_252_, v_inst_246_, v_inst_247_, v_toBind_248_, v___f_249_, v___f_250_, v_____r_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10(lean_object* v_toMonadRef_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_toBind_259_, lean_object* v_declName_260_, lean_object* v_toPure_261_, lean_object* v_getEnv_262_, lean_object* v_inst_263_, lean_object* v_env_264_){
_start:
{
uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v_addInfo_267_; lean_object* v_env_268_; lean_object* v___f_269_; lean_object* v___f_270_; lean_object* v___f_271_; lean_object* v___f_272_; lean_object* v___x_273_; lean_object* v___f_274_; uint8_t v___x_275_; uint8_t v___x_276_; 
v___x_265_ = 0;
v___x_266_ = lean_box(v___x_265_);
lean_inc(v_toBind_259_);
lean_inc_ref(v_inst_258_);
lean_inc_ref(v_inst_257_);
lean_inc_ref(v_inst_256_);
lean_inc_ref(v_inst_255_);
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
lean_inc(v_toBind_259_);
lean_inc_ref(v_addInfo_267_);
lean_inc_ref(v_inst_258_);
lean_inc_ref(v_inst_255_);
lean_inc_ref(v_env_268_);
lean_inc(v_declName_260_);
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
lean_inc(v_toBind_259_);
lean_inc_ref(v_inst_258_);
lean_inc_ref(v_inst_255_);
lean_inc(v_declName_260_);
lean_inc_ref(v_env_268_);
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
lean_inc_ref(v_env_268_);
lean_inc(v_toBind_259_);
lean_inc_ref(v_inst_258_);
lean_inc_ref(v_inst_255_);
lean_inc(v_declName_260_);
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
lean_inc(v_declName_260_);
lean_inc_ref(v_env_268_);
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
lean_inc(v_toBind_259_);
v___f_279_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8), 4, 3);
lean_closure_set(v___f_279_, 0, v_toBind_259_);
lean_closure_set(v___f_279_, 1, v_getEnv_262_);
lean_closure_set(v___f_279_, 2, v___f_274_);
v___x_280_ = lean_box(v___x_275_);
lean_inc_ref(v___f_279_);
lean_inc(v_toBind_259_);
lean_inc_ref(v_inst_258_);
lean_inc_ref(v_inst_255_);
lean_inc(v_declName_260_);
v___f_281_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_281_, 0, v_declName_260_);
lean_closure_set(v___f_281_, 1, v___x_280_);
lean_closure_set(v___f_281_, 2, v_inst_255_);
lean_closure_set(v___f_281_, 3, v_inst_258_);
lean_closure_set(v___f_281_, 4, v_toBind_259_);
lean_closure_set(v___f_281_, 5, v___f_279_);
lean_closure_set(v___f_281_, 6, v___f_279_);
lean_inc(v_toBind_259_);
lean_inc_ref(v_inst_257_);
lean_inc_ref(v_inst_255_);
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
lean_inc(v_toBind_292_);
v_getEnv_293_ = lean_ctor_get(v_inst_286_, 0);
lean_inc(v_getEnv_293_);
v_toMonadRef_294_ = lean_ctor_get(v_inst_287_, 1);
lean_inc_ref(v_toMonadRef_294_);
v_toPure_295_ = lean_ctor_get(v_toApplicative_291_, 1);
lean_inc(v_toPure_295_);
lean_inc(v_getEnv_293_);
lean_inc(v_toBind_292_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx(uint8_t v_x_416_){
_start:
{
switch(v_x_416_)
{
case 0:
{
lean_object* v___x_417_; 
v___x_417_ = lean_unsigned_to_nat(0u);
return v___x_417_;
}
case 1:
{
lean_object* v___x_418_; 
v___x_418_ = lean_unsigned_to_nat(1u);
return v___x_418_;
}
default: 
{
lean_object* v___x_419_; 
v___x_419_ = lean_unsigned_to_nat(2u);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorIdx___boxed(lean_object* v_x_420_){
_start:
{
uint8_t v_x_boxed_421_; lean_object* v_res_422_; 
v_x_boxed_421_ = lean_unbox(v_x_420_);
v_res_422_ = l_Lean_Elab_RecKind_ctorIdx(v_x_boxed_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx(uint8_t v_x_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Elab_RecKind_ctorIdx(v_x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_toCtorIdx___boxed(lean_object* v_x_425_){
_start:
{
uint8_t v_x_4__boxed_426_; lean_object* v_res_427_; 
v_x_4__boxed_426_ = lean_unbox(v_x_425_);
v_res_427_ = l_Lean_Elab_RecKind_toCtorIdx(v_x_4__boxed_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg(lean_object* v_k_428_){
_start:
{
lean_inc(v_k_428_);
return v_k_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___redArg___boxed(lean_object* v_k_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Elab_RecKind_ctorElim___redArg(v_k_429_);
lean_dec(v_k_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim(lean_object* v_motive_431_, lean_object* v_ctorIdx_432_, uint8_t v_t_433_, lean_object* v_h_434_, lean_object* v_k_435_){
_start:
{
lean_inc(v_k_435_);
return v_k_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_ctorElim___boxed(lean_object* v_motive_436_, lean_object* v_ctorIdx_437_, lean_object* v_t_438_, lean_object* v_h_439_, lean_object* v_k_440_){
_start:
{
uint8_t v_t_boxed_441_; lean_object* v_res_442_; 
v_t_boxed_441_ = lean_unbox(v_t_438_);
v_res_442_ = l_Lean_Elab_RecKind_ctorElim(v_motive_436_, v_ctorIdx_437_, v_t_boxed_441_, v_h_439_, v_k_440_);
lean_dec(v_k_440_);
lean_dec(v_ctorIdx_437_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg(lean_object* v_partial_443_){
_start:
{
lean_inc(v_partial_443_);
return v_partial_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___redArg___boxed(lean_object* v_partial_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Elab_RecKind_partial_elim___redArg(v_partial_444_);
lean_dec(v_partial_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim(lean_object* v_motive_446_, uint8_t v_t_447_, lean_object* v_h_448_, lean_object* v_partial_449_){
_start:
{
lean_inc(v_partial_449_);
return v_partial_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_partial_elim___boxed(lean_object* v_motive_450_, lean_object* v_t_451_, lean_object* v_h_452_, lean_object* v_partial_453_){
_start:
{
uint8_t v_t_boxed_454_; lean_object* v_res_455_; 
v_t_boxed_454_ = lean_unbox(v_t_451_);
v_res_455_ = l_Lean_Elab_RecKind_partial_elim(v_motive_450_, v_t_boxed_454_, v_h_452_, v_partial_453_);
lean_dec(v_partial_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg(lean_object* v_nonrec_456_){
_start:
{
lean_inc(v_nonrec_456_);
return v_nonrec_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___redArg___boxed(lean_object* v_nonrec_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Elab_RecKind_nonrec_elim___redArg(v_nonrec_457_);
lean_dec(v_nonrec_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim(lean_object* v_motive_459_, uint8_t v_t_460_, lean_object* v_h_461_, lean_object* v_nonrec_462_){
_start:
{
lean_inc(v_nonrec_462_);
return v_nonrec_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_nonrec_elim___boxed(lean_object* v_motive_463_, lean_object* v_t_464_, lean_object* v_h_465_, lean_object* v_nonrec_466_){
_start:
{
uint8_t v_t_boxed_467_; lean_object* v_res_468_; 
v_t_boxed_467_ = lean_unbox(v_t_464_);
v_res_468_ = l_Lean_Elab_RecKind_nonrec_elim(v_motive_463_, v_t_boxed_467_, v_h_465_, v_nonrec_466_);
lean_dec(v_nonrec_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg(lean_object* v_default_469_){
_start:
{
lean_inc(v_default_469_);
return v_default_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___redArg___boxed(lean_object* v_default_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Elab_RecKind_default_elim___redArg(v_default_470_);
lean_dec(v_default_470_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim(lean_object* v_motive_472_, uint8_t v_t_473_, lean_object* v_h_474_, lean_object* v_default_475_){
_start:
{
lean_inc(v_default_475_);
return v_default_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_RecKind_default_elim___boxed(lean_object* v_motive_476_, lean_object* v_t_477_, lean_object* v_h_478_, lean_object* v_default_479_){
_start:
{
uint8_t v_t_boxed_480_; lean_object* v_res_481_; 
v_t_boxed_480_ = lean_unbox(v_t_477_);
v_res_481_ = l_Lean_Elab_RecKind_default_elim(v_motive_476_, v_t_boxed_480_, v_h_478_, v_default_479_);
lean_dec(v_default_479_);
return v_res_481_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind_default(void){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = 0;
return v___x_482_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedRecKind(void){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = 0;
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx(uint8_t v_x_484_){
_start:
{
switch(v_x_484_)
{
case 0:
{
lean_object* v___x_485_; 
v___x_485_ = lean_unsigned_to_nat(0u);
return v___x_485_;
}
case 1:
{
lean_object* v___x_486_; 
v___x_486_ = lean_unsigned_to_nat(1u);
return v___x_486_;
}
default: 
{
lean_object* v___x_487_; 
v___x_487_ = lean_unsigned_to_nat(2u);
return v___x_487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorIdx___boxed(lean_object* v_x_488_){
_start:
{
uint8_t v_x_boxed_489_; lean_object* v_res_490_; 
v_x_boxed_489_ = lean_unbox(v_x_488_);
v_res_490_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_boxed_489_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_toCtorIdx(uint8_t v_x_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_toCtorIdx___boxed(lean_object* v_x_493_){
_start:
{
uint8_t v_x_4__boxed_494_; lean_object* v_res_495_; 
v_x_4__boxed_494_ = lean_unbox(v_x_493_);
v_res_495_ = l_Lean_Elab_ComputeKind_toCtorIdx(v_x_4__boxed_494_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg(lean_object* v_k_496_){
_start:
{
lean_inc(v_k_496_);
return v_k_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___redArg___boxed(lean_object* v_k_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Elab_ComputeKind_ctorElim___redArg(v_k_497_);
lean_dec(v_k_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim(lean_object* v_motive_499_, lean_object* v_ctorIdx_500_, uint8_t v_t_501_, lean_object* v_h_502_, lean_object* v_k_503_){
_start:
{
lean_inc(v_k_503_);
return v_k_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_ctorElim___boxed(lean_object* v_motive_504_, lean_object* v_ctorIdx_505_, lean_object* v_t_506_, lean_object* v_h_507_, lean_object* v_k_508_){
_start:
{
uint8_t v_t_boxed_509_; lean_object* v_res_510_; 
v_t_boxed_509_ = lean_unbox(v_t_506_);
v_res_510_ = l_Lean_Elab_ComputeKind_ctorElim(v_motive_504_, v_ctorIdx_505_, v_t_boxed_509_, v_h_507_, v_k_508_);
lean_dec(v_k_508_);
lean_dec(v_ctorIdx_505_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg(lean_object* v_regular_511_){
_start:
{
lean_inc(v_regular_511_);
return v_regular_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___redArg___boxed(lean_object* v_regular_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Elab_ComputeKind_regular_elim___redArg(v_regular_512_);
lean_dec(v_regular_512_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim(lean_object* v_motive_514_, uint8_t v_t_515_, lean_object* v_h_516_, lean_object* v_regular_517_){
_start:
{
lean_inc(v_regular_517_);
return v_regular_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_regular_elim___boxed(lean_object* v_motive_518_, lean_object* v_t_519_, lean_object* v_h_520_, lean_object* v_regular_521_){
_start:
{
uint8_t v_t_boxed_522_; lean_object* v_res_523_; 
v_t_boxed_522_ = lean_unbox(v_t_519_);
v_res_523_ = l_Lean_Elab_ComputeKind_regular_elim(v_motive_518_, v_t_boxed_522_, v_h_520_, v_regular_521_);
lean_dec(v_regular_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg(lean_object* v_meta_524_){
_start:
{
lean_inc(v_meta_524_);
return v_meta_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___redArg___boxed(lean_object* v_meta_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_Elab_ComputeKind_meta_elim___redArg(v_meta_525_);
lean_dec(v_meta_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim(lean_object* v_motive_527_, uint8_t v_t_528_, lean_object* v_h_529_, lean_object* v_meta_530_){
_start:
{
lean_inc(v_meta_530_);
return v_meta_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_meta_elim___boxed(lean_object* v_motive_531_, lean_object* v_t_532_, lean_object* v_h_533_, lean_object* v_meta_534_){
_start:
{
uint8_t v_t_boxed_535_; lean_object* v_res_536_; 
v_t_boxed_535_ = lean_unbox(v_t_532_);
v_res_536_ = l_Lean_Elab_ComputeKind_meta_elim(v_motive_531_, v_t_boxed_535_, v_h_533_, v_meta_534_);
lean_dec(v_meta_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(lean_object* v_noncomputable_537_){
_start:
{
lean_inc(v_noncomputable_537_);
return v_noncomputable_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___redArg___boxed(lean_object* v_noncomputable_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(v_noncomputable_538_);
lean_dec(v_noncomputable_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim(lean_object* v_motive_540_, uint8_t v_t_541_, lean_object* v_h_542_, lean_object* v_noncomputable_543_){
_start:
{
lean_inc(v_noncomputable_543_);
return v_noncomputable_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputeKind_noncomputable_elim___boxed(lean_object* v_motive_544_, lean_object* v_t_545_, lean_object* v_h_546_, lean_object* v_noncomputable_547_){
_start:
{
uint8_t v_t_boxed_548_; lean_object* v_res_549_; 
v_t_boxed_548_ = lean_unbox(v_t_545_);
v_res_549_ = l_Lean_Elab_ComputeKind_noncomputable_elim(v_motive_544_, v_t_boxed_548_, v_h_546_, v_noncomputable_547_);
lean_dec(v_noncomputable_547_);
return v_res_549_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind_default(void){
_start:
{
uint8_t v___x_550_; 
v___x_550_ = 0;
return v___x_550_;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedComputeKind(void){
_start:
{
uint8_t v___x_551_; 
v___x_551_ = 0;
return v___x_551_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_instBEqComputeKind_beq(uint8_t v_x_552_, uint8_t v_y_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_554_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_552_);
v___x_555_ = l_Lean_Elab_ComputeKind_ctorIdx(v_y_553_);
v___x_556_ = lean_nat_dec_eq(v___x_554_, v___x_555_);
lean_dec(v___x_555_);
lean_dec(v___x_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqComputeKind_beq___boxed(lean_object* v_x_557_, lean_object* v_y_558_){
_start:
{
uint8_t v_x_17__boxed_559_; uint8_t v_y_18__boxed_560_; uint8_t v_res_561_; lean_object* v_r_562_; 
v_x_17__boxed_559_ = lean_unbox(v_x_557_);
v_y_18__boxed_560_ = lean_unbox(v_y_558_);
v_res_561_ = l_Lean_Elab_instBEqComputeKind_beq(v_x_17__boxed_559_, v_y_18__boxed_560_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object* v_m_577_){
_start:
{
uint8_t v_visibility_578_; uint8_t v___x_579_; 
v_visibility_578_ = lean_ctor_get_uint8(v_m_577_, sizeof(void*)*3);
v___x_579_ = l_Lean_Elab_Visibility_isPrivate(v_visibility_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPrivate___boxed(lean_object* v_m_580_){
_start:
{
uint8_t v_res_581_; lean_object* v_r_582_; 
v_res_581_ = l_Lean_Elab_Modifiers_isPrivate(v_m_580_);
lean_dec_ref(v_m_580_);
v_r_582_ = lean_box(v_res_581_);
return v_r_582_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPublic(lean_object* v_m_583_){
_start:
{
uint8_t v_visibility_584_; uint8_t v___x_585_; 
v_visibility_584_ = lean_ctor_get_uint8(v_m_583_, sizeof(void*)*3);
v___x_585_ = l_Lean_Elab_Visibility_isPublic(v_visibility_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPublic___boxed(lean_object* v_m_586_){
_start:
{
uint8_t v_res_587_; lean_object* v_r_588_; 
v_res_587_ = l_Lean_Elab_Modifiers_isPublic(v_m_586_);
lean_dec_ref(v_m_586_);
v_r_588_ = lean_box(v_res_587_);
return v_r_588_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isInferredPublic(lean_object* v_env_589_, lean_object* v_m_590_){
_start:
{
uint8_t v_visibility_591_; uint8_t v___x_592_; 
v_visibility_591_ = lean_ctor_get_uint8(v_m_590_, sizeof(void*)*3);
v___x_592_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_589_, v_visibility_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isInferredPublic___boxed(lean_object* v_env_593_, lean_object* v_m_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l_Lean_Elab_Modifiers_isInferredPublic(v_env_593_, v_m_594_);
lean_dec_ref(v_m_594_);
lean_dec_ref(v_env_593_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object* v_x_597_){
_start:
{
uint8_t v_recKind_598_; 
v_recKind_598_ = lean_ctor_get_uint8(v_x_597_, sizeof(void*)*3 + 3);
if (v_recKind_598_ == 0)
{
uint8_t v___x_599_; 
v___x_599_ = 1;
return v___x_599_;
}
else
{
uint8_t v___x_600_; 
v___x_600_ = 0;
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isPartial___boxed(lean_object* v_x_601_){
_start:
{
uint8_t v_res_602_; lean_object* v_r_603_; 
v_res_602_ = l_Lean_Elab_Modifiers_isPartial(v_x_601_);
lean_dec_ref(v_x_601_);
v_r_603_ = lean_box(v_res_602_);
return v_r_603_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNonrec(lean_object* v_x_604_){
_start:
{
uint8_t v_recKind_605_; 
v_recKind_605_ = lean_ctor_get_uint8(v_x_604_, sizeof(void*)*3 + 3);
if (v_recKind_605_ == 1)
{
uint8_t v___x_606_; 
v___x_606_ = 1;
return v___x_606_;
}
else
{
uint8_t v___x_607_; 
v___x_607_ = 0;
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNonrec___boxed(lean_object* v_x_608_){
_start:
{
uint8_t v_res_609_; lean_object* v_r_610_; 
v_res_609_ = l_Lean_Elab_Modifiers_isNonrec(v_x_608_);
lean_dec_ref(v_x_608_);
v_r_610_ = lean_box(v_res_609_);
return v_r_610_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isMeta(lean_object* v_m_611_){
_start:
{
uint8_t v_computeKind_612_; 
v_computeKind_612_ = lean_ctor_get_uint8(v_m_611_, sizeof(void*)*3 + 2);
if (v_computeKind_612_ == 1)
{
uint8_t v___x_613_; 
v___x_613_ = 1;
return v___x_613_;
}
else
{
uint8_t v___x_614_; 
v___x_614_ = 0;
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isMeta___boxed(lean_object* v_m_615_){
_start:
{
uint8_t v_res_616_; lean_object* v_r_617_; 
v_res_616_ = l_Lean_Elab_Modifiers_isMeta(v_m_615_);
lean_dec_ref(v_m_615_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_isNoncomputable(lean_object* v_m_618_){
_start:
{
uint8_t v_computeKind_619_; 
v_computeKind_619_ = lean_ctor_get_uint8(v_m_618_, sizeof(void*)*3 + 2);
if (v_computeKind_619_ == 2)
{
uint8_t v___x_620_; 
v___x_620_ = 1;
return v___x_620_;
}
else
{
uint8_t v___x_621_; 
v___x_621_ = 0;
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_isNoncomputable___boxed(lean_object* v_m_622_){
_start:
{
uint8_t v_res_623_; lean_object* v_r_624_; 
v_res_623_ = l_Lean_Elab_Modifiers_isNoncomputable(v_m_622_);
lean_dec_ref(v_m_622_);
v_r_624_ = lean_box(v_res_623_);
return v_r_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addAttr(lean_object* v_modifiers_625_, lean_object* v_attr_626_){
_start:
{
lean_object* v_stx_627_; lean_object* v_docString_x3f_628_; uint8_t v_visibility_629_; uint8_t v_isProtected_630_; uint8_t v_computeKind_631_; uint8_t v_recKind_632_; uint8_t v_isUnsafe_633_; lean_object* v_attrs_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_642_; 
v_stx_627_ = lean_ctor_get(v_modifiers_625_, 0);
v_docString_x3f_628_ = lean_ctor_get(v_modifiers_625_, 1);
v_visibility_629_ = lean_ctor_get_uint8(v_modifiers_625_, sizeof(void*)*3);
v_isProtected_630_ = lean_ctor_get_uint8(v_modifiers_625_, sizeof(void*)*3 + 1);
v_computeKind_631_ = lean_ctor_get_uint8(v_modifiers_625_, sizeof(void*)*3 + 2);
v_recKind_632_ = lean_ctor_get_uint8(v_modifiers_625_, sizeof(void*)*3 + 3);
v_isUnsafe_633_ = lean_ctor_get_uint8(v_modifiers_625_, sizeof(void*)*3 + 4);
v_attrs_634_ = lean_ctor_get(v_modifiers_625_, 2);
v_isSharedCheck_642_ = !lean_is_exclusive(v_modifiers_625_);
if (v_isSharedCheck_642_ == 0)
{
v___x_636_ = v_modifiers_625_;
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_attrs_634_);
lean_inc(v_docString_x3f_628_);
lean_inc(v_stx_627_);
lean_dec(v_modifiers_625_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = lean_array_push(v_attrs_634_, v_attr_626_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 2, v___x_638_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_stx_627_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_docString_x3f_628_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v___x_638_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, sizeof(void*)*3, v_visibility_629_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, sizeof(void*)*3 + 1, v_isProtected_630_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, sizeof(void*)*3 + 2, v_computeKind_631_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, sizeof(void*)*3 + 3, v_recKind_632_);
lean_ctor_set_uint8(v_reuseFailAlloc_641_, sizeof(void*)*3 + 4, v_isUnsafe_633_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_addFirstAttr(lean_object* v_modifiers_643_, lean_object* v_attr_644_){
_start:
{
lean_object* v_stx_645_; lean_object* v_docString_x3f_646_; uint8_t v_visibility_647_; uint8_t v_isProtected_648_; uint8_t v_computeKind_649_; uint8_t v_recKind_650_; uint8_t v_isUnsafe_651_; lean_object* v_attrs_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_663_; 
v_stx_645_ = lean_ctor_get(v_modifiers_643_, 0);
v_docString_x3f_646_ = lean_ctor_get(v_modifiers_643_, 1);
v_visibility_647_ = lean_ctor_get_uint8(v_modifiers_643_, sizeof(void*)*3);
v_isProtected_648_ = lean_ctor_get_uint8(v_modifiers_643_, sizeof(void*)*3 + 1);
v_computeKind_649_ = lean_ctor_get_uint8(v_modifiers_643_, sizeof(void*)*3 + 2);
v_recKind_650_ = lean_ctor_get_uint8(v_modifiers_643_, sizeof(void*)*3 + 3);
v_isUnsafe_651_ = lean_ctor_get_uint8(v_modifiers_643_, sizeof(void*)*3 + 4);
v_attrs_652_ = lean_ctor_get(v_modifiers_643_, 2);
v_isSharedCheck_663_ = !lean_is_exclusive(v_modifiers_643_);
if (v_isSharedCheck_663_ == 0)
{
v___x_654_ = v_modifiers_643_;
v_isShared_655_ = v_isSharedCheck_663_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_attrs_652_);
lean_inc(v_docString_x3f_646_);
lean_inc(v_stx_645_);
lean_dec(v_modifiers_643_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_663_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_mk_empty_array_with_capacity(v___x_656_);
v___x_658_ = lean_array_push(v___x_657_, v_attr_644_);
v___x_659_ = l_Array_append___redArg(v___x_658_, v_attrs_652_);
lean_dec_ref(v_attrs_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 2, v___x_659_);
v___x_661_ = v___x_654_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_stx_645_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_docString_x3f_646_);
lean_ctor_set(v_reuseFailAlloc_662_, 2, v___x_659_);
lean_ctor_set_uint8(v_reuseFailAlloc_662_, sizeof(void*)*3, v_visibility_647_);
lean_ctor_set_uint8(v_reuseFailAlloc_662_, sizeof(void*)*3 + 1, v_isProtected_648_);
lean_ctor_set_uint8(v_reuseFailAlloc_662_, sizeof(void*)*3 + 2, v_computeKind_649_);
lean_ctor_set_uint8(v_reuseFailAlloc_662_, sizeof(void*)*3 + 3, v_recKind_650_);
lean_ctor_set_uint8(v_reuseFailAlloc_662_, sizeof(void*)*3 + 4, v_isUnsafe_651_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(lean_object* v_p_664_, lean_object* v_as_665_, size_t v_i_666_, size_t v_stop_667_, lean_object* v_b_668_){
_start:
{
lean_object* v___y_670_; uint8_t v___x_674_; 
v___x_674_ = lean_usize_dec_eq(v_i_666_, v_stop_667_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_675_ = lean_array_uget_borrowed(v_as_665_, v_i_666_);
lean_inc_ref(v_p_664_);
lean_inc(v___x_675_);
v___x_676_ = lean_apply_1(v_p_664_, v___x_675_);
v___x_677_ = lean_unbox(v___x_676_);
if (v___x_677_ == 0)
{
v___y_670_ = v_b_668_;
goto v___jp_669_;
}
else
{
lean_object* v___x_678_; 
lean_inc(v___x_675_);
v___x_678_ = lean_array_push(v_b_668_, v___x_675_);
v___y_670_ = v___x_678_;
goto v___jp_669_;
}
}
else
{
lean_dec_ref(v_p_664_);
return v_b_668_;
}
v___jp_669_:
{
size_t v___x_671_; size_t v___x_672_; 
v___x_671_ = ((size_t)1ULL);
v___x_672_ = lean_usize_add(v_i_666_, v___x_671_);
v_i_666_ = v___x_672_;
v_b_668_ = v___y_670_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0___boxed(lean_object* v_p_679_, lean_object* v_as_680_, lean_object* v_i_681_, lean_object* v_stop_682_, lean_object* v_b_683_){
_start:
{
size_t v_i_boxed_684_; size_t v_stop_boxed_685_; lean_object* v_res_686_; 
v_i_boxed_684_ = lean_unbox_usize(v_i_681_);
lean_dec(v_i_681_);
v_stop_boxed_685_ = lean_unbox_usize(v_stop_682_);
lean_dec(v_stop_682_);
v_res_686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_679_, v_as_680_, v_i_boxed_684_, v_stop_boxed_685_, v_b_683_);
lean_dec_ref(v_as_680_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object* v_modifiers_689_, lean_object* v_p_690_){
_start:
{
lean_object* v_stx_691_; lean_object* v_docString_x3f_692_; uint8_t v_visibility_693_; uint8_t v_isProtected_694_; uint8_t v_computeKind_695_; uint8_t v_recKind_696_; uint8_t v_isUnsafe_697_; lean_object* v_attrs_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_725_; 
v_stx_691_ = lean_ctor_get(v_modifiers_689_, 0);
v_docString_x3f_692_ = lean_ctor_get(v_modifiers_689_, 1);
v_visibility_693_ = lean_ctor_get_uint8(v_modifiers_689_, sizeof(void*)*3);
v_isProtected_694_ = lean_ctor_get_uint8(v_modifiers_689_, sizeof(void*)*3 + 1);
v_computeKind_695_ = lean_ctor_get_uint8(v_modifiers_689_, sizeof(void*)*3 + 2);
v_recKind_696_ = lean_ctor_get_uint8(v_modifiers_689_, sizeof(void*)*3 + 3);
v_isUnsafe_697_ = lean_ctor_get_uint8(v_modifiers_689_, sizeof(void*)*3 + 4);
v_attrs_698_ = lean_ctor_get(v_modifiers_689_, 2);
v_isSharedCheck_725_ = !lean_is_exclusive(v_modifiers_689_);
if (v_isSharedCheck_725_ == 0)
{
v___x_700_ = v_modifiers_689_;
v_isShared_701_ = v_isSharedCheck_725_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_attrs_698_);
lean_inc(v_docString_x3f_692_);
lean_inc(v_stx_691_);
lean_dec(v_modifiers_689_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_725_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_array_get_size(v_attrs_698_);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Modifiers_filterAttrs___closed__0));
v___x_705_ = lean_nat_dec_lt(v___x_702_, v___x_703_);
if (v___x_705_ == 0)
{
lean_object* v___x_707_; 
lean_dec_ref(v_attrs_698_);
lean_dec_ref(v_p_690_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 2, v___x_704_);
v___x_707_ = v___x_700_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_stx_691_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_docString_x3f_692_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v___x_704_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*3, v_visibility_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*3 + 1, v_isProtected_694_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*3 + 2, v_computeKind_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*3 + 3, v_recKind_696_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*3 + 4, v_isUnsafe_697_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
else
{
uint8_t v___x_709_; 
v___x_709_ = lean_nat_dec_le(v___x_703_, v___x_703_);
if (v___x_709_ == 0)
{
if (v___x_705_ == 0)
{
lean_object* v___x_711_; 
lean_dec_ref(v_attrs_698_);
lean_dec_ref(v_p_690_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 2, v___x_704_);
v___x_711_ = v___x_700_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_stx_691_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_docString_x3f_692_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v___x_704_);
lean_ctor_set_uint8(v_reuseFailAlloc_712_, sizeof(void*)*3, v_visibility_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_712_, sizeof(void*)*3 + 1, v_isProtected_694_);
lean_ctor_set_uint8(v_reuseFailAlloc_712_, sizeof(void*)*3 + 2, v_computeKind_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_712_, sizeof(void*)*3 + 3, v_recKind_696_);
lean_ctor_set_uint8(v_reuseFailAlloc_712_, sizeof(void*)*3 + 4, v_isUnsafe_697_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
else
{
size_t v___x_713_; size_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_713_ = ((size_t)0ULL);
v___x_714_ = lean_usize_of_nat(v___x_703_);
v___x_715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_690_, v_attrs_698_, v___x_713_, v___x_714_, v___x_704_);
lean_dec_ref(v_attrs_698_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 2, v___x_715_);
v___x_717_ = v___x_700_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_stx_691_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_docString_x3f_692_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v___x_715_);
lean_ctor_set_uint8(v_reuseFailAlloc_718_, sizeof(void*)*3, v_visibility_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_718_, sizeof(void*)*3 + 1, v_isProtected_694_);
lean_ctor_set_uint8(v_reuseFailAlloc_718_, sizeof(void*)*3 + 2, v_computeKind_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_718_, sizeof(void*)*3 + 3, v_recKind_696_);
lean_ctor_set_uint8(v_reuseFailAlloc_718_, sizeof(void*)*3 + 4, v_isUnsafe_697_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
else
{
size_t v___x_719_; size_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_719_ = ((size_t)0ULL);
v___x_720_ = lean_usize_of_nat(v___x_703_);
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_690_, v_attrs_698_, v___x_719_, v___x_720_, v___x_704_);
lean_dec_ref(v_attrs_698_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 2, v___x_721_);
v___x_723_ = v___x_700_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_stx_691_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_docString_x3f_692_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v___x_721_);
lean_ctor_set_uint8(v_reuseFailAlloc_724_, sizeof(void*)*3, v_visibility_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_724_, sizeof(void*)*3 + 1, v_isProtected_694_);
lean_ctor_set_uint8(v_reuseFailAlloc_724_, sizeof(void*)*3 + 2, v_computeKind_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_724_, sizeof(void*)*3 + 3, v_recKind_696_);
lean_ctor_set_uint8(v_reuseFailAlloc_724_, sizeof(void*)*3 + 4, v_isUnsafe_697_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(lean_object* v_p_726_, lean_object* v_as_727_, size_t v_i_728_, size_t v_stop_729_){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = lean_usize_dec_eq(v_i_728_, v_stop_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_731_ = lean_array_uget_borrowed(v_as_727_, v_i_728_);
lean_inc_ref(v_p_726_);
lean_inc(v___x_731_);
v___x_732_ = lean_apply_1(v_p_726_, v___x_731_);
v___x_733_ = lean_unbox(v___x_732_);
if (v___x_733_ == 0)
{
size_t v___x_734_; size_t v___x_735_; 
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_add(v_i_728_, v___x_734_);
v_i_728_ = v___x_735_;
goto _start;
}
else
{
uint8_t v___x_737_; 
lean_dec_ref(v_p_726_);
v___x_737_ = lean_unbox(v___x_732_);
return v___x_737_;
}
}
else
{
uint8_t v___x_738_; 
lean_dec_ref(v_p_726_);
v___x_738_ = 0;
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0___boxed(lean_object* v_p_739_, lean_object* v_as_740_, lean_object* v_i_741_, lean_object* v_stop_742_){
_start:
{
size_t v_i_boxed_743_; size_t v_stop_boxed_744_; uint8_t v_res_745_; lean_object* v_r_746_; 
v_i_boxed_743_ = lean_unbox_usize(v_i_741_);
lean_dec(v_i_741_);
v_stop_boxed_744_ = lean_unbox_usize(v_stop_742_);
lean_dec(v_stop_742_);
v_res_745_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_739_, v_as_740_, v_i_boxed_743_, v_stop_boxed_744_);
lean_dec_ref(v_as_740_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Modifiers_anyAttr(lean_object* v_modifiers_747_, lean_object* v_p_748_){
_start:
{
lean_object* v_attrs_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_attrs_749_ = lean_ctor_get(v_modifiers_747_, 2);
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = lean_array_get_size(v_attrs_749_);
v___x_752_ = lean_nat_dec_lt(v___x_750_, v___x_751_);
if (v___x_752_ == 0)
{
lean_dec_ref(v_p_748_);
return v___x_752_;
}
else
{
if (v___x_752_ == 0)
{
lean_dec_ref(v_p_748_);
return v___x_752_;
}
else
{
size_t v___x_753_; size_t v___x_754_; uint8_t v___x_755_; 
v___x_753_ = ((size_t)0ULL);
v___x_754_ = lean_usize_of_nat(v___x_751_);
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_748_, v_attrs_749_, v___x_753_, v___x_754_);
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Modifiers_anyAttr___boxed(lean_object* v_modifiers_756_, lean_object* v_p_757_){
_start:
{
uint8_t v_res_758_; lean_object* v_r_759_; 
v_res_758_ = l_Lean_Elab_Modifiers_anyAttr(v_modifiers_756_, v_p_757_);
lean_dec_ref(v_modifiers_756_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__0));
v___x_763_ = lean_string_length(v___x_762_);
return v___x_763_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__2, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__2_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2);
v___x_765_ = lean_nat_to_int(v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__0(lean_object* v_attr_773_){
_start:
{
uint8_t v_kind_774_; lean_object* v_name_775_; lean_object* v_stx_776_; lean_object* v___y_778_; 
v_kind_774_ = lean_ctor_get_uint8(v_attr_773_, sizeof(void*)*2);
v_name_775_ = lean_ctor_get(v_attr_773_, 0);
lean_inc(v_name_775_);
v_stx_776_ = lean_ctor_get(v_attr_773_, 1);
lean_inc(v_stx_776_);
lean_dec_ref(v_attr_773_);
switch(v_kind_774_)
{
case 0:
{
lean_object* v___x_800_; 
v___x_800_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__6));
v___y_778_ = v___x_800_;
goto v___jp_777_;
}
case 1:
{
lean_object* v___x_801_; 
v___x_801_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__7));
v___y_778_ = v___x_801_;
goto v___jp_777_;
}
default: 
{
lean_object* v___x_802_; 
v___x_802_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__8));
v___y_778_ = v___x_802_;
goto v___jp_777_;
}
}
v___jp_777_:
{
lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; lean_object* v___x_799_; 
v___x_779_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_779_, 0, v___y_778_);
v___x_780_ = 1;
v___x_781_ = l_Lean_Name_toString(v_name_775_, v___x_780_);
v___x_782_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
v___x_783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_779_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_box(0);
v___x_785_ = 0;
v___x_786_ = l_Lean_Syntax_formatStx(v_stx_776_, v___x_784_, v___x_785_);
v___x_787_ = l_Std_Format_defWidth;
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = l_Std_Format_pretty(v___x_786_, v___x_787_, v___x_788_, v___x_788_);
v___x_790_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
v___x_791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_783_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__0___closed__3, &l_Lean_Elab_instToFormatModifiers___lam__0___closed__3_once, _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3);
v___x_793_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__4));
v___x_794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v___x_791_);
v___x_795_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__0___closed__5));
v___x_796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_792_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = 0;
v___x_799_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set_uint8(v___x_799_, sizeof(void*)*1, v___x_798_);
return v___x_799_;
}
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__0));
v___x_812_ = lean_string_length(v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__5, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__5_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5);
v___x_814_ = lean_nat_to_int(v___x_813_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__35(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__33));
v___x_871_ = lean_string_length(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__36(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__35, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__35_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__35);
v___x_873_ = lean_nat_to_int(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToFormatModifiers___lam__1(lean_object* v___f_883_, lean_object* v___f_884_, lean_object* v_m_885_){
_start:
{
lean_object* v_docString_x3f_886_; uint8_t v_visibility_887_; uint8_t v_isProtected_888_; uint8_t v_computeKind_889_; uint8_t v_recKind_890_; uint8_t v_isUnsafe_891_; lean_object* v_attrs_892_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_938_; 
v_docString_x3f_886_ = lean_ctor_get(v_m_885_, 1);
lean_inc(v_docString_x3f_886_);
v_visibility_887_ = lean_ctor_get_uint8(v_m_885_, sizeof(void*)*3);
v_isProtected_888_ = lean_ctor_get_uint8(v_m_885_, sizeof(void*)*3 + 1);
v_computeKind_889_ = lean_ctor_get_uint8(v_m_885_, sizeof(void*)*3 + 2);
v_recKind_890_ = lean_ctor_get_uint8(v_m_885_, sizeof(void*)*3 + 3);
v_isUnsafe_891_ = lean_ctor_get_uint8(v_m_885_, sizeof(void*)*3 + 4);
v_attrs_892_ = lean_ctor_get(v_m_885_, 2);
lean_inc_ref(v_attrs_892_);
lean_dec_ref(v_m_885_);
if (lean_obj_tag(v_docString_x3f_886_) == 0)
{
lean_object* v___x_942_; 
v___x_942_ = lean_box(0);
v___y_938_ = v___x_942_;
goto v___jp_937_;
}
else
{
lean_object* v_val_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_985_; 
v_val_943_ = lean_ctor_get(v_docString_x3f_886_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v_docString_x3f_886_);
if (v_isSharedCheck_985_ == 0)
{
v___x_945_ = v_docString_x3f_886_;
v_isShared_946_ = v_isSharedCheck_985_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_val_943_);
lean_dec(v_docString_x3f_886_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_985_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_fst_947_; lean_object* v_snd_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_984_; 
v_fst_947_ = lean_ctor_get(v_val_943_, 0);
v_snd_948_ = lean_ctor_get(v_val_943_, 1);
v_isSharedCheck_984_ = !lean_is_exclusive(v_val_943_);
if (v_isSharedCheck_984_ == 0)
{
v___x_950_ = v_val_943_;
v_isShared_951_ = v_isSharedCheck_984_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_snd_948_);
lean_inc(v_fst_947_);
lean_dec(v_val_943_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_984_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_952_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__32));
v___x_953_ = lean_box(0);
v___x_954_ = 0;
v___x_955_ = l_Lean_Syntax_formatStx(v_fst_947_, v___x_953_, v___x_954_);
v___x_956_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__2));
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 5);
lean_ctor_set(v___x_950_, 1, v___x_956_);
lean_ctor_set(v___x_950_, 0, v___x_955_);
v___x_958_ = v___x_950_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_956_);
v___x_958_ = v_reuseFailAlloc_983_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___y_962_; uint8_t v___x_980_; 
v___x_959_ = lean_box(1);
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_980_ = lean_unbox(v_snd_948_);
lean_dec(v_snd_948_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
v___x_981_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__41));
v___y_962_ = v___x_981_;
goto v___jp_961_;
}
else
{
lean_object* v___x_982_; 
v___x_982_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__42));
v___y_962_ = v___x_982_;
goto v___jp_961_;
}
v___jp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 3);
lean_ctor_set(v___x_945_, 0, v___y_962_);
v___x_964_ = v___x_945_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___y_962_);
v___x_964_ = v_reuseFailAlloc_979_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_960_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__36, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__36_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__36);
v___x_967_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__37));
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_965_);
v___x_969_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__38));
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_966_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = 0;
v___x_973_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*1, v___x_972_);
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_952_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__40));
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_box(0);
v___x_978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___y_938_ = v___x_978_;
goto v___jp_937_;
}
}
}
}
}
}
v___jp_893_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_components_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; lean_object* v___x_910_; 
v___x_896_ = l_List_appendTR___redArg(v___y_894_, v___y_895_);
v___x_897_ = lean_array_to_list(v_attrs_892_);
v___x_898_ = lean_box(0);
v___x_899_ = l_List_mapTR_loop___redArg(v___f_883_, v___x_897_, v___x_898_);
v_components_900_ = l_List_appendTR___redArg(v___x_896_, v___x_899_);
v___x_901_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__3));
v___x_902_ = l_Std_Format_joinSep___redArg(v___f_884_, v_components_900_, v___x_901_);
v___x_903_ = lean_obj_once(&l_Lean_Elab_instToFormatModifiers___lam__1___closed__6, &l_Lean_Elab_instToFormatModifiers___lam__1___closed__6_once, _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6);
v___x_904_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__7));
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_902_);
v___x_906_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__8));
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_903_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = 0;
v___x_910_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*1, v___x_909_);
return v___x_910_;
}
v___jp_911_:
{
lean_object* v___x_914_; 
v___x_914_ = l_List_appendTR___redArg(v___y_912_, v___y_913_);
if (v_isUnsafe_891_ == 0)
{
lean_object* v___x_915_; 
v___x_915_ = lean_box(0);
v___y_894_ = v___x_914_;
v___y_895_ = v___x_915_;
goto v___jp_893_;
}
else
{
lean_object* v___x_916_; 
v___x_916_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__11));
v___y_894_ = v___x_914_;
v___y_895_ = v___x_916_;
goto v___jp_893_;
}
}
v___jp_917_:
{
lean_object* v___x_920_; 
v___x_920_ = l_List_appendTR___redArg(v___y_918_, v___y_919_);
switch(v_recKind_890_)
{
case 0:
{
lean_object* v___x_921_; 
v___x_921_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__14));
v___y_912_ = v___x_920_;
v___y_913_ = v___x_921_;
goto v___jp_911_;
}
case 1:
{
lean_object* v___x_922_; 
v___x_922_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__17));
v___y_912_ = v___x_920_;
v___y_913_ = v___x_922_;
goto v___jp_911_;
}
default: 
{
lean_object* v___x_923_; 
v___x_923_ = lean_box(0);
v___y_912_ = v___x_920_;
v___y_913_ = v___x_923_;
goto v___jp_911_;
}
}
}
v___jp_924_:
{
lean_object* v___x_927_; 
v___x_927_ = l_List_appendTR___redArg(v___y_925_, v___y_926_);
switch(v_computeKind_889_)
{
case 0:
{
lean_object* v___x_928_; 
v___x_928_ = lean_box(0);
v___y_918_ = v___x_927_;
v___y_919_ = v___x_928_;
goto v___jp_917_;
}
case 1:
{
lean_object* v___x_929_; 
v___x_929_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__20));
v___y_918_ = v___x_927_;
v___y_919_ = v___x_929_;
goto v___jp_917_;
}
default: 
{
lean_object* v___x_930_; 
v___x_930_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__23));
v___y_918_ = v___x_927_;
v___y_919_ = v___x_930_;
goto v___jp_917_;
}
}
}
v___jp_931_:
{
lean_object* v___x_934_; 
v___x_934_ = l_List_appendTR___redArg(v___y_932_, v___y_933_);
if (v_isProtected_888_ == 0)
{
lean_object* v___x_935_; 
v___x_935_ = lean_box(0);
v___y_925_ = v___x_934_;
v___y_926_ = v___x_935_;
goto v___jp_924_;
}
else
{
lean_object* v___x_936_; 
v___x_936_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__26));
v___y_925_ = v___x_934_;
v___y_926_ = v___x_936_;
goto v___jp_924_;
}
}
v___jp_937_:
{
switch(v_visibility_887_)
{
case 0:
{
lean_object* v___x_939_; 
v___x_939_ = lean_box(0);
v___y_932_ = v___y_938_;
v___y_933_ = v___x_939_;
goto v___jp_931_;
}
case 1:
{
lean_object* v___x_940_; 
v___x_940_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__28));
v___y_932_ = v___y_938_;
v___y_933_ = v___x_940_;
goto v___jp_931_;
}
default: 
{
lean_object* v___x_941_; 
v___x_941_ = ((lean_object*)(l_Lean_Elab_instToFormatModifiers___lam__1___closed__30));
v___y_932_ = v___y_938_;
v___y_933_ = v___x_941_;
goto v___jp_931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToStringModifiers___lam__0(lean_object* v_f_992_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = l_Std_Format_defWidth;
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = l_Std_Format_pretty(v_f_992_, v___x_993_, v___x_994_, v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((lean_object*)(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0));
v___x_1003_ = l_Lean_stringToMessageData(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg(lean_object* v_inst_1004_, lean_object* v_inst_1005_, lean_object* v_optDocComment_1006_){
_start:
{
lean_object* v_toApplicative_1007_; lean_object* v_toPure_1008_; lean_object* v___x_1009_; 
v_toApplicative_1007_ = lean_ctor_get(v_inst_1004_, 0);
v_toPure_1008_ = lean_ctor_get(v_toApplicative_1007_, 1);
v___x_1009_ = l_Lean_Syntax_getOptional_x3f(v_optDocComment_1006_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_inc(v_toPure_1008_);
lean_dec_ref(v_inst_1005_);
lean_dec_ref(v_inst_1004_);
v___x_1010_ = lean_box(0);
v___x_1011_ = lean_apply_2(v_toPure_1008_, lean_box(0), v___x_1010_);
return v___x_1011_;
}
else
{
lean_object* v_val_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1033_; 
v_val_1012_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1014_ = v___x_1009_;
v_isShared_1015_ = v_isSharedCheck_1033_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_val_1012_);
lean_dec(v___x_1009_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1033_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = l_Lean_Syntax_getArg(v_val_1012_, v___x_1016_);
if (lean_obj_tag(v___x_1017_) == 2)
{
lean_object* v_val_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
lean_inc(v_toPure_1008_);
lean_dec(v_val_1012_);
lean_dec_ref(v_inst_1005_);
lean_dec_ref(v_inst_1004_);
v_val_1018_ = lean_ctor_get(v___x_1017_, 1);
lean_inc_ref(v_val_1018_);
lean_dec_ref(v___x_1017_);
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = lean_string_utf8_byte_size(v_val_1018_);
v___x_1021_ = lean_unsigned_to_nat(2u);
v___x_1022_ = lean_nat_sub(v___x_1020_, v___x_1021_);
v___x_1023_ = lean_string_utf8_extract(v_val_1018_, v___x_1019_, v___x_1022_);
lean_dec(v___x_1022_);
lean_dec_ref(v_val_1018_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1023_);
v___x_1025_ = v___x_1014_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_apply_2(v_toPure_1008_, lean_box(0), v___x_1025_);
return v___x_1026_;
}
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_del_object(v___x_1014_);
v___x_1028_ = lean_obj_once(&l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1, &l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1_once, _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1);
v___x_1029_ = l_Lean_MessageData_ofSyntax(v___x_1017_);
v___x_1030_ = l_Lean_indentD(v___x_1029_);
v___x_1031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1028_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = l_Lean_throwErrorAt___redArg(v_inst_1004_, v_inst_1005_, v_val_1012_, v___x_1031_);
return v___x_1032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___redArg___boxed(lean_object* v_inst_1034_, lean_object* v_inst_1035_, lean_object* v_optDocComment_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1034_, v_inst_1035_, v_optDocComment_1036_);
lean_dec(v_optDocComment_1036_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f(lean_object* v_m_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_optDocComment_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(v_inst_1039_, v_inst_1040_, v_optDocComment_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDocComment_x3f___boxed(lean_object* v_m_1043_, lean_object* v_inst_1044_, lean_object* v_inst_1045_, lean_object* v_optDocComment_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_Elab_expandOptDocComment_x3f(v_m_1043_, v_inst_1044_, v_inst_1045_, v_optDocComment_1046_);
lean_dec(v_optDocComment_1046_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0(lean_object* v_stx_1048_, lean_object* v___y_1049_, uint8_t v_visibility_1050_, uint8_t v___y_1051_, uint8_t v___y_1052_, uint8_t v___y_1053_, lean_object* v_toPure_1054_, lean_object* v_unsafeStx_1055_, lean_object* v_attrs_1056_){
_start:
{
uint8_t v___y_1058_; uint8_t v___x_1061_; 
v___x_1061_ = l_Lean_Syntax_isNone(v_unsafeStx_1055_);
if (v___x_1061_ == 0)
{
uint8_t v___x_1062_; 
v___x_1062_ = 1;
v___y_1058_ = v___x_1062_;
goto v___jp_1057_;
}
else
{
uint8_t v___x_1063_; 
v___x_1063_ = 0;
v___y_1058_ = v___x_1063_;
goto v___jp_1057_;
}
v___jp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1059_, 0, v_stx_1048_);
lean_ctor_set(v___x_1059_, 1, v___y_1049_);
lean_ctor_set(v___x_1059_, 2, v_attrs_1056_);
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*3, v_visibility_1050_);
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*3 + 1, v___y_1051_);
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*3 + 2, v___y_1052_);
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*3 + 3, v___y_1053_);
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*3 + 4, v___y_1058_);
v___x_1060_ = lean_apply_2(v_toPure_1054_, lean_box(0), v___x_1059_);
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__0___boxed(lean_object* v_stx_1064_, lean_object* v___y_1065_, lean_object* v_visibility_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v_toPure_1070_, lean_object* v_unsafeStx_1071_, lean_object* v_attrs_1072_){
_start:
{
uint8_t v_visibility_boxed_1073_; uint8_t v___y_721__boxed_1074_; uint8_t v___y_722__boxed_1075_; uint8_t v___y_723__boxed_1076_; lean_object* v_res_1077_; 
v_visibility_boxed_1073_ = lean_unbox(v_visibility_1066_);
v___y_721__boxed_1074_ = lean_unbox(v___y_1067_);
v___y_722__boxed_1075_ = lean_unbox(v___y_1068_);
v___y_723__boxed_1076_ = lean_unbox(v___y_1069_);
v_res_1077_ = l_Lean_Elab_elabModifiers___redArg___lam__0(v_stx_1064_, v___y_1065_, v_visibility_boxed_1073_, v___y_721__boxed_1074_, v___y_722__boxed_1075_, v___y_723__boxed_1076_, v_toPure_1070_, v_unsafeStx_1071_, v_attrs_1072_);
lean_dec(v_unsafeStx_1071_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__1(lean_object* v___f_1078_, lean_object* v_attrs_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_apply_1(v___f_1078_, v_attrs_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3(lean_object* v_stx_1081_, lean_object* v___y_1082_, uint8_t v___y_1083_, uint8_t v___y_1084_, lean_object* v_toPure_1085_, lean_object* v_unsafeStx_1086_, lean_object* v_attrsStx_1087_, lean_object* v___x_1088_, lean_object* v_toBind_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_inst_1097_, lean_object* v_inst_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_protectedStx_1102_, uint8_t v_visibility_1103_){
_start:
{
uint8_t v___y_1105_; uint8_t v___x_1120_; 
v___x_1120_ = l_Lean_Syntax_isNone(v_protectedStx_1102_);
if (v___x_1120_ == 0)
{
uint8_t v___x_1121_; 
v___x_1121_ = 1;
v___y_1105_ = v___x_1121_;
goto v___jp_1104_;
}
else
{
uint8_t v___x_1122_; 
v___x_1122_ = 0;
v___y_1105_ = v___x_1122_;
goto v___jp_1104_;
}
v___jp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___f_1110_; lean_object* v___x_1111_; 
v___x_1106_ = lean_box(v_visibility_1103_);
v___x_1107_ = lean_box(v___y_1105_);
v___x_1108_ = lean_box(v___y_1083_);
v___x_1109_ = lean_box(v___y_1084_);
lean_inc(v_toPure_1085_);
v___f_1110_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_1110_, 0, v_stx_1081_);
lean_closure_set(v___f_1110_, 1, v___y_1082_);
lean_closure_set(v___f_1110_, 2, v___x_1106_);
lean_closure_set(v___f_1110_, 3, v___x_1107_);
lean_closure_set(v___f_1110_, 4, v___x_1108_);
lean_closure_set(v___f_1110_, 5, v___x_1109_);
lean_closure_set(v___f_1110_, 6, v_toPure_1085_);
lean_closure_set(v___f_1110_, 7, v_unsafeStx_1086_);
v___x_1111_ = l_Lean_Syntax_getOptional_x3f(v_attrsStx_1087_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___f_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec(v_inst_1101_);
lean_dec(v_inst_1100_);
lean_dec_ref(v_inst_1099_);
lean_dec(v_inst_1098_);
lean_dec(v_inst_1097_);
lean_dec_ref(v_inst_1096_);
lean_dec_ref(v_inst_1095_);
lean_dec_ref(v_inst_1094_);
lean_dec_ref(v_inst_1093_);
lean_dec_ref(v_inst_1092_);
lean_dec_ref(v_inst_1091_);
lean_dec_ref(v_inst_1090_);
v___f_1112_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1112_, 0, v___f_1110_);
v___x_1113_ = lean_mk_empty_array_with_capacity(v___x_1088_);
v___x_1114_ = lean_apply_2(v_toPure_1085_, lean_box(0), v___x_1113_);
v___x_1115_ = lean_apply_4(v_toBind_1089_, lean_box(0), lean_box(0), v___x_1114_, v___f_1112_);
return v___x_1115_;
}
else
{
lean_object* v_val_1116_; lean_object* v___f_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec(v_toPure_1085_);
v_val_1116_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_val_1116_);
lean_dec_ref(v___x_1111_);
v___f_1117_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1117_, 0, v___f_1110_);
v___x_1118_ = l_Lean_Elab_elabDeclAttrs___redArg(v_inst_1090_, v_inst_1091_, v_inst_1092_, v_inst_1093_, v_inst_1094_, v_inst_1095_, v_inst_1096_, v_inst_1097_, v_inst_1098_, v_inst_1099_, v_inst_1100_, v_inst_1101_, v_val_1116_);
lean_dec(v_val_1116_);
v___x_1119_ = lean_apply_4(v_toBind_1089_, lean_box(0), lean_box(0), v___x_1118_, v___f_1117_);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_stx_1123_ = _args[0];
lean_object* v___y_1124_ = _args[1];
lean_object* v___y_1125_ = _args[2];
lean_object* v___y_1126_ = _args[3];
lean_object* v_toPure_1127_ = _args[4];
lean_object* v_unsafeStx_1128_ = _args[5];
lean_object* v_attrsStx_1129_ = _args[6];
lean_object* v___x_1130_ = _args[7];
lean_object* v_toBind_1131_ = _args[8];
lean_object* v_inst_1132_ = _args[9];
lean_object* v_inst_1133_ = _args[10];
lean_object* v_inst_1134_ = _args[11];
lean_object* v_inst_1135_ = _args[12];
lean_object* v_inst_1136_ = _args[13];
lean_object* v_inst_1137_ = _args[14];
lean_object* v_inst_1138_ = _args[15];
lean_object* v_inst_1139_ = _args[16];
lean_object* v_inst_1140_ = _args[17];
lean_object* v_inst_1141_ = _args[18];
lean_object* v_inst_1142_ = _args[19];
lean_object* v_inst_1143_ = _args[20];
lean_object* v_protectedStx_1144_ = _args[21];
lean_object* v_visibility_1145_ = _args[22];
_start:
{
uint8_t v___y_751__boxed_1146_; uint8_t v___y_752__boxed_1147_; uint8_t v_visibility_boxed_1148_; lean_object* v_res_1149_; 
v___y_751__boxed_1146_ = lean_unbox(v___y_1125_);
v___y_752__boxed_1147_ = lean_unbox(v___y_1126_);
v_visibility_boxed_1148_ = lean_unbox(v_visibility_1145_);
v_res_1149_ = l_Lean_Elab_elabModifiers___redArg___lam__3(v_stx_1123_, v___y_1124_, v___y_751__boxed_1146_, v___y_752__boxed_1147_, v_toPure_1127_, v_unsafeStx_1128_, v_attrsStx_1129_, v___x_1130_, v_toBind_1131_, v_inst_1132_, v_inst_1133_, v_inst_1134_, v_inst_1135_, v_inst_1136_, v_inst_1137_, v_inst_1138_, v_inst_1139_, v_inst_1140_, v_inst_1141_, v_inst_1142_, v_inst_1143_, v_protectedStx_1144_, v_visibility_boxed_1148_);
lean_dec(v_protectedStx_1144_);
lean_dec(v___x_1130_);
lean_dec(v_attrsStx_1129_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2(lean_object* v___f_1150_, uint8_t v_visibility_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_box(v_visibility_1151_);
v___x_1153_ = lean_apply_1(v___f_1150_, v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__2___boxed(lean_object* v___f_1154_, lean_object* v_visibility_1155_){
_start:
{
uint8_t v_visibility_boxed_1156_; lean_object* v_res_1157_; 
v_visibility_boxed_1156_ = lean_unbox(v_visibility_1155_);
v_res_1157_ = l_Lean_Elab_elabModifiers___redArg___lam__2(v___f_1154_, v_visibility_boxed_1156_);
return v_res_1157_;
}
}
static lean_object* _init_l_Lean_Elab_elabModifiers___redArg___lam__7___closed__6(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___lam__7___closed__5));
v___x_1173_ = l_Lean_stringToMessageData(v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__7(lean_object* v_stx_1174_, uint8_t v___y_1175_, uint8_t v___y_1176_, lean_object* v_toPure_1177_, lean_object* v_unsafeStx_1178_, lean_object* v_attrsStx_1179_, lean_object* v___x_1180_, lean_object* v_toBind_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_protectedStx_1194_, lean_object* v_visibilityStx_1195_, lean_object* v_docCommentStx_1196_, lean_object* v___x_1197_, lean_object* v_____do__lift_1198_){
_start:
{
lean_object* v___y_1200_; lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Syntax_getOptional_x3f(v_docCommentStx_1196_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; 
lean_dec_ref(v___x_1197_);
v___x_1230_ = lean_box(0);
v___y_1200_ = v___x_1230_;
goto v___jp_1199_;
}
else
{
lean_object* v_val_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1241_; 
v_val_1231_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1233_ = v___x_1229_;
v_isShared_1234_ = v_isSharedCheck_1241_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_val_1231_);
lean_dec(v___x_1229_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1241_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1235_ = l_Lean_doc_verso;
v___x_1236_ = l_Lean_Option_get___redArg(v___x_1197_, v_____do__lift_1198_, v___x_1235_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_val_1231_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1237_);
v___x_1239_ = v___x_1233_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
v___y_1200_ = v___x_1239_;
goto v___jp_1199_;
}
}
}
v___jp_1199_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___f_1203_; lean_object* v___x_1204_; 
v___x_1201_ = lean_box(v___y_1175_);
v___x_1202_ = lean_box(v___y_1176_);
lean_inc_ref(v_inst_1185_);
lean_inc_ref(v_inst_1182_);
lean_inc(v_toBind_1181_);
lean_inc(v_toPure_1177_);
v___f_1203_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__3___boxed), 23, 22);
lean_closure_set(v___f_1203_, 0, v_stx_1174_);
lean_closure_set(v___f_1203_, 1, v___y_1200_);
lean_closure_set(v___f_1203_, 2, v___x_1201_);
lean_closure_set(v___f_1203_, 3, v___x_1202_);
lean_closure_set(v___f_1203_, 4, v_toPure_1177_);
lean_closure_set(v___f_1203_, 5, v_unsafeStx_1178_);
lean_closure_set(v___f_1203_, 6, v_attrsStx_1179_);
lean_closure_set(v___f_1203_, 7, v___x_1180_);
lean_closure_set(v___f_1203_, 8, v_toBind_1181_);
lean_closure_set(v___f_1203_, 9, v_inst_1182_);
lean_closure_set(v___f_1203_, 10, v_inst_1183_);
lean_closure_set(v___f_1203_, 11, v_inst_1184_);
lean_closure_set(v___f_1203_, 12, v_inst_1185_);
lean_closure_set(v___f_1203_, 13, v_inst_1186_);
lean_closure_set(v___f_1203_, 14, v_inst_1187_);
lean_closure_set(v___f_1203_, 15, v_inst_1188_);
lean_closure_set(v___f_1203_, 16, v_inst_1189_);
lean_closure_set(v___f_1203_, 17, v_inst_1190_);
lean_closure_set(v___f_1203_, 18, v_inst_1191_);
lean_closure_set(v___f_1203_, 19, v_inst_1192_);
lean_closure_set(v___f_1203_, 20, v_inst_1193_);
lean_closure_set(v___f_1203_, 21, v_protectedStx_1194_);
v___x_1204_ = l_Lean_Syntax_getOptional_x3f(v_visibilityStx_1195_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v___f_1205_; uint8_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1182_);
v___f_1205_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1205_, 0, v___f_1203_);
v___x_1206_ = 0;
v___x_1207_ = lean_box(v___x_1206_);
v___x_1208_ = lean_apply_2(v_toPure_1177_, lean_box(0), v___x_1207_);
v___x_1209_ = lean_apply_4(v_toBind_1181_, lean_box(0), lean_box(0), v___x_1208_, v___f_1205_);
return v___x_1209_;
}
else
{
lean_object* v_val_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v_val_1210_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_val_1210_);
lean_dec_ref(v___x_1204_);
v___x_1211_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___lam__7___closed__3));
lean_inc(v_val_1210_);
v___x_1212_ = l_Lean_Syntax_isOfKind(v_val_1210_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___lam__7___closed__4));
lean_inc(v_val_1210_);
v___x_1214_ = l_Lean_Syntax_isOfKind(v_val_1210_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___f_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
lean_dec(v_toPure_1177_);
v___f_1215_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1215_, 0, v___f_1203_);
v___x_1216_ = lean_obj_once(&l_Lean_Elab_elabModifiers___redArg___lam__7___closed__6, &l_Lean_Elab_elabModifiers___redArg___lam__7___closed__6_once, _init_l_Lean_Elab_elabModifiers___redArg___lam__7___closed__6);
v___x_1217_ = l_Lean_throwErrorAt___redArg(v_inst_1182_, v_inst_1185_, v_val_1210_, v___x_1216_);
v___x_1218_ = lean_apply_4(v_toBind_1181_, lean_box(0), lean_box(0), v___x_1217_, v___f_1215_);
return v___x_1218_;
}
else
{
lean_object* v___f_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_dec(v_val_1210_);
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1182_);
v___f_1219_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1219_, 0, v___f_1203_);
v___x_1220_ = 2;
v___x_1221_ = lean_box(v___x_1220_);
v___x_1222_ = lean_apply_2(v_toPure_1177_, lean_box(0), v___x_1221_);
v___x_1223_ = lean_apply_4(v_toBind_1181_, lean_box(0), lean_box(0), v___x_1222_, v___f_1219_);
return v___x_1223_;
}
}
else
{
lean_object* v___f_1224_; uint8_t v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec(v_val_1210_);
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1182_);
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1224_, 0, v___f_1203_);
v___x_1225_ = 1;
v___x_1226_ = lean_box(v___x_1225_);
v___x_1227_ = lean_apply_2(v_toPure_1177_, lean_box(0), v___x_1226_);
v___x_1228_ = lean_apply_4(v_toBind_1181_, lean_box(0), lean_box(0), v___x_1227_, v___f_1224_);
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_stx_1242_ = _args[0];
lean_object* v___y_1243_ = _args[1];
lean_object* v___y_1244_ = _args[2];
lean_object* v_toPure_1245_ = _args[3];
lean_object* v_unsafeStx_1246_ = _args[4];
lean_object* v_attrsStx_1247_ = _args[5];
lean_object* v___x_1248_ = _args[6];
lean_object* v_toBind_1249_ = _args[7];
lean_object* v_inst_1250_ = _args[8];
lean_object* v_inst_1251_ = _args[9];
lean_object* v_inst_1252_ = _args[10];
lean_object* v_inst_1253_ = _args[11];
lean_object* v_inst_1254_ = _args[12];
lean_object* v_inst_1255_ = _args[13];
lean_object* v_inst_1256_ = _args[14];
lean_object* v_inst_1257_ = _args[15];
lean_object* v_inst_1258_ = _args[16];
lean_object* v_inst_1259_ = _args[17];
lean_object* v_inst_1260_ = _args[18];
lean_object* v_inst_1261_ = _args[19];
lean_object* v_protectedStx_1262_ = _args[20];
lean_object* v_visibilityStx_1263_ = _args[21];
lean_object* v_docCommentStx_1264_ = _args[22];
lean_object* v___x_1265_ = _args[23];
lean_object* v_____do__lift_1266_ = _args[24];
_start:
{
uint8_t v___y_877__boxed_1267_; uint8_t v___y_878__boxed_1268_; lean_object* v_res_1269_; 
v___y_877__boxed_1267_ = lean_unbox(v___y_1243_);
v___y_878__boxed_1268_ = lean_unbox(v___y_1244_);
v_res_1269_ = l_Lean_Elab_elabModifiers___redArg___lam__7(v_stx_1242_, v___y_877__boxed_1267_, v___y_878__boxed_1268_, v_toPure_1245_, v_unsafeStx_1246_, v_attrsStx_1247_, v___x_1248_, v_toBind_1249_, v_inst_1250_, v_inst_1251_, v_inst_1252_, v_inst_1253_, v_inst_1254_, v_inst_1255_, v_inst_1256_, v_inst_1257_, v_inst_1258_, v_inst_1259_, v_inst_1260_, v_inst_1261_, v_protectedStx_1262_, v_visibilityStx_1263_, v_docCommentStx_1264_, v___x_1265_, v_____do__lift_1266_);
lean_dec_ref(v_____do__lift_1266_);
lean_dec(v_docCommentStx_1264_);
lean_dec(v_visibilityStx_1263_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers___redArg(lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_stx_1292_){
_start:
{
lean_object* v___x_1293_; lean_object* v_toApplicative_1294_; lean_object* v_toBind_1295_; lean_object* v_toPure_1296_; lean_object* v___x_1297_; lean_object* v_docCommentStx_1298_; lean_object* v___x_1299_; lean_object* v_attrsStx_1300_; lean_object* v___x_1301_; lean_object* v_visibilityStx_1302_; lean_object* v___x_1303_; lean_object* v_protectedStx_1304_; lean_object* v___y_1306_; uint8_t v___y_1307_; uint8_t v___y_1308_; uint8_t v___y_1314_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1293_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1294_ = lean_ctor_get(v_inst_1280_, 0);
v_toBind_1295_ = lean_ctor_get(v_inst_1280_, 1);
lean_inc(v_toBind_1295_);
v_toPure_1296_ = lean_ctor_get(v_toApplicative_1294_, 1);
lean_inc(v_toPure_1296_);
v___x_1297_ = lean_unsigned_to_nat(0u);
v_docCommentStx_1298_ = l_Lean_Syntax_getArg(v_stx_1292_, v___x_1297_);
v___x_1299_ = lean_unsigned_to_nat(1u);
v_attrsStx_1300_ = l_Lean_Syntax_getArg(v_stx_1292_, v___x_1299_);
v___x_1301_ = lean_unsigned_to_nat(2u);
v_visibilityStx_1302_ = l_Lean_Syntax_getArg(v_stx_1292_, v___x_1301_);
v___x_1303_ = lean_unsigned_to_nat(3u);
v_protectedStx_1304_ = l_Lean_Syntax_getArg(v_stx_1292_, v___x_1303_);
v___x_1327_ = lean_unsigned_to_nat(4u);
v___x_1328_ = l_Lean_Syntax_getArg(v_stx_1292_, v___x_1327_);
v___x_1329_ = l_Lean_Syntax_isNone(v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1330_ = l_Lean_Syntax_getArg(v___x_1328_, v___x_1297_);
lean_dec(v___x_1328_);
v___x_1331_ = l_Lean_Syntax_getKind(v___x_1330_);
v___x_1332_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__1));
v___x_1333_ = lean_name_eq(v___x_1331_, v___x_1332_);
lean_dec(v___x_1331_);
if (v___x_1333_ == 0)
{
uint8_t v___x_1334_; 
v___x_1334_ = 2;
v___y_1314_ = v___x_1334_;
goto v___jp_1313_;
}
else
{
uint8_t v___x_1335_; 
v___x_1335_ = 1;
v___y_1314_ = v___x_1335_;
goto v___jp_1313_;
}
}
else
{
uint8_t v___x_1336_; 
lean_dec(v___x_1328_);
v___x_1336_ = 0;
v___y_1314_ = v___x_1336_;
goto v___jp_1313_;
}
v___jp_1305_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; 
v___x_1309_ = lean_box(v___y_1307_);
v___x_1310_ = lean_box(v___y_1308_);
lean_inc(v_inst_1288_);
lean_inc(v_toBind_1295_);
v___f_1311_ = lean_alloc_closure((void*)(l_Lean_Elab_elabModifiers___redArg___lam__7___boxed), 25, 24);
lean_closure_set(v___f_1311_, 0, v_stx_1292_);
lean_closure_set(v___f_1311_, 1, v___x_1309_);
lean_closure_set(v___f_1311_, 2, v___x_1310_);
lean_closure_set(v___f_1311_, 3, v_toPure_1296_);
lean_closure_set(v___f_1311_, 4, v___y_1306_);
lean_closure_set(v___f_1311_, 5, v_attrsStx_1300_);
lean_closure_set(v___f_1311_, 6, v___x_1297_);
lean_closure_set(v___f_1311_, 7, v_toBind_1295_);
lean_closure_set(v___f_1311_, 8, v_inst_1280_);
lean_closure_set(v___f_1311_, 9, v_inst_1281_);
lean_closure_set(v___f_1311_, 10, v_inst_1282_);
lean_closure_set(v___f_1311_, 11, v_inst_1283_);
lean_closure_set(v___f_1311_, 12, v_inst_1285_);
lean_closure_set(v___f_1311_, 13, v_inst_1286_);
lean_closure_set(v___f_1311_, 14, v_inst_1287_);
lean_closure_set(v___f_1311_, 15, v_inst_1288_);
lean_closure_set(v___f_1311_, 16, v_inst_1289_);
lean_closure_set(v___f_1311_, 17, v_inst_1290_);
lean_closure_set(v___f_1311_, 18, v_inst_1291_);
lean_closure_set(v___f_1311_, 19, v_inst_1284_);
lean_closure_set(v___f_1311_, 20, v_protectedStx_1304_);
lean_closure_set(v___f_1311_, 21, v_visibilityStx_1302_);
lean_closure_set(v___f_1311_, 22, v_docCommentStx_1298_);
lean_closure_set(v___f_1311_, 23, v___x_1293_);
v___x_1312_ = lean_apply_4(v_toBind_1295_, lean_box(0), lean_box(0), v_inst_1288_, v___f_1311_);
return v___x_1312_;
}
v___jp_1313_:
{
lean_object* v___x_1315_; lean_object* v_unsafeStx_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1315_ = lean_unsigned_to_nat(5u);
v_unsafeStx_1316_ = l_Lean_Syntax_getArg(v_stx_1292_, v___x_1315_);
v___x_1317_ = lean_unsigned_to_nat(6u);
v___x_1318_ = l_Lean_Syntax_getArg(v_stx_1292_, v___x_1317_);
v___x_1319_ = l_Lean_Syntax_isNone(v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1320_ = l_Lean_Syntax_getArg(v___x_1318_, v___x_1297_);
lean_dec(v___x_1318_);
v___x_1321_ = l_Lean_Syntax_getKind(v___x_1320_);
v___x_1322_ = ((lean_object*)(l_Lean_Elab_elabModifiers___redArg___closed__0));
v___x_1323_ = lean_name_eq(v___x_1321_, v___x_1322_);
lean_dec(v___x_1321_);
if (v___x_1323_ == 0)
{
uint8_t v___x_1324_; 
v___x_1324_ = 1;
v___y_1306_ = v_unsafeStx_1316_;
v___y_1307_ = v___y_1314_;
v___y_1308_ = v___x_1324_;
goto v___jp_1305_;
}
else
{
uint8_t v___x_1325_; 
v___x_1325_ = 0;
v___y_1306_ = v_unsafeStx_1316_;
v___y_1307_ = v___y_1314_;
v___y_1308_ = v___x_1325_;
goto v___jp_1305_;
}
}
else
{
uint8_t v___x_1326_; 
lean_dec(v___x_1318_);
v___x_1326_ = 2;
v___y_1306_ = v_unsafeStx_1316_;
v___y_1307_ = v___y_1314_;
v___y_1308_ = v___x_1326_;
goto v___jp_1305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabModifiers(lean_object* v_m_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_inst_1341_, lean_object* v_inst_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_stx_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_Elab_elabModifiers___redArg(v_inst_1338_, v_inst_1339_, v_inst_1340_, v_inst_1341_, v_inst_1342_, v_inst_1343_, v_inst_1344_, v_inst_1345_, v_inst_1346_, v_inst_1347_, v_inst_1348_, v_inst_1349_, v_stx_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__0(lean_object* v_toPure_1352_, lean_object* v_declName_1353_, lean_object* v_____r_1354_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_apply_2(v_toPure_1352_, lean_box(0), v_declName_1353_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__1(lean_object* v_declName_1356_, lean_object* v_env_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_addProtected(v_env_1357_, v_declName_1356_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2(lean_object* v_modifiers_1359_, lean_object* v_toPure_1360_, lean_object* v_declName_1361_, lean_object* v_modifyEnv_1362_, lean_object* v___f_1363_, lean_object* v_toBind_1364_, lean_object* v___f_1365_, lean_object* v_____r_1366_){
_start:
{
uint8_t v_isProtected_1367_; 
v_isProtected_1367_ = lean_ctor_get_uint8(v_modifiers_1359_, sizeof(void*)*3 + 1);
if (v_isProtected_1367_ == 0)
{
lean_object* v___x_1368_; 
lean_dec(v___f_1365_);
lean_dec(v_toBind_1364_);
lean_dec_ref(v___f_1363_);
lean_dec(v_modifyEnv_1362_);
v___x_1368_ = lean_apply_2(v_toPure_1360_, lean_box(0), v_declName_1361_);
return v___x_1368_;
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec(v_declName_1361_);
lean_dec(v_toPure_1360_);
v___x_1369_ = lean_apply_1(v_modifyEnv_1362_, v___f_1363_);
v___x_1370_ = lean_apply_4(v_toBind_1364_, lean_box(0), lean_box(0), v___x_1369_, v___f_1365_);
return v___x_1370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__2___boxed(lean_object* v_modifiers_1371_, lean_object* v_toPure_1372_, lean_object* v_declName_1373_, lean_object* v_modifyEnv_1374_, lean_object* v___f_1375_, lean_object* v_toBind_1376_, lean_object* v___f_1377_, lean_object* v_____r_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_Elab_applyVisibility___redArg___lam__2(v_modifiers_1371_, v_toPure_1372_, v_declName_1373_, v_modifyEnv_1374_, v___f_1375_, v_toBind_1376_, v___f_1377_, v_____r_1378_);
lean_dec_ref(v_modifiers_1371_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__3(lean_object* v_toPure_1380_, lean_object* v_modifiers_1381_, lean_object* v_modifyEnv_1382_, lean_object* v_toBind_1383_, lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_inst_1386_, lean_object* v_inst_1387_, lean_object* v_inst_1388_, lean_object* v_____r_1389_, lean_object* v_declName_1390_){
_start:
{
lean_object* v___f_1391_; lean_object* v___f_1392_; lean_object* v___f_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_inc(v_declName_1390_);
lean_inc(v_toPure_1380_);
v___f_1391_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1391_, 0, v_toPure_1380_);
lean_closure_set(v___f_1391_, 1, v_declName_1390_);
lean_inc(v_declName_1390_);
v___f_1392_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1392_, 0, v_declName_1390_);
lean_inc(v_toBind_1383_);
lean_inc(v_declName_1390_);
v___f_1393_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1393_, 0, v_modifiers_1381_);
lean_closure_set(v___f_1393_, 1, v_toPure_1380_);
lean_closure_set(v___f_1393_, 2, v_declName_1390_);
lean_closure_set(v___f_1393_, 3, v_modifyEnv_1382_);
lean_closure_set(v___f_1393_, 4, v___f_1392_);
lean_closure_set(v___f_1393_, 5, v_toBind_1383_);
lean_closure_set(v___f_1393_, 6, v___f_1391_);
v___x_1394_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(v_inst_1384_, v_inst_1385_, v_inst_1386_, v_inst_1387_, v_inst_1388_, v_declName_1390_);
v___x_1395_ = lean_apply_4(v_toBind_1383_, lean_box(0), lean_box(0), v___x_1394_, v___f_1393_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4(lean_object* v_declName_1396_, lean_object* v___f_1397_, lean_object* v_____do__lift_1398_){
_start:
{
lean_object* v_declName_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_declName_1399_ = l_Lean_mkPrivateName(v_____do__lift_1398_, v_declName_1396_);
v___x_1400_ = lean_box(0);
v___x_1401_ = lean_apply_2(v___f_1397_, v___x_1400_, v_declName_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__4___boxed(lean_object* v_declName_1402_, lean_object* v___f_1403_, lean_object* v_____do__lift_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_Elab_applyVisibility___redArg___lam__4(v_declName_1402_, v___f_1403_, v_____do__lift_1404_);
lean_dec_ref(v_____do__lift_1404_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5(lean_object* v_modifiers_1406_, lean_object* v_toBind_1407_, lean_object* v_getEnv_1408_, lean_object* v___f_1409_, lean_object* v___f_1410_, lean_object* v_declName_1411_, lean_object* v_____do__lift_1412_){
_start:
{
uint8_t v_visibility_1413_; uint8_t v___x_1414_; 
v_visibility_1413_ = lean_ctor_get_uint8(v_modifiers_1406_, sizeof(void*)*3);
v___x_1414_ = l_Lean_Elab_Visibility_isInferredPublic(v_____do__lift_1412_, v_visibility_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; 
lean_dec(v_declName_1411_);
lean_dec(v___f_1410_);
v___x_1415_ = lean_apply_4(v_toBind_1407_, lean_box(0), lean_box(0), v_getEnv_1408_, v___f_1409_);
return v___x_1415_;
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_dec(v___f_1409_);
lean_dec(v_getEnv_1408_);
lean_dec(v_toBind_1407_);
v___x_1416_ = lean_box(0);
v___x_1417_ = lean_apply_2(v___f_1410_, v___x_1416_, v_declName_1411_);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg___lam__5___boxed(lean_object* v_modifiers_1418_, lean_object* v_toBind_1419_, lean_object* v_getEnv_1420_, lean_object* v___f_1421_, lean_object* v___f_1422_, lean_object* v_declName_1423_, lean_object* v_____do__lift_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Elab_applyVisibility___redArg___lam__5(v_modifiers_1418_, v_toBind_1419_, v_getEnv_1420_, v___f_1421_, v___f_1422_, v_declName_1423_, v_____do__lift_1424_);
lean_dec_ref(v_____do__lift_1424_);
lean_dec_ref(v_modifiers_1418_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___redArg(lean_object* v_inst_1426_, lean_object* v_inst_1427_, lean_object* v_inst_1428_, lean_object* v_inst_1429_, lean_object* v_inst_1430_, lean_object* v_modifiers_1431_, lean_object* v_declName_1432_){
_start:
{
lean_object* v_toApplicative_1433_; lean_object* v_toBind_1434_; lean_object* v_getEnv_1435_; lean_object* v_modifyEnv_1436_; lean_object* v_toPure_1437_; lean_object* v___f_1438_; lean_object* v___f_1439_; lean_object* v___f_1440_; lean_object* v___x_1441_; 
v_toApplicative_1433_ = lean_ctor_get(v_inst_1426_, 0);
v_toBind_1434_ = lean_ctor_get(v_inst_1426_, 1);
lean_inc(v_toBind_1434_);
v_getEnv_1435_ = lean_ctor_get(v_inst_1427_, 0);
lean_inc(v_getEnv_1435_);
v_modifyEnv_1436_ = lean_ctor_get(v_inst_1427_, 1);
lean_inc(v_modifyEnv_1436_);
v_toPure_1437_ = lean_ctor_get(v_toApplicative_1433_, 1);
lean_inc(v_toPure_1437_);
lean_inc(v_toBind_1434_);
lean_inc_ref(v_modifiers_1431_);
v___f_1438_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__3), 11, 9);
lean_closure_set(v___f_1438_, 0, v_toPure_1437_);
lean_closure_set(v___f_1438_, 1, v_modifiers_1431_);
lean_closure_set(v___f_1438_, 2, v_modifyEnv_1436_);
lean_closure_set(v___f_1438_, 3, v_toBind_1434_);
lean_closure_set(v___f_1438_, 4, v_inst_1426_);
lean_closure_set(v___f_1438_, 5, v_inst_1427_);
lean_closure_set(v___f_1438_, 6, v_inst_1428_);
lean_closure_set(v___f_1438_, 7, v_inst_1429_);
lean_closure_set(v___f_1438_, 8, v_inst_1430_);
lean_inc_ref(v___f_1438_);
lean_inc(v_declName_1432_);
v___f_1439_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_1439_, 0, v_declName_1432_);
lean_closure_set(v___f_1439_, 1, v___f_1438_);
lean_inc(v_getEnv_1435_);
lean_inc(v_toBind_1434_);
v___f_1440_ = lean_alloc_closure((void*)(l_Lean_Elab_applyVisibility___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1440_, 0, v_modifiers_1431_);
lean_closure_set(v___f_1440_, 1, v_toBind_1434_);
lean_closure_set(v___f_1440_, 2, v_getEnv_1435_);
lean_closure_set(v___f_1440_, 3, v___f_1439_);
lean_closure_set(v___f_1440_, 4, v___f_1438_);
lean_closure_set(v___f_1440_, 5, v_declName_1432_);
v___x_1441_ = lean_apply_4(v_toBind_1434_, lean_box(0), lean_box(0), v_getEnv_1435_, v___f_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility(lean_object* v_m_1442_, lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_inst_1445_, lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_modifiers_1448_, lean_object* v_declName_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1443_, v_inst_1444_, v_inst_1445_, v_inst_1446_, v_inst_1447_, v_modifiers_1448_, v_declName_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0(lean_object* v_toPure_1451_, lean_object* v_____s_1452_){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_box(0);
v___x_1454_ = lean_apply_2(v_toPure_1451_, lean_box(0), v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1(lean_object* v___x_1455_, lean_object* v_toPure_1456_, lean_object* v_r_1457_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1455_);
v___x_1459_ = lean_apply_2(v_toPure_1456_, lean_box(0), v___x_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0));
v___x_1462_ = l_Lean_stringToMessageData(v___x_1461_);
return v___x_1462_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2));
v___x_1465_ = l_Lean_stringToMessageData(v___x_1464_);
return v___x_1465_;
}
}
static lean_object* _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = ((lean_object*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4));
v___x_1468_ = l_Lean_stringToMessageData(v___x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2(lean_object* v_pre_1469_, lean_object* v_declName_1470_, lean_object* v___x_1471_, lean_object* v_toPure_1472_, lean_object* v_inst_1473_, lean_object* v_inst_1474_, lean_object* v_toBind_1475_, lean_object* v___f_1476_, lean_object* v_a_1477_, lean_object* v_x_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1480_; uint8_t v___x_1481_; 
lean_inc(v_a_1477_);
lean_inc(v_pre_1469_);
v___x_1480_ = l_Lean_Name_append(v_pre_1469_, v_a_1477_);
v___x_1481_ = lean_name_eq(v___x_1480_, v_declName_1470_);
lean_dec(v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec(v_a_1477_);
lean_dec(v___f_1476_);
lean_dec(v_toBind_1475_);
lean_dec_ref(v_inst_1474_);
lean_dec_ref(v_inst_1473_);
lean_dec(v_declName_1470_);
lean_dec(v_pre_1469_);
v___x_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1471_);
v___x_1483_ = lean_apply_2(v_toPure_1472_, lean_box(0), v___x_1482_);
return v___x_1483_;
}
else
{
lean_object* v___x_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec(v_toPure_1472_);
v___x_1484_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1485_ = 0;
v___x_1486_ = l_Lean_MessageData_ofConstName(v_declName_1470_, v___x_1485_);
v___x_1487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1484_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = l_Lean_MessageData_ofName(v_pre_1469_);
v___x_1491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_1493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1491_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = l_Lean_MessageData_ofName(v_a_1477_);
v___x_1495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1493_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1495_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = l_Lean_throwError___redArg(v_inst_1473_, v_inst_1474_, v___x_1497_);
v___x_1499_ = lean_apply_4(v_toBind_1475_, lean_box(0), lean_box(0), v___x_1498_, v___f_1476_);
return v___x_1499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(lean_object* v_pre_1500_, uint8_t v___x_1501_, lean_object* v_toPure_1502_, lean_object* v_declName_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_toBind_1506_, lean_object* v___f_1507_, lean_object* v_____do__lift_1508_){
_start:
{
lean_object* v_fieldNames_1509_; lean_object* v___x_1510_; lean_object* v___f_1511_; lean_object* v___f_1512_; size_t v_sz_1513_; size_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_inc(v_pre_1500_);
v_fieldNames_1509_ = l_Lean_getStructureFieldsFlattened(v_____do__lift_1508_, v_pre_1500_, v___x_1501_);
v___x_1510_ = lean_box(0);
lean_inc(v_toPure_1502_);
v___f_1511_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1511_, 0, v___x_1510_);
lean_closure_set(v___f_1511_, 1, v_toPure_1502_);
lean_inc(v_toBind_1506_);
lean_inc_ref(v_inst_1504_);
v___f_1512_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2), 11, 8);
lean_closure_set(v___f_1512_, 0, v_pre_1500_);
lean_closure_set(v___f_1512_, 1, v_declName_1503_);
lean_closure_set(v___f_1512_, 2, v___x_1510_);
lean_closure_set(v___f_1512_, 3, v_toPure_1502_);
lean_closure_set(v___f_1512_, 4, v_inst_1504_);
lean_closure_set(v___f_1512_, 5, v_inst_1505_);
lean_closure_set(v___f_1512_, 6, v_toBind_1506_);
lean_closure_set(v___f_1512_, 7, v___f_1511_);
v_sz_1513_ = lean_array_size(v_fieldNames_1509_);
v___x_1514_ = ((size_t)0ULL);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1504_, v_fieldNames_1509_, v___f_1512_, v_sz_1513_, v___x_1514_, v___x_1510_);
v___x_1516_ = lean_apply_4(v_toBind_1506_, lean_box(0), lean_box(0), v___x_1515_, v___f_1507_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed(lean_object* v_pre_1517_, lean_object* v___x_1518_, lean_object* v_toPure_1519_, lean_object* v_declName_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_toBind_1523_, lean_object* v___f_1524_, lean_object* v_____do__lift_1525_){
_start:
{
uint8_t v___x_671__boxed_1526_; lean_object* v_res_1527_; 
v___x_671__boxed_1526_ = lean_unbox(v___x_1518_);
v_res_1527_ = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(v_pre_1517_, v___x_671__boxed_1526_, v_toPure_1519_, v_declName_1520_, v_inst_1521_, v_inst_1522_, v_toBind_1523_, v___f_1524_, v_____do__lift_1525_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4(lean_object* v_pre_1528_, lean_object* v_toPure_1529_, lean_object* v_declName_1530_, lean_object* v_inst_1531_, lean_object* v_inst_1532_, lean_object* v_toBind_1533_, lean_object* v___f_1534_, lean_object* v_getEnv_1535_, lean_object* v_____do__lift_1536_){
_start:
{
uint8_t v___x_1537_; 
lean_inc(v_pre_1528_);
v___x_1537_ = l_Lean_isStructure(v_____do__lift_1536_, v_pre_1528_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_dec(v_getEnv_1535_);
lean_dec(v___f_1534_);
lean_dec(v_toBind_1533_);
lean_dec_ref(v_inst_1532_);
lean_dec_ref(v_inst_1531_);
lean_dec(v_declName_1530_);
lean_dec(v_pre_1528_);
v___x_1538_ = lean_box(0);
v___x_1539_ = lean_apply_2(v_toPure_1529_, lean_box(0), v___x_1538_);
return v___x_1539_;
}
else
{
lean_object* v___x_1540_; lean_object* v___f_1541_; lean_object* v___x_1542_; 
v___x_1540_ = lean_box(v___x_1537_);
lean_inc(v_toBind_1533_);
v___f_1541_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1541_, 0, v_pre_1528_);
lean_closure_set(v___f_1541_, 1, v___x_1540_);
lean_closure_set(v___f_1541_, 2, v_toPure_1529_);
lean_closure_set(v___f_1541_, 3, v_declName_1530_);
lean_closure_set(v___f_1541_, 4, v_inst_1531_);
lean_closure_set(v___f_1541_, 5, v_inst_1532_);
lean_closure_set(v___f_1541_, 6, v_toBind_1533_);
lean_closure_set(v___f_1541_, 7, v___f_1534_);
v___x_1542_ = lean_apply_4(v_toBind_1533_, lean_box(0), lean_box(0), v_getEnv_1535_, v___f_1541_);
return v___x_1542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___redArg(lean_object* v_inst_1543_, lean_object* v_inst_1544_, lean_object* v_inst_1545_, lean_object* v_declName_1546_){
_start:
{
if (lean_obj_tag(v_declName_1546_) == 1)
{
lean_object* v_toApplicative_1547_; lean_object* v_toBind_1548_; lean_object* v_toPure_1549_; lean_object* v_pre_1550_; lean_object* v_getEnv_1551_; lean_object* v___f_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; 
v_toApplicative_1547_ = lean_ctor_get(v_inst_1543_, 0);
v_toBind_1548_ = lean_ctor_get(v_inst_1543_, 1);
lean_inc(v_toBind_1548_);
v_toPure_1549_ = lean_ctor_get(v_toApplicative_1547_, 1);
lean_inc(v_toPure_1549_);
v_pre_1550_ = lean_ctor_get(v_declName_1546_, 0);
lean_inc(v_pre_1550_);
v_getEnv_1551_ = lean_ctor_get(v_inst_1544_, 0);
lean_inc(v_getEnv_1551_);
lean_dec_ref(v_inst_1544_);
lean_inc(v_toPure_1549_);
v___f_1552_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1552_, 0, v_toPure_1549_);
lean_inc(v_getEnv_1551_);
lean_inc(v_toBind_1548_);
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1553_, 0, v_pre_1550_);
lean_closure_set(v___f_1553_, 1, v_toPure_1549_);
lean_closure_set(v___f_1553_, 2, v_declName_1546_);
lean_closure_set(v___f_1553_, 3, v_inst_1543_);
lean_closure_set(v___f_1553_, 4, v_inst_1545_);
lean_closure_set(v___f_1553_, 5, v_toBind_1548_);
lean_closure_set(v___f_1553_, 6, v___f_1552_);
lean_closure_set(v___f_1553_, 7, v_getEnv_1551_);
v___x_1554_ = lean_apply_4(v_toBind_1548_, lean_box(0), lean_box(0), v_getEnv_1551_, v___f_1553_);
return v___x_1554_;
}
else
{
lean_object* v_toApplicative_1555_; lean_object* v_toPure_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_toApplicative_1555_ = lean_ctor_get(v_inst_1543_, 0);
lean_inc_ref(v_toApplicative_1555_);
lean_dec(v_declName_1546_);
lean_dec_ref(v_inst_1545_);
lean_dec_ref(v_inst_1544_);
lean_dec_ref(v_inst_1543_);
v_toPure_1556_ = lean_ctor_get(v_toApplicative_1555_, 1);
lean_inc(v_toPure_1556_);
lean_dec_ref(v_toApplicative_1555_);
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_apply_2(v_toPure_1556_, lean_box(0), v___x_1557_);
return v___x_1558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField(lean_object* v_m_1559_, lean_object* v_inst_1560_, lean_object* v_inst_1561_, lean_object* v_inst_1562_, lean_object* v_declName_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1560_, v_inst_1561_, v_inst_1562_, v_declName_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__0(lean_object* v_toApplicative_1565_, lean_object* v_declName_1566_, lean_object* v_shortName_1567_, lean_object* v_____r_1568_){
_start:
{
lean_object* v_toPure_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_toPure_1569_ = lean_ctor_get(v_toApplicative_1565_, 1);
lean_inc(v_toPure_1569_);
lean_dec_ref(v_toApplicative_1565_);
v___x_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1570_, 0, v_declName_1566_);
lean_ctor_set(v___x_1570_, 1, v_shortName_1567_);
v___x_1571_ = lean_apply_2(v_toPure_1569_, lean_box(0), v___x_1570_);
return v___x_1571_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0));
v___x_1574_ = l_Lean_stringToMessageData(v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2(lean_object* v_modifiers_1575_, lean_object* v_toApplicative_1576_, lean_object* v_shortName_1577_, lean_object* v_currNamespace_1578_, lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_toBind_1581_, lean_object* v_declName_1582_){
_start:
{
uint8_t v_isProtected_1583_; 
v_isProtected_1583_ = lean_ctor_get_uint8(v_modifiers_1575_, sizeof(void*)*3 + 1);
if (v_isProtected_1583_ == 0)
{
lean_object* v_toPure_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec(v_toBind_1581_);
lean_dec_ref(v_inst_1580_);
lean_dec_ref(v_inst_1579_);
lean_dec(v_currNamespace_1578_);
v_toPure_1584_ = lean_ctor_get(v_toApplicative_1576_, 1);
lean_inc(v_toPure_1584_);
lean_dec_ref(v_toApplicative_1576_);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v_declName_1582_);
lean_ctor_set(v___x_1585_, 1, v_shortName_1577_);
v___x_1586_ = lean_apply_2(v_toPure_1584_, lean_box(0), v___x_1585_);
return v___x_1586_;
}
else
{
if (lean_obj_tag(v_currNamespace_1578_) == 1)
{
lean_object* v_str_1587_; lean_object* v_toPure_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec(v_toBind_1581_);
lean_dec_ref(v_inst_1580_);
lean_dec_ref(v_inst_1579_);
v_str_1587_ = lean_ctor_get(v_currNamespace_1578_, 1);
lean_inc_ref(v_str_1587_);
lean_dec_ref(v_currNamespace_1578_);
v_toPure_1588_ = lean_ctor_get(v_toApplicative_1576_, 1);
lean_inc(v_toPure_1588_);
lean_dec_ref(v_toApplicative_1576_);
v___x_1589_ = lean_box(0);
v___x_1590_ = l_Lean_Name_str___override(v___x_1589_, v_str_1587_);
v___x_1591_ = l_Lean_Name_append(v___x_1590_, v_shortName_1577_);
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v_declName_1582_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = lean_apply_2(v_toPure_1588_, lean_box(0), v___x_1592_);
return v___x_1593_;
}
else
{
lean_object* v___f_1594_; uint8_t v___x_1595_; 
lean_dec(v_currNamespace_1578_);
lean_inc(v_shortName_1577_);
lean_inc(v_declName_1582_);
lean_inc_ref(v_toApplicative_1576_);
v___f_1594_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1594_, 0, v_toApplicative_1576_);
lean_closure_set(v___f_1594_, 1, v_declName_1582_);
lean_closure_set(v___f_1594_, 2, v_shortName_1577_);
v___x_1595_ = l_Lean_Name_isAtomic(v_shortName_1577_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec_ref(v___f_1594_);
lean_dec(v_toBind_1581_);
lean_dec_ref(v_inst_1580_);
lean_dec_ref(v_inst_1579_);
v___x_1596_ = lean_box(0);
v___x_1597_ = l_Lean_Elab_mkDeclName___redArg___lam__0(v_toApplicative_1576_, v_declName_1582_, v_shortName_1577_, v___x_1596_);
return v___x_1597_;
}
else
{
lean_object* v___f_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec(v_declName_1582_);
lean_dec(v_shortName_1577_);
lean_dec_ref(v_toApplicative_1576_);
v___f_1598_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1598_, 0, v___f_1594_);
v___x_1599_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_1600_ = l_Lean_throwError___redArg(v_inst_1579_, v_inst_1580_, v___x_1599_);
v___x_1601_ = lean_apply_4(v_toBind_1581_, lean_box(0), lean_box(0), v___x_1600_, v___f_1598_);
return v___x_1601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__2___boxed(lean_object* v_modifiers_1602_, lean_object* v_toApplicative_1603_, lean_object* v_shortName_1604_, lean_object* v_currNamespace_1605_, lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v_toBind_1608_, lean_object* v_declName_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Elab_mkDeclName___redArg___lam__2(v_modifiers_1602_, v_toApplicative_1603_, v_shortName_1604_, v_currNamespace_1605_, v_inst_1606_, v_inst_1607_, v_toBind_1608_, v_declName_1609_);
lean_dec_ref(v_modifiers_1602_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__1(lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_inst_1614_, lean_object* v_inst_1615_, lean_object* v_modifiers_1616_, lean_object* v___y_1617_, lean_object* v_toBind_1618_, lean_object* v___f_1619_, lean_object* v_____r_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = l_Lean_Elab_applyVisibility___redArg(v_inst_1611_, v_inst_1612_, v_inst_1613_, v_inst_1614_, v_inst_1615_, v_modifiers_1616_, v___y_1617_);
v___x_1622_ = lean_apply_4(v_toBind_1618_, lean_box(0), lean_box(0), v___x_1621_, v___f_1619_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__3(lean_object* v_modifiers_1623_, lean_object* v_toApplicative_1624_, lean_object* v_inst_1625_, lean_object* v_inst_1626_, lean_object* v_toBind_1627_, lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v___y_1631_, lean_object* v_____r_1632_, lean_object* v_shortName_1633_, lean_object* v_currNamespace_1634_){
_start:
{
lean_object* v___f_1635_; lean_object* v___f_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_inc(v_toBind_1627_);
lean_inc_ref(v_inst_1626_);
lean_inc_ref(v_inst_1625_);
lean_inc_ref(v_modifiers_1623_);
v___f_1635_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1635_, 0, v_modifiers_1623_);
lean_closure_set(v___f_1635_, 1, v_toApplicative_1624_);
lean_closure_set(v___f_1635_, 2, v_shortName_1633_);
lean_closure_set(v___f_1635_, 3, v_currNamespace_1634_);
lean_closure_set(v___f_1635_, 4, v_inst_1625_);
lean_closure_set(v___f_1635_, 5, v_inst_1626_);
lean_closure_set(v___f_1635_, 6, v_toBind_1627_);
lean_inc(v_toBind_1627_);
lean_inc(v___y_1631_);
lean_inc_ref(v_inst_1626_);
lean_inc_ref(v_inst_1628_);
lean_inc_ref(v_inst_1625_);
v___f_1636_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1636_, 0, v_inst_1625_);
lean_closure_set(v___f_1636_, 1, v_inst_1628_);
lean_closure_set(v___f_1636_, 2, v_inst_1626_);
lean_closure_set(v___f_1636_, 3, v_inst_1629_);
lean_closure_set(v___f_1636_, 4, v_inst_1630_);
lean_closure_set(v___f_1636_, 5, v_modifiers_1623_);
lean_closure_set(v___f_1636_, 6, v___y_1631_);
lean_closure_set(v___f_1636_, 7, v_toBind_1627_);
lean_closure_set(v___f_1636_, 8, v___f_1635_);
v___x_1637_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(v_inst_1625_, v_inst_1628_, v_inst_1626_, v___y_1631_);
v___x_1638_ = lean_apply_4(v_toBind_1627_, lean_box(0), lean_box(0), v___x_1637_, v___f_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__4(lean_object* v___f_1639_, lean_object* v_shortName_1640_, lean_object* v_currNamespace_1641_, lean_object* v_____r_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_apply_3(v___f_1639_, v_____r_1642_, v_shortName_1640_, v_currNamespace_1641_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5(lean_object* v_modifiers_1644_, lean_object* v_toApplicative_1645_, lean_object* v_inst_1646_, lean_object* v_inst_1647_, lean_object* v_toBind_1648_, lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_inst_1651_, uint8_t v_isRootName_1652_, lean_object* v_shortName_1653_, lean_object* v_currNamespace_1654_, lean_object* v_name_1655_, lean_object* v___x_1656_, lean_object* v_imported_1657_, lean_object* v_ctx_1658_, lean_object* v_scopes_1659_, lean_object* v_____r_1660_){
_start:
{
lean_object* v___y_1662_; 
if (v_isRootName_1652_ == 0)
{
lean_object* v___x_1681_; 
lean_dec(v_scopes_1659_);
lean_dec(v_ctx_1658_);
lean_dec(v_imported_1657_);
lean_inc(v_shortName_1653_);
lean_inc(v_currNamespace_1654_);
v___x_1681_ = l_Lean_Name_append(v_currNamespace_1654_, v_shortName_1653_);
v___y_1662_ = v___x_1681_;
goto v___jp_1661_;
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1682_ = lean_box(0);
lean_inc(v_name_1655_);
v___x_1683_ = l_Lean_Name_replacePrefix(v_name_1655_, v___x_1656_, v___x_1682_);
v___x_1684_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
lean_ctor_set(v___x_1684_, 1, v_imported_1657_);
lean_ctor_set(v___x_1684_, 2, v_ctx_1658_);
lean_ctor_set(v___x_1684_, 3, v_scopes_1659_);
v___x_1685_ = l_Lean_MacroScopesView_review(v___x_1684_);
v___y_1662_ = v___x_1685_;
goto v___jp_1661_;
}
v___jp_1661_:
{
lean_object* v___f_1663_; 
lean_inc(v___y_1662_);
lean_inc_ref(v_inst_1651_);
lean_inc(v_inst_1650_);
lean_inc_ref(v_inst_1649_);
lean_inc(v_toBind_1648_);
lean_inc_ref(v_inst_1647_);
lean_inc_ref(v_inst_1646_);
lean_inc_ref(v_toApplicative_1645_);
lean_inc_ref(v_modifiers_1644_);
v___f_1663_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__3), 12, 9);
lean_closure_set(v___f_1663_, 0, v_modifiers_1644_);
lean_closure_set(v___f_1663_, 1, v_toApplicative_1645_);
lean_closure_set(v___f_1663_, 2, v_inst_1646_);
lean_closure_set(v___f_1663_, 3, v_inst_1647_);
lean_closure_set(v___f_1663_, 4, v_toBind_1648_);
lean_closure_set(v___f_1663_, 5, v_inst_1649_);
lean_closure_set(v___f_1663_, 6, v_inst_1650_);
lean_closure_set(v___f_1663_, 7, v_inst_1651_);
lean_closure_set(v___f_1663_, 8, v___y_1662_);
if (v_isRootName_1652_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec_ref(v___f_1663_);
lean_dec(v_name_1655_);
v___x_1664_ = lean_box(0);
v___x_1665_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1644_, v_toApplicative_1645_, v_inst_1646_, v_inst_1647_, v_toBind_1648_, v_inst_1649_, v_inst_1650_, v_inst_1651_, v___y_1662_, v___x_1664_, v_shortName_1653_, v_currNamespace_1654_);
return v___x_1665_;
}
else
{
if (lean_obj_tag(v_name_1655_) == 1)
{
lean_object* v_pre_1666_; lean_object* v_str_1667_; lean_object* v___x_1668_; lean_object* v_shortName_1669_; lean_object* v_currNamespace_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_dec_ref(v___f_1663_);
lean_dec(v_currNamespace_1654_);
lean_dec(v_shortName_1653_);
v_pre_1666_ = lean_ctor_get(v_name_1655_, 0);
lean_inc(v_pre_1666_);
v_str_1667_ = lean_ctor_get(v_name_1655_, 1);
lean_inc_ref(v_str_1667_);
lean_dec_ref(v_name_1655_);
v___x_1668_ = lean_box(0);
v_shortName_1669_ = l_Lean_Name_str___override(v___x_1668_, v_str_1667_);
v_currNamespace_1670_ = l_Lean_Name_replacePrefix(v_pre_1666_, v___x_1656_, v___x_1668_);
v___x_1671_ = lean_box(0);
v___x_1672_ = l_Lean_Elab_mkDeclName___redArg___lam__3(v_modifiers_1644_, v_toApplicative_1645_, v_inst_1646_, v_inst_1647_, v_toBind_1648_, v_inst_1649_, v_inst_1650_, v_inst_1651_, v___y_1662_, v___x_1671_, v_shortName_1669_, v_currNamespace_1670_);
return v___x_1672_;
}
else
{
lean_object* v___f_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec(v___y_1662_);
lean_dec_ref(v_inst_1651_);
lean_dec(v_inst_1650_);
lean_dec_ref(v_inst_1649_);
lean_dec_ref(v_toApplicative_1645_);
lean_dec_ref(v_modifiers_1644_);
v___f_1673_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__4), 4, 3);
lean_closure_set(v___f_1673_, 0, v___f_1663_);
lean_closure_set(v___f_1673_, 1, v_shortName_1653_);
lean_closure_set(v___f_1673_, 2, v_currNamespace_1654_);
v___x_1674_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_1675_ = l_Lean_MessageData_ofName(v_name_1655_);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1676_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = l_Lean_throwError___redArg(v_inst_1646_, v_inst_1647_, v___x_1678_);
v___x_1680_ = lean_apply_4(v_toBind_1648_, lean_box(0), lean_box(0), v___x_1679_, v___f_1673_);
return v___x_1680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_modifiers_1686_ = _args[0];
lean_object* v_toApplicative_1687_ = _args[1];
lean_object* v_inst_1688_ = _args[2];
lean_object* v_inst_1689_ = _args[3];
lean_object* v_toBind_1690_ = _args[4];
lean_object* v_inst_1691_ = _args[5];
lean_object* v_inst_1692_ = _args[6];
lean_object* v_inst_1693_ = _args[7];
lean_object* v_isRootName_1694_ = _args[8];
lean_object* v_shortName_1695_ = _args[9];
lean_object* v_currNamespace_1696_ = _args[10];
lean_object* v_name_1697_ = _args[11];
lean_object* v___x_1698_ = _args[12];
lean_object* v_imported_1699_ = _args[13];
lean_object* v_ctx_1700_ = _args[14];
lean_object* v_scopes_1701_ = _args[15];
lean_object* v_____r_1702_ = _args[16];
_start:
{
uint8_t v_isRootName_boxed_1703_; lean_object* v_res_1704_; 
v_isRootName_boxed_1703_ = lean_unbox(v_isRootName_1694_);
v_res_1704_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1686_, v_toApplicative_1687_, v_inst_1688_, v_inst_1689_, v_toBind_1690_, v_inst_1691_, v_inst_1692_, v_inst_1693_, v_isRootName_boxed_1703_, v_shortName_1695_, v_currNamespace_1696_, v_name_1697_, v___x_1698_, v_imported_1699_, v_ctx_1700_, v_scopes_1701_, v_____r_1702_);
lean_dec(v___x_1698_);
return v_res_1704_;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___redArg___closed__3(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__2));
v___x_1710_ = l_Lean_stringToMessageData(v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___redArg(lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_inst_1715_, lean_object* v_currNamespace_1716_, lean_object* v_modifiers_1717_, lean_object* v_shortName_1718_){
_start:
{
lean_object* v_view_1719_; lean_object* v_name_1720_; lean_object* v_imported_1721_; lean_object* v_ctx_1722_; lean_object* v_scopes_1723_; lean_object* v_toApplicative_1724_; lean_object* v_toBind_1725_; lean_object* v___x_1726_; uint8_t v_isRootName_1727_; lean_object* v___x_1728_; lean_object* v___f_1729_; uint8_t v___x_1730_; 
lean_inc(v_shortName_1718_);
v_view_1719_ = l_Lean_extractMacroScopes(v_shortName_1718_);
v_name_1720_ = lean_ctor_get(v_view_1719_, 0);
lean_inc(v_name_1720_);
v_imported_1721_ = lean_ctor_get(v_view_1719_, 1);
lean_inc(v_imported_1721_);
v_ctx_1722_ = lean_ctor_get(v_view_1719_, 2);
lean_inc(v_ctx_1722_);
v_scopes_1723_ = lean_ctor_get(v_view_1719_, 3);
lean_inc(v_scopes_1723_);
lean_dec_ref(v_view_1719_);
v_toApplicative_1724_ = lean_ctor_get(v_inst_1711_, 0);
v_toBind_1725_ = lean_ctor_get(v_inst_1711_, 1);
lean_inc(v_toBind_1725_);
v___x_1726_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_1727_ = l_Lean_Name_isPrefixOf(v___x_1726_, v_name_1720_);
v___x_1728_ = lean_box(v_isRootName_1727_);
lean_inc(v_scopes_1723_);
lean_inc(v_ctx_1722_);
lean_inc(v_imported_1721_);
lean_inc(v_name_1720_);
lean_inc(v_currNamespace_1716_);
lean_inc(v_shortName_1718_);
lean_inc_ref(v_inst_1715_);
lean_inc(v_inst_1714_);
lean_inc_ref(v_inst_1712_);
lean_inc(v_toBind_1725_);
lean_inc_ref(v_inst_1713_);
lean_inc_ref(v_inst_1711_);
lean_inc_ref(v_toApplicative_1724_);
lean_inc_ref(v_modifiers_1717_);
v___f_1729_ = lean_alloc_closure((void*)(l_Lean_Elab_mkDeclName___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1729_, 0, v_modifiers_1717_);
lean_closure_set(v___f_1729_, 1, v_toApplicative_1724_);
lean_closure_set(v___f_1729_, 2, v_inst_1711_);
lean_closure_set(v___f_1729_, 3, v_inst_1713_);
lean_closure_set(v___f_1729_, 4, v_toBind_1725_);
lean_closure_set(v___f_1729_, 5, v_inst_1712_);
lean_closure_set(v___f_1729_, 6, v_inst_1714_);
lean_closure_set(v___f_1729_, 7, v_inst_1715_);
lean_closure_set(v___f_1729_, 8, v___x_1728_);
lean_closure_set(v___f_1729_, 9, v_shortName_1718_);
lean_closure_set(v___f_1729_, 10, v_currNamespace_1716_);
lean_closure_set(v___f_1729_, 11, v_name_1720_);
lean_closure_set(v___f_1729_, 12, v___x_1726_);
lean_closure_set(v___f_1729_, 13, v_imported_1721_);
lean_closure_set(v___f_1729_, 14, v_ctx_1722_);
lean_closure_set(v___f_1729_, 15, v_scopes_1723_);
v___x_1730_ = lean_name_eq(v_name_1720_, v___x_1726_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_inc_ref(v_toApplicative_1724_);
lean_dec_ref(v___f_1729_);
v___x_1731_ = lean_box(0);
v___x_1732_ = l_Lean_Elab_mkDeclName___redArg___lam__5(v_modifiers_1717_, v_toApplicative_1724_, v_inst_1711_, v_inst_1713_, v_toBind_1725_, v_inst_1712_, v_inst_1714_, v_inst_1715_, v_isRootName_1727_, v_shortName_1718_, v_currNamespace_1716_, v_name_1720_, v___x_1726_, v_imported_1721_, v_ctx_1722_, v_scopes_1723_, v___x_1731_);
return v___x_1732_;
}
else
{
lean_object* v___f_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
lean_dec(v_scopes_1723_);
lean_dec(v_ctx_1722_);
lean_dec(v_imported_1721_);
lean_dec(v_name_1720_);
lean_dec(v_shortName_1718_);
lean_dec_ref(v_modifiers_1717_);
lean_dec(v_currNamespace_1716_);
lean_dec_ref(v_inst_1715_);
lean_dec(v_inst_1714_);
lean_dec_ref(v_inst_1712_);
v___f_1733_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1733_, 0, v___f_1729_);
v___x_1734_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_1735_ = l_Lean_throwError___redArg(v_inst_1711_, v_inst_1713_, v___x_1734_);
v___x_1736_ = lean_apply_4(v_toBind_1725_, lean_box(0), lean_box(0), v___x_1735_, v___f_1733_);
return v___x_1736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName(lean_object* v_m_1737_, lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_currNamespace_1743_, lean_object* v_modifiers_1744_, lean_object* v_shortName_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Elab_mkDeclName___redArg(v_inst_1738_, v_inst_1739_, v_inst_1740_, v_inst_1741_, v_inst_1742_, v_currNamespace_1743_, v_modifiers_1744_, v_shortName_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore(lean_object* v_declId_1756_){
_start:
{
uint8_t v___x_1757_; 
v___x_1757_ = l_Lean_Syntax_isIdent(v_declId_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v_id_1760_; lean_object* v___x_1761_; lean_object* v_optUnivDeclStx_1762_; lean_object* v___x_1763_; 
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = l_Lean_Syntax_getArg(v_declId_1756_, v___x_1758_);
v_id_1760_ = l_Lean_Syntax_getId(v___x_1759_);
lean_dec(v___x_1759_);
v___x_1761_ = lean_unsigned_to_nat(1u);
v_optUnivDeclStx_1762_ = l_Lean_Syntax_getArg(v_declId_1756_, v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v_id_1760_);
lean_ctor_set(v___x_1763_, 1, v_optUnivDeclStx_1762_);
return v___x_1763_;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = l_Lean_Syntax_getId(v_declId_1756_);
v___x_1765_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__3));
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1764_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
return v___x_1766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclIdCore___boxed(lean_object* v_declId_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Elab_expandDeclIdCore(v_declId_1767_);
lean_dec(v_declId_1767_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(lean_object* v_msgData_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v___x_1775_; lean_object* v_env_1776_; lean_object* v___x_1777_; lean_object* v_mctx_1778_; lean_object* v_lctx_1779_; lean_object* v_options_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1775_ = lean_st_ref_get(v___y_1773_);
v_env_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc_ref(v_env_1776_);
lean_dec(v___x_1775_);
v___x_1777_ = lean_st_ref_get(v___y_1771_);
v_mctx_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc_ref(v_mctx_1778_);
lean_dec(v___x_1777_);
v_lctx_1779_ = lean_ctor_get(v___y_1770_, 2);
v_options_1780_ = lean_ctor_get(v___y_1772_, 2);
lean_inc_ref(v_options_1780_);
lean_inc_ref(v_lctx_1779_);
v___x_1781_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1781_, 0, v_env_1776_);
lean_ctor_set(v___x_1781_, 1, v_mctx_1778_);
lean_ctor_set(v___x_1781_, 2, v_lctx_1779_);
lean_ctor_set(v___x_1781_, 3, v_options_1780_);
v___x_1782_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v_msgData_1769_);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msgData_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
return v_res_1790_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(lean_object* v_opts_1791_, lean_object* v_opt_1792_){
_start:
{
lean_object* v_name_1793_; lean_object* v_defValue_1794_; lean_object* v_map_1795_; lean_object* v___x_1796_; 
v_name_1793_ = lean_ctor_get(v_opt_1792_, 0);
v_defValue_1794_ = lean_ctor_get(v_opt_1792_, 1);
v_map_1795_ = lean_ctor_get(v_opts_1791_, 0);
v___x_1796_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1795_, v_name_1793_);
if (lean_obj_tag(v___x_1796_) == 0)
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_unbox(v_defValue_1794_);
return v___x_1797_;
}
else
{
lean_object* v_val_1798_; 
v_val_1798_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_val_1798_);
lean_dec_ref(v___x_1796_);
if (lean_obj_tag(v_val_1798_) == 1)
{
uint8_t v_v_1799_; 
v_v_1799_ = lean_ctor_get_uint8(v_val_1798_, 0);
lean_dec_ref(v_val_1798_);
return v_v_1799_;
}
else
{
uint8_t v___x_1800_; 
lean_dec(v_val_1798_);
v___x_1800_ = lean_unbox(v_defValue_1794_);
return v___x_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_opts_1801_, lean_object* v_opt_1802_){
_start:
{
uint8_t v_res_1803_; lean_object* v_r_1804_; 
v_res_1803_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_opts_1801_, v_opt_1802_);
lean_dec_ref(v_opt_1802_);
lean_dec_ref(v_opts_1801_);
v_r_1804_ = lean_box(v_res_1803_);
return v_r_1804_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = lean_box(1);
v___x_1806_ = l_Lean_MessageData_ofFormat(v___x_1805_);
return v___x_1806_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2));
v___x_1811_ = l_Lean_MessageData_ofFormat(v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(lean_object* v_x_1812_, lean_object* v_x_1813_){
_start:
{
if (lean_obj_tag(v_x_1813_) == 0)
{
return v_x_1812_;
}
else
{
lean_object* v_head_1814_; lean_object* v_tail_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1837_; 
v_head_1814_ = lean_ctor_get(v_x_1813_, 0);
v_tail_1815_ = lean_ctor_get(v_x_1813_, 1);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_x_1813_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1817_ = v_x_1813_;
v_isShared_1818_ = v_isSharedCheck_1837_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_tail_1815_);
lean_inc(v_head_1814_);
lean_dec(v_x_1813_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1837_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v_before_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1835_; 
v_before_1819_ = lean_ctor_get(v_head_1814_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_head_1814_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; 
v_unused_1836_ = lean_ctor_get(v_head_1814_, 1);
lean_dec(v_unused_1836_);
v___x_1821_ = v_head_1814_;
v_isShared_1822_ = v_isSharedCheck_1835_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_before_1819_);
lean_dec(v_head_1814_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1835_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1823_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_1822_ == 0)
{
lean_ctor_set_tag(v___x_1821_, 7);
lean_ctor_set(v___x_1821_, 1, v___x_1823_);
lean_ctor_set(v___x_1821_, 0, v_x_1812_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_x_1812_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1826_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3);
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 7);
lean_ctor_set(v___x_1817_, 1, v___x_1826_);
lean_ctor_set(v___x_1817_, 0, v___x_1825_);
v___x_1828_ = v___x_1817_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = l_Lean_MessageData_ofSyntax(v_before_1819_);
v___x_1830_ = l_Lean_indentD(v___x_1829_);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1828_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v_x_1812_ = v___x_1831_;
v_x_1813_ = v_tail_1815_;
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
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1));
v___x_1842_ = l_Lean_MessageData_ofFormat(v___x_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_1843_, lean_object* v_macroStack_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_options_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v_options_1847_ = lean_ctor_get(v___y_1845_, 2);
v___x_1848_ = l_Lean_Elab_pp_macroStack;
v___x_1849_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_options_1847_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; 
lean_dec(v_macroStack_1844_);
v___x_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1850_, 0, v_msgData_1843_);
return v___x_1850_;
}
else
{
if (lean_obj_tag(v_macroStack_1844_) == 0)
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_msgData_1843_);
return v___x_1851_;
}
else
{
lean_object* v_head_1852_; lean_object* v_after_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1868_; 
v_head_1852_ = lean_ctor_get(v_macroStack_1844_, 0);
lean_inc(v_head_1852_);
v_after_1853_ = lean_ctor_get(v_head_1852_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_head_1852_);
if (v_isSharedCheck_1868_ == 0)
{
lean_object* v_unused_1869_; 
v_unused_1869_ = lean_ctor_get(v_head_1852_, 0);
lean_dec(v_unused_1869_);
v___x_1855_ = v_head_1852_;
v_isShared_1856_ = v_isSharedCheck_1868_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_after_1853_);
lean_dec(v_head_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1868_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1857_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
if (v_isShared_1856_ == 0)
{
lean_ctor_set_tag(v___x_1855_, 7);
lean_ctor_set(v___x_1855_, 1, v___x_1857_);
lean_ctor_set(v___x_1855_, 0, v_msgData_1843_);
v___x_1859_ = v___x_1855_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_msgData_1843_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v_msgData_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1860_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = l_Lean_MessageData_ofSyntax(v_after_1853_);
v___x_1863_ = l_Lean_indentD(v___x_1862_);
v_msgData_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1864_, 0, v___x_1861_);
lean_ctor_set(v_msgData_1864_, 1, v___x_1863_);
v___x_1865_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(v_msgData_1864_, v_macroStack_1844_);
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
return v___x_1866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_1870_, lean_object* v_macroStack_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_1870_, v_macroStack_1871_, v___y_1872_);
lean_dec_ref(v___y_1872_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(lean_object* v_msg_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_ref_1883_; lean_object* v___x_1884_; lean_object* v_a_1885_; lean_object* v_macroStack_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1897_; 
v_ref_1883_ = lean_ctor_get(v___y_1880_, 5);
v___x_1884_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msg_1875_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1884_);
v_macroStack_1886_ = lean_ctor_get(v___y_1876_, 1);
lean_inc(v_macroStack_1886_);
lean_dec_ref(v___y_1876_);
lean_inc(v_macroStack_1886_);
v___x_1887_ = l_Lean_Elab_getBetterRef(v_ref_1883_, v_macroStack_1886_);
v___x_1888_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_a_1885_, v_macroStack_1886_, v___y_1880_);
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1887_);
lean_ctor_set(v___x_1893_, 1, v_a_1889_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set_tag(v___x_1891_, 1);
lean_ctor_set(v___x_1891_, 0, v___x_1893_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(lean_object* v_env_1907_, lean_object* v_declName_1908_, lean_object* v___f_1909_, lean_object* v_addInfo_1910_, lean_object* v_____r_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v___x_1919_; uint8_t v___x_1920_; uint8_t v___x_1921_; 
lean_inc(v_declName_1908_);
v___x_1919_ = l_Lean_mkPrivateName(v_env_1907_, v_declName_1908_);
v___x_1920_ = 1;
lean_inc(v___x_1919_);
v___x_1921_ = l_Lean_Environment_contains(v_env_1907_, v___x_1919_, v___x_1920_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
lean_dec(v___x_1919_);
lean_dec_ref(v_addInfo_1910_);
lean_dec(v_declName_1908_);
v___x_1922_ = lean_box(0);
v___x_1923_ = lean_apply_8(v___f_1909_, v___x_1922_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, lean_box(0));
return v___x_1923_;
}
else
{
lean_object* v___x_1924_; 
lean_dec_ref(v___f_1909_);
lean_inc(v___y_1917_);
lean_inc_ref(v___y_1916_);
lean_inc(v___y_1915_);
lean_inc_ref(v___y_1914_);
lean_inc(v___y_1913_);
lean_inc_ref(v___y_1912_);
v___x_1924_ = lean_apply_8(v_addInfo_1910_, v___x_1919_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, lean_box(0));
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
lean_dec_ref(v___x_1924_);
v___x_1925_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1);
v___x_1926_ = l_Lean_MessageData_ofConstName(v_declName_1908_, v___x_1920_);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_1929_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
return v___x_1930_;
}
else
{
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v_declName_1908_);
return v___x_1924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed(lean_object* v_env_1931_, lean_object* v_declName_1932_, lean_object* v___f_1933_, lean_object* v_addInfo_1934_, lean_object* v_____r_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(v_env_1931_, v_declName_1932_, v___f_1933_, v_addInfo_1934_, v_____r_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(lean_object* v___f_1944_, lean_object* v_declName_1945_, uint8_t v___x_1946_, lean_object* v_env_1947_, lean_object* v_____do__lift_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
uint8_t v___y_1957_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
lean_inc(v_declName_1945_);
v___x_1966_ = l_Lean_privateToUserName(v_declName_1945_);
lean_inc_ref(v_env_1947_);
v___x_1967_ = lean_is_reserved_name(v_env_1947_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; uint8_t v___x_1969_; 
lean_inc(v_declName_1945_);
v___x_1968_ = l_Lean_mkPrivateName(v_____do__lift_1948_, v_declName_1945_);
v___x_1969_ = lean_is_reserved_name(v_env_1947_, v___x_1968_);
v___y_1957_ = v___x_1969_;
goto v___jp_1956_;
}
else
{
lean_dec_ref(v_env_1947_);
v___y_1957_ = v___x_1967_;
goto v___jp_1956_;
}
v___jp_1956_:
{
if (v___y_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_dec(v_declName_1945_);
v___x_1958_ = lean_box(0);
v___x_1959_ = lean_apply_8(v___f_1944_, v___x_1958_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, lean_box(0));
return v___x_1959_;
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_dec_ref(v___f_1944_);
v___x_1960_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_1961_ = l_Lean_MessageData_ofConstName(v_declName_1945_, v___x_1946_);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1960_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_1964_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
return v___x_1965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed(lean_object* v___f_1970_, lean_object* v_declName_1971_, lean_object* v___x_1972_, lean_object* v_env_1973_, lean_object* v_____do__lift_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
uint8_t v___x_18034__boxed_1982_; lean_object* v_res_1983_; 
v___x_18034__boxed_1982_ = lean_unbox(v___x_1972_);
v_res_1983_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(v___f_1970_, v_declName_1971_, v___x_18034__boxed_1982_, v_env_1973_, v_____do__lift_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec_ref(v_____do__lift_1974_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(lean_object* v_t_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; lean_object* v_infoState_1988_; uint8_t v_enabled_1989_; 
v___x_1987_ = lean_st_ref_get(v___y_1985_);
v_infoState_1988_ = lean_ctor_get(v___x_1987_, 7);
lean_inc_ref(v_infoState_1988_);
lean_dec(v___x_1987_);
v_enabled_1989_ = lean_ctor_get_uint8(v_infoState_1988_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1988_);
if (v_enabled_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec_ref(v_t_1984_);
v___x_1990_ = lean_box(0);
v___x_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
return v___x_1991_;
}
else
{
lean_object* v___x_1992_; lean_object* v_infoState_1993_; lean_object* v_env_1994_; lean_object* v_nextMacroScope_1995_; lean_object* v_ngen_1996_; lean_object* v_auxDeclNGen_1997_; lean_object* v_traceState_1998_; lean_object* v_cache_1999_; lean_object* v_messages_2000_; lean_object* v_snapshotTasks_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2023_; 
v___x_1992_ = lean_st_ref_take(v___y_1985_);
v_infoState_1993_ = lean_ctor_get(v___x_1992_, 7);
v_env_1994_ = lean_ctor_get(v___x_1992_, 0);
v_nextMacroScope_1995_ = lean_ctor_get(v___x_1992_, 1);
v_ngen_1996_ = lean_ctor_get(v___x_1992_, 2);
v_auxDeclNGen_1997_ = lean_ctor_get(v___x_1992_, 3);
v_traceState_1998_ = lean_ctor_get(v___x_1992_, 4);
v_cache_1999_ = lean_ctor_get(v___x_1992_, 5);
v_messages_2000_ = lean_ctor_get(v___x_1992_, 6);
v_snapshotTasks_2001_ = lean_ctor_get(v___x_1992_, 8);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2003_ = v___x_1992_;
v_isShared_2004_ = v_isSharedCheck_2023_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_snapshotTasks_2001_);
lean_inc(v_infoState_1993_);
lean_inc(v_messages_2000_);
lean_inc(v_cache_1999_);
lean_inc(v_traceState_1998_);
lean_inc(v_auxDeclNGen_1997_);
lean_inc(v_ngen_1996_);
lean_inc(v_nextMacroScope_1995_);
lean_inc(v_env_1994_);
lean_dec(v___x_1992_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2023_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
uint8_t v_enabled_2005_; lean_object* v_assignment_2006_; lean_object* v_lazyAssignment_2007_; lean_object* v_trees_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2022_; 
v_enabled_2005_ = lean_ctor_get_uint8(v_infoState_1993_, sizeof(void*)*3);
v_assignment_2006_ = lean_ctor_get(v_infoState_1993_, 0);
v_lazyAssignment_2007_ = lean_ctor_get(v_infoState_1993_, 1);
v_trees_2008_ = lean_ctor_get(v_infoState_1993_, 2);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_infoState_1993_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2010_ = v_infoState_1993_;
v_isShared_2011_ = v_isSharedCheck_2022_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_trees_2008_);
lean_inc(v_lazyAssignment_2007_);
lean_inc(v_assignment_2006_);
lean_dec(v_infoState_1993_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2022_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = l_Lean_PersistentArray_push___redArg(v_trees_2008_, v_t_1984_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 2, v___x_2012_);
v___x_2014_ = v___x_2010_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_assignment_2006_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_lazyAssignment_2007_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v___x_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2021_, sizeof(void*)*3, v_enabled_2005_);
v___x_2014_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2016_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 7, v___x_2014_);
v___x_2016_ = v___x_2003_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_env_1994_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_nextMacroScope_1995_);
lean_ctor_set(v_reuseFailAlloc_2020_, 2, v_ngen_1996_);
lean_ctor_set(v_reuseFailAlloc_2020_, 3, v_auxDeclNGen_1997_);
lean_ctor_set(v_reuseFailAlloc_2020_, 4, v_traceState_1998_);
lean_ctor_set(v_reuseFailAlloc_2020_, 5, v_cache_1999_);
lean_ctor_set(v_reuseFailAlloc_2020_, 6, v_messages_2000_);
lean_ctor_set(v_reuseFailAlloc_2020_, 7, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2020_, 8, v_snapshotTasks_2001_);
v___x_2016_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2017_ = lean_st_ref_set(v___y_1985_, v___x_2016_);
v___x_2018_ = lean_box(0);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
return v___x_2019_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg___boxed(lean_object* v_t_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_2024_, v___y_2025_);
lean_dec(v___y_2025_);
return v_res_2027_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = lean_unsigned_to_nat(32u);
v___x_2029_ = lean_mk_empty_array_with_capacity(v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1(void){
_start:
{
size_t v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2031_ = ((size_t)5ULL);
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = lean_unsigned_to_nat(32u);
v___x_2034_ = lean_mk_empty_array_with_capacity(v___x_2033_);
v___x_2035_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0);
v___x_2036_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
lean_ctor_set(v___x_2036_, 1, v___x_2034_);
lean_ctor_set(v___x_2036_, 2, v___x_2032_);
lean_ctor_set(v___x_2036_, 3, v___x_2032_);
lean_ctor_set_usize(v___x_2036_, 4, v___x_2031_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(lean_object* v_t_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v___x_2045_; lean_object* v_infoState_2046_; uint8_t v_enabled_2047_; 
v___x_2045_ = lean_st_ref_get(v___y_2043_);
v_infoState_2046_ = lean_ctor_get(v___x_2045_, 7);
lean_inc_ref(v_infoState_2046_);
lean_dec(v___x_2045_);
v_enabled_2047_ = lean_ctor_get_uint8(v_infoState_2046_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2046_);
if (v_enabled_2047_ == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec_ref(v_t_2037_);
v___x_2048_ = lean_box(0);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1);
v___x_2051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2051_, 0, v_t_2037_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v___x_2051_, v___y_2043_);
return v___x_2052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___boxed(lean_object* v_t_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v_t_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
if (lean_obj_tag(v_a_2062_) == 0)
{
lean_object* v___x_2064_; 
v___x_2064_ = l_List_reverse___redArg(v_a_2063_);
return v___x_2064_;
}
else
{
lean_object* v_head_2065_; lean_object* v_tail_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2075_; 
v_head_2065_ = lean_ctor_get(v_a_2062_, 0);
v_tail_2066_ = lean_ctor_get(v_a_2062_, 1);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_a_2062_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2068_ = v_a_2062_;
v_isShared_2069_ = v_isSharedCheck_2075_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_tail_2066_);
lean_inc(v_head_2065_);
lean_dec(v_a_2062_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2075_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = l_Lean_mkLevelParam(v_head_2065_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 1, v_a_2063_);
lean_ctor_set(v___x_2068_, 0, v___x_2070_);
v___x_2072_ = v___x_2068_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_a_2063_);
v___x_2072_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
v_a_2062_ = v_tail_2066_;
v_a_2063_ = v___x_2072_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0(void){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2076_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
lean_ctor_set(v___x_2081_, 2, v___x_2080_);
lean_ctor_set(v___x_2081_, 3, v___x_2079_);
lean_ctor_set(v___x_2081_, 4, v___x_2079_);
lean_ctor_set(v___x_2081_, 5, v___x_2079_);
lean_ctor_set(v___x_2081_, 6, v___x_2079_);
lean_ctor_set(v___x_2081_, 7, v___x_2079_);
lean_ctor_set(v___x_2081_, 8, v___x_2079_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2082_ = lean_box(1);
v___x_2083_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3);
v___x_2084_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
v___x_2085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v___x_2083_);
lean_ctor_set(v___x_2085_, 2, v___x_2082_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4));
v___x_2088_ = l_Lean_stringToMessageData(v___x_2087_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6));
v___x_2091_ = l_Lean_stringToMessageData(v___x_2090_);
return v___x_2091_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8));
v___x_2094_ = l_Lean_stringToMessageData(v___x_2093_);
return v___x_2094_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10));
v___x_2097_ = l_Lean_stringToMessageData(v___x_2096_);
return v___x_2097_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12));
v___x_2100_ = l_Lean_stringToMessageData(v___x_2099_);
return v___x_2100_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14));
v___x_2103_ = l_Lean_stringToMessageData(v___x_2102_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16));
v___x_2106_ = l_Lean_stringToMessageData(v___x_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(lean_object* v_msg_2107_, lean_object* v_declHint_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v_env_2112_; uint8_t v___x_2113_; 
v___x_2111_ = lean_st_ref_get(v___y_2109_);
v_env_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc_ref(v_env_2112_);
lean_dec(v___x_2111_);
v___x_2113_ = l_Lean_Name_isAnonymous(v_declHint_2108_);
if (v___x_2113_ == 0)
{
uint8_t v_isExporting_2114_; 
v_isExporting_2114_ = lean_ctor_get_uint8(v_env_2112_, sizeof(void*)*8);
if (v_isExporting_2114_ == 0)
{
lean_object* v___x_2115_; 
lean_dec_ref(v_env_2112_);
lean_dec(v_declHint_2108_);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v_msg_2107_);
return v___x_2115_;
}
else
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
lean_inc_ref(v_env_2112_);
v___x_2116_ = l_Lean_Environment_setExporting(v_env_2112_, v___x_2113_);
lean_inc(v_declHint_2108_);
lean_inc_ref(v___x_2116_);
v___x_2117_ = l_Lean_Environment_contains(v___x_2116_, v_declHint_2108_, v_isExporting_2114_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
lean_dec_ref(v___x_2116_);
lean_dec_ref(v_env_2112_);
lean_dec(v_declHint_2108_);
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_msg_2107_);
return v___x_2118_;
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v_c_2124_; lean_object* v___x_2125_; 
v___x_2119_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2);
v___x_2120_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3);
v___x_2121_ = l_Lean_Options_empty;
v___x_2122_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2116_);
lean_ctor_set(v___x_2122_, 1, v___x_2119_);
lean_ctor_set(v___x_2122_, 2, v___x_2120_);
lean_ctor_set(v___x_2122_, 3, v___x_2121_);
lean_inc(v_declHint_2108_);
v___x_2123_ = l_Lean_MessageData_ofConstName(v_declHint_2108_, v___x_2113_);
v_c_2124_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2124_, 0, v___x_2122_);
lean_ctor_set(v_c_2124_, 1, v___x_2123_);
v___x_2125_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2112_, v_declHint_2108_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_dec_ref(v_env_2112_);
lean_dec(v_declHint_2108_);
v___x_2126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5);
v___x_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v_c_2124_);
v___x_2128_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7);
v___x_2129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = l_Lean_MessageData_note(v___x_2129_);
v___x_2131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2131_, 0, v_msg_2107_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
return v___x_2132_;
}
else
{
lean_object* v_val_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2168_; 
v_val_2133_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2135_ = v___x_2125_;
v_isShared_2136_ = v_isSharedCheck_2168_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_val_2133_);
lean_dec(v___x_2125_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2168_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v_mod_2140_; uint8_t v___x_2141_; 
v___x_2137_ = lean_box(0);
v___x_2138_ = l_Lean_Environment_header(v_env_2112_);
lean_dec_ref(v_env_2112_);
v___x_2139_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2138_);
v_mod_2140_ = lean_array_get(v___x_2137_, v___x_2139_, v_val_2133_);
lean_dec(v_val_2133_);
lean_dec_ref(v___x_2139_);
v___x_2141_ = l_Lean_isPrivateName(v_declHint_2108_);
lean_dec(v_declHint_2108_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2153_; 
v___x_2142_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v_c_2124_);
v___x_2144_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = l_Lean_MessageData_ofName(v_mod_2140_);
v___x_2147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13);
v___x_2149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2147_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = l_Lean_MessageData_note(v___x_2149_);
v___x_2151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2151_, 0, v_msg_2107_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2151_);
v___x_2153_ = v___x_2135_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2155_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5);
v___x_2156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
lean_ctor_set(v___x_2156_, 1, v_c_2124_);
v___x_2157_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15);
v___x_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2156_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = l_Lean_MessageData_ofName(v_mod_2140_);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = l_Lean_MessageData_note(v___x_2162_);
v___x_2164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2164_, 0, v_msg_2107_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2164_);
v___x_2166_ = v___x_2135_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2169_; 
lean_dec_ref(v_env_2112_);
lean_dec(v_declHint_2108_);
v___x_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2169_, 0, v_msg_2107_);
return v___x_2169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___boxed(lean_object* v_msg_2170_, lean_object* v_declHint_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2170_, v_declHint_2171_, v___y_2172_);
lean_dec(v___y_2172_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(lean_object* v_msg_2175_, lean_object* v_declHint_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2194_; 
v___x_2184_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_2175_, v_declHint_2176_, v___y_2182_);
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2194_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2194_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2189_ = l_Lean_unknownIdentifierMessageTag;
v___x_2190_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v_a_2185_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v___x_2190_);
v___x_2192_ = v___x_2187_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23___boxed(lean_object* v_msg_2195_, lean_object* v_declHint_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2195_, v_declHint_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(lean_object* v_ref_2205_, lean_object* v_msg_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v_fileName_2214_; lean_object* v_fileMap_2215_; lean_object* v_options_2216_; lean_object* v_currRecDepth_2217_; lean_object* v_maxRecDepth_2218_; lean_object* v_ref_2219_; lean_object* v_currNamespace_2220_; lean_object* v_openDecls_2221_; lean_object* v_initHeartbeats_2222_; lean_object* v_maxHeartbeats_2223_; lean_object* v_quotContext_2224_; lean_object* v_currMacroScope_2225_; uint8_t v_diag_2226_; lean_object* v_cancelTk_x3f_2227_; uint8_t v_suppressElabErrors_2228_; lean_object* v_inheritedTraceOptions_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2238_; 
v_fileName_2214_ = lean_ctor_get(v___y_2211_, 0);
v_fileMap_2215_ = lean_ctor_get(v___y_2211_, 1);
v_options_2216_ = lean_ctor_get(v___y_2211_, 2);
v_currRecDepth_2217_ = lean_ctor_get(v___y_2211_, 3);
v_maxRecDepth_2218_ = lean_ctor_get(v___y_2211_, 4);
v_ref_2219_ = lean_ctor_get(v___y_2211_, 5);
v_currNamespace_2220_ = lean_ctor_get(v___y_2211_, 6);
v_openDecls_2221_ = lean_ctor_get(v___y_2211_, 7);
v_initHeartbeats_2222_ = lean_ctor_get(v___y_2211_, 8);
v_maxHeartbeats_2223_ = lean_ctor_get(v___y_2211_, 9);
v_quotContext_2224_ = lean_ctor_get(v___y_2211_, 10);
v_currMacroScope_2225_ = lean_ctor_get(v___y_2211_, 11);
v_diag_2226_ = lean_ctor_get_uint8(v___y_2211_, sizeof(void*)*14);
v_cancelTk_x3f_2227_ = lean_ctor_get(v___y_2211_, 12);
v_suppressElabErrors_2228_ = lean_ctor_get_uint8(v___y_2211_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2229_ = lean_ctor_get(v___y_2211_, 13);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___y_2211_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2231_ = v___y_2211_;
v_isShared_2232_ = v_isSharedCheck_2238_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_inheritedTraceOptions_2229_);
lean_inc(v_cancelTk_x3f_2227_);
lean_inc(v_currMacroScope_2225_);
lean_inc(v_quotContext_2224_);
lean_inc(v_maxHeartbeats_2223_);
lean_inc(v_initHeartbeats_2222_);
lean_inc(v_openDecls_2221_);
lean_inc(v_currNamespace_2220_);
lean_inc(v_ref_2219_);
lean_inc(v_maxRecDepth_2218_);
lean_inc(v_currRecDepth_2217_);
lean_inc(v_options_2216_);
lean_inc(v_fileMap_2215_);
lean_inc(v_fileName_2214_);
lean_dec(v___y_2211_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2238_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v_ref_2233_; lean_object* v___x_2235_; 
v_ref_2233_ = l_Lean_replaceRef(v_ref_2205_, v_ref_2219_);
lean_dec(v_ref_2219_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 5, v_ref_2233_);
v___x_2235_ = v___x_2231_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_fileName_2214_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_fileMap_2215_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_options_2216_);
lean_ctor_set(v_reuseFailAlloc_2237_, 3, v_currRecDepth_2217_);
lean_ctor_set(v_reuseFailAlloc_2237_, 4, v_maxRecDepth_2218_);
lean_ctor_set(v_reuseFailAlloc_2237_, 5, v_ref_2233_);
lean_ctor_set(v_reuseFailAlloc_2237_, 6, v_currNamespace_2220_);
lean_ctor_set(v_reuseFailAlloc_2237_, 7, v_openDecls_2221_);
lean_ctor_set(v_reuseFailAlloc_2237_, 8, v_initHeartbeats_2222_);
lean_ctor_set(v_reuseFailAlloc_2237_, 9, v_maxHeartbeats_2223_);
lean_ctor_set(v_reuseFailAlloc_2237_, 10, v_quotContext_2224_);
lean_ctor_set(v_reuseFailAlloc_2237_, 11, v_currMacroScope_2225_);
lean_ctor_set(v_reuseFailAlloc_2237_, 12, v_cancelTk_x3f_2227_);
lean_ctor_set(v_reuseFailAlloc_2237_, 13, v_inheritedTraceOptions_2229_);
lean_ctor_set_uint8(v_reuseFailAlloc_2237_, sizeof(void*)*14, v_diag_2226_);
lean_ctor_set_uint8(v_reuseFailAlloc_2237_, sizeof(void*)*14 + 1, v_suppressElabErrors_2228_);
v___x_2235_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___x_2235_, v___y_2212_);
lean_dec_ref(v___x_2235_);
return v___x_2236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg___boxed(lean_object* v_ref_2239_, lean_object* v_msg_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2239_, v_msg_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec(v_ref_2239_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(lean_object* v_ref_2249_, lean_object* v_msg_2250_, lean_object* v_declHint_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v___x_2259_; lean_object* v_a_2260_; lean_object* v___x_2261_; 
v___x_2259_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_2250_, v_declHint_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref(v___x_2259_);
v___x_2261_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_2249_, v_a_2260_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg___boxed(lean_object* v_ref_2262_, lean_object* v_msg_2263_, lean_object* v_declHint_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2262_, v_msg_2263_, v_declHint_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec(v_ref_2262_);
return v_res_2272_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0));
v___x_2275_ = l_Lean_stringToMessageData(v___x_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(lean_object* v_ref_2276_, lean_object* v_constName_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; uint8_t v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2285_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1);
v___x_2286_ = 0;
lean_inc(v_constName_2277_);
v___x_2287_ = l_Lean_MessageData_ofConstName(v_constName_2277_, v___x_2286_);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2285_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_2276_, v___x_2290_, v_constName_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___boxed(lean_object* v_ref_2292_, lean_object* v_constName_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2292_, v_constName_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec(v_ref_2292_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(lean_object* v_constName_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_ref_2310_; lean_object* v___x_2311_; 
v_ref_2310_ = lean_ctor_get(v___y_2307_, 5);
lean_inc(v_ref_2310_);
v___x_2311_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_2310_, v_constName_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v_ref_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_constName_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(lean_object* v_constName_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; lean_object* v_env_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; 
v___x_2329_ = lean_st_ref_get(v___y_2327_);
v_env_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc_ref(v_env_2330_);
lean_dec(v___x_2329_);
v___x_2331_ = 0;
lean_inc(v_constName_2321_);
v___x_2332_ = l_Lean_Environment_findConstVal_x3f(v_env_2330_, v_constName_2321_, v___x_2331_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
return v___x_2333_;
}
else
{
lean_object* v_val_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec_ref(v___y_2326_);
lean_dec_ref(v___y_2322_);
lean_dec(v_constName_2321_);
v_val_2334_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2332_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_val_2334_);
lean_dec(v___x_2332_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set_tag(v___x_2336_, 0);
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_val_2334_);
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14___boxed(lean_object* v_constName_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(lean_object* v_constName_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2359_; 
lean_inc(v_constName_2351_);
v___x_2359_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2371_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2362_ = v___x_2359_;
v_isShared_2363_ = v_isSharedCheck_2371_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2359_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2371_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v_levelParams_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v_levelParams_2364_ = lean_ctor_get(v_a_2360_, 1);
lean_inc(v_levelParams_2364_);
lean_dec(v_a_2360_);
v___x_2365_ = lean_box(0);
v___x_2366_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(v_levelParams_2364_, v___x_2365_);
v___x_2367_ = l_Lean_mkConst(v_constName_2351_, v___x_2366_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v___x_2367_);
v___x_2369_ = v___x_2362_;
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
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec(v_constName_2351_);
v_a_2372_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2359_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2359_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_constName_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_constName_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(uint8_t v___x_2389_, lean_object* v_declName_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v_ref_2398_; lean_object* v___x_2399_; 
v_ref_2398_ = lean_ctor_get(v___y_2395_, 5);
lean_inc_ref(v___y_2395_);
lean_inc_ref(v___y_2391_);
v___x_2399_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_declName_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref(v___x_2399_);
v___x_2401_ = lean_box(0);
lean_inc(v_ref_2398_);
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
lean_ctor_set(v___x_2402_, 1, v_ref_2398_);
v___x_2403_ = lean_unsigned_to_nat(32u);
v___x_2404_ = lean_mk_empty_array_with_capacity(v___x_2403_);
lean_dec_ref(v___x_2404_);
v___x_2405_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4);
v___x_2406_ = lean_box(0);
v___x_2407_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2407_, 0, v___x_2402_);
lean_ctor_set(v___x_2407_, 1, v___x_2405_);
lean_ctor_set(v___x_2407_, 2, v___x_2406_);
lean_ctor_set(v___x_2407_, 3, v_a_2400_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*4, v___x_2389_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*4 + 1, v___x_2389_);
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
v___x_2409_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v___x_2408_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec_ref(v___y_2391_);
return v___x_2409_;
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec_ref(v___y_2395_);
lean_dec_ref(v___y_2391_);
v_a_2410_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2399_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2399_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v___x_2418_, lean_object* v_declName_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
uint8_t v___x_18773__boxed_2427_; lean_object* v_res_2428_; 
v___x_18773__boxed_2427_ = lean_unbox(v___x_2418_);
v_res_2428_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(v___x_18773__boxed_2427_, v_declName_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(lean_object* v___f_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___x_2437_; lean_object* v_env_2438_; lean_object* v___x_2439_; 
v___x_2437_ = lean_st_ref_get(v___y_2435_);
v_env_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc_ref(v_env_2438_);
lean_dec(v___x_2437_);
v___x_2439_ = lean_apply_8(v___f_2429_, v_env_2438_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, lean_box(0));
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed(lean_object* v___f_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(v___f_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
return v_res_2448_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2449_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
v___x_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
return v___x_2451_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
return v___x_2453_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
v___x_2455_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
lean_ctor_set(v___x_2455_, 2, v___x_2454_);
lean_ctor_set(v___x_2455_, 3, v___x_2454_);
lean_ctor_set(v___x_2455_, 4, v___x_2454_);
lean_ctor_set(v___x_2455_, 5, v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(lean_object* v_env_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v___x_2460_; lean_object* v_nextMacroScope_2461_; lean_object* v_ngen_2462_; lean_object* v_auxDeclNGen_2463_; lean_object* v_traceState_2464_; lean_object* v_messages_2465_; lean_object* v_infoState_2466_; lean_object* v_snapshotTasks_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2493_; 
v___x_2460_ = lean_st_ref_take(v___y_2458_);
v_nextMacroScope_2461_ = lean_ctor_get(v___x_2460_, 1);
v_ngen_2462_ = lean_ctor_get(v___x_2460_, 2);
v_auxDeclNGen_2463_ = lean_ctor_get(v___x_2460_, 3);
v_traceState_2464_ = lean_ctor_get(v___x_2460_, 4);
v_messages_2465_ = lean_ctor_get(v___x_2460_, 6);
v_infoState_2466_ = lean_ctor_get(v___x_2460_, 7);
v_snapshotTasks_2467_ = lean_ctor_get(v___x_2460_, 8);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; lean_object* v_unused_2495_; 
v_unused_2494_ = lean_ctor_get(v___x_2460_, 5);
lean_dec(v_unused_2494_);
v_unused_2495_ = lean_ctor_get(v___x_2460_, 0);
lean_dec(v_unused_2495_);
v___x_2469_ = v___x_2460_;
v_isShared_2470_ = v_isSharedCheck_2493_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_snapshotTasks_2467_);
lean_inc(v_infoState_2466_);
lean_inc(v_messages_2465_);
lean_inc(v_traceState_2464_);
lean_inc(v_auxDeclNGen_2463_);
lean_inc(v_ngen_2462_);
lean_inc(v_nextMacroScope_2461_);
lean_dec(v___x_2460_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2493_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2471_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 5, v___x_2471_);
lean_ctor_set(v___x_2469_, 0, v_env_2456_);
v___x_2473_ = v___x_2469_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_env_2456_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_nextMacroScope_2461_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_ngen_2462_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_auxDeclNGen_2463_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v_traceState_2464_);
lean_ctor_set(v_reuseFailAlloc_2492_, 5, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2492_, 6, v_messages_2465_);
lean_ctor_set(v_reuseFailAlloc_2492_, 7, v_infoState_2466_);
lean_ctor_set(v_reuseFailAlloc_2492_, 8, v_snapshotTasks_2467_);
v___x_2473_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v_mctx_2476_; lean_object* v_zetaDeltaFVarIds_2477_; lean_object* v_postponed_2478_; lean_object* v_diag_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2490_; 
v___x_2474_ = lean_st_ref_set(v___y_2458_, v___x_2473_);
v___x_2475_ = lean_st_ref_take(v___y_2457_);
v_mctx_2476_ = lean_ctor_get(v___x_2475_, 0);
v_zetaDeltaFVarIds_2477_ = lean_ctor_get(v___x_2475_, 2);
v_postponed_2478_ = lean_ctor_get(v___x_2475_, 3);
v_diag_2479_ = lean_ctor_get(v___x_2475_, 4);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; 
v_unused_2491_ = lean_ctor_get(v___x_2475_, 1);
lean_dec(v_unused_2491_);
v___x_2481_ = v___x_2475_;
v_isShared_2482_ = v_isSharedCheck_2490_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_diag_2479_);
lean_inc(v_postponed_2478_);
lean_inc(v_zetaDeltaFVarIds_2477_);
lean_inc(v_mctx_2476_);
lean_dec(v___x_2475_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2490_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2483_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 1, v___x_2483_);
v___x_2485_ = v___x_2481_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_mctx_2476_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_zetaDeltaFVarIds_2477_);
lean_ctor_set(v_reuseFailAlloc_2489_, 3, v_postponed_2478_);
lean_ctor_set(v_reuseFailAlloc_2489_, 4, v_diag_2479_);
v___x_2485_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2486_ = lean_st_ref_set(v___y_2457_, v___x_2485_);
v___x_2487_ = lean_box(0);
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
return v___x_2488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___boxed(lean_object* v_env_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec(v___y_2497_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(lean_object* v_env_2501_, lean_object* v_x_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v___x_2510_; lean_object* v_env_2511_; lean_object* v_a_2513_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2510_ = lean_st_ref_get(v___y_2508_);
v_env_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc_ref(v_env_2511_);
lean_dec(v___x_2510_);
v___x_2523_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2501_, v___y_2506_, v___y_2508_);
lean_dec_ref(v___x_2523_);
lean_inc(v___y_2508_);
lean_inc(v___y_2506_);
v___x_2524_ = lean_apply_7(v_x_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, lean_box(0));
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref(v___x_2524_);
v___x_2526_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2511_, v___y_2506_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec(v___y_2506_);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v___x_2526_, 0);
lean_dec(v_unused_2534_);
v___x_2528_ = v___x_2526_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_dec(v___x_2526_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v_a_2525_);
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2525_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
else
{
lean_object* v_a_2535_; 
v_a_2535_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2535_);
lean_dec_ref(v___x_2524_);
v_a_2513_ = v_a_2535_;
goto v___jp_2512_;
}
v___jp_2512_:
{
lean_object* v___x_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
v___x_2514_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_2511_, v___y_2506_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec(v___y_2506_);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2521_ == 0)
{
lean_object* v_unused_2522_; 
v_unused_2522_ = lean_ctor_get(v___x_2514_, 0);
lean_dec(v_unused_2522_);
v___x_2516_ = v___x_2514_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_dec(v___x_2514_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
lean_ctor_set_tag(v___x_2516_, 1);
lean_ctor_set(v___x_2516_, 0, v_a_2513_);
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2513_);
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
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_env_2536_, lean_object* v_x_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2536_, v_x_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(lean_object* v_declName_2546_, lean_object* v_env_2547_, lean_object* v_addInfo_2548_, lean_object* v_____r_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = lean_private_to_user_name(v_declName_2546_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec_ref(v_addInfo_2548_);
lean_dec_ref(v_env_2547_);
v___x_2558_ = lean_box(0);
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
return v___x_2559_;
}
else
{
lean_object* v_val_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2577_; 
v_val_2560_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2562_ = v___x_2557_;
v_isShared_2563_ = v_isSharedCheck_2577_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_val_2560_);
lean_dec(v___x_2557_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2577_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
uint8_t v___x_2564_; uint8_t v___x_2565_; 
v___x_2564_ = 1;
lean_inc(v_val_2560_);
v___x_2565_ = l_Lean_Environment_contains(v_env_2547_, v_val_2560_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2568_; 
lean_dec(v_val_2560_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec_ref(v_addInfo_2548_);
v___x_2566_ = lean_box(0);
if (v_isShared_2563_ == 0)
{
lean_ctor_set_tag(v___x_2562_, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2566_);
v___x_2568_ = v___x_2562_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
else
{
lean_object* v___x_2570_; 
lean_del_object(v___x_2562_);
lean_inc(v___y_2555_);
lean_inc_ref(v___y_2554_);
lean_inc(v___y_2553_);
lean_inc_ref(v___y_2552_);
lean_inc(v___y_2551_);
lean_inc_ref(v___y_2550_);
lean_inc(v_val_2560_);
v___x_2570_ = lean_apply_8(v_addInfo_2548_, v_val_2560_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, lean_box(0));
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
lean_dec_ref(v___x_2570_);
v___x_2571_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
v___x_2572_ = l_Lean_MessageData_ofConstName(v_val_2560_, v___x_2564_);
v___x_2573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2571_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2575_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
return v___x_2576_;
}
else
{
lean_dec(v_val_2560_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
return v___x_2570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed(lean_object* v_declName_2578_, lean_object* v_env_2579_, lean_object* v_addInfo_2580_, lean_object* v_____r_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(v_declName_2578_, v_env_2579_, v_addInfo_2580_, v_____r_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(lean_object* v_addInfo_2590_, lean_object* v_declName_2591_, uint8_t v___x_2592_, lean_object* v___f_2593_, uint8_t v___x_2594_, lean_object* v_env_2595_, lean_object* v___f_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; 
lean_inc(v___y_2602_);
lean_inc_ref(v___y_2601_);
lean_inc(v___y_2600_);
lean_inc_ref(v___y_2599_);
lean_inc(v___y_2598_);
lean_inc_ref(v___y_2597_);
lean_inc(v_declName_2591_);
v___x_2604_ = lean_apply_8(v_addInfo_2590_, v_declName_2591_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, lean_box(0));
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v___x_2605_; 
lean_dec_ref(v___x_2604_);
lean_inc(v_declName_2591_);
v___x_2605_ = lean_private_to_user_name(v_declName_2591_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2606_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2607_ = l_Lean_MessageData_ofConstName(v_declName_2591_, v___x_2592_);
v___x_2608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2606_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2610_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
return v___x_2611_;
}
else
{
lean_object* v_val_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_dec(v_declName_2591_);
v_val_2612_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_val_2612_);
lean_dec_ref(v___x_2605_);
v___x_2613_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1);
v___x_2614_ = l_Lean_MessageData_ofConstName(v_val_2612_, v___x_2592_);
v___x_2615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2613_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_2617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2615_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2617_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
return v___x_2618_;
}
}
else
{
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v_declName_2591_);
return v___x_2604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed(lean_object* v_addInfo_2619_, lean_object* v_declName_2620_, lean_object* v___x_2621_, lean_object* v___f_2622_, lean_object* v___x_2623_, lean_object* v_env_2624_, lean_object* v___f_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
uint8_t v___x_19127__boxed_2633_; uint8_t v___x_19129__boxed_2634_; lean_object* v_res_2635_; 
v___x_19127__boxed_2633_ = lean_unbox(v___x_2621_);
v___x_19129__boxed_2634_ = lean_unbox(v___x_2623_);
v_res_2635_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(v_addInfo_2619_, v_declName_2620_, v___x_19127__boxed_2633_, v___f_2622_, v___x_19129__boxed_2634_, v_env_2624_, v___f_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec_ref(v___f_2625_);
lean_dec_ref(v_env_2624_);
lean_dec_ref(v___f_2622_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(lean_object* v_declName_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v___x_2647_; lean_object* v_env_2648_; uint8_t v___x_2649_; lean_object* v_addInfo_2650_; lean_object* v_env_2651_; lean_object* v___f_2652_; lean_object* v___f_2653_; lean_object* v___x_2654_; lean_object* v___f_2655_; uint8_t v___x_2656_; uint8_t v___x_2657_; 
v___x_2647_ = lean_st_ref_get(v___y_2645_);
v_env_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc_ref(v_env_2648_);
lean_dec(v___x_2647_);
v___x_2649_ = 0;
v_addInfo_2650_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0));
v_env_2651_ = l_Lean_Environment_setExporting(v_env_2648_, v___x_2649_);
lean_inc_ref(v_env_2651_);
lean_inc(v_declName_2639_);
v___f_2652_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed), 11, 3);
lean_closure_set(v___f_2652_, 0, v_declName_2639_);
lean_closure_set(v___f_2652_, 1, v_env_2651_);
lean_closure_set(v___f_2652_, 2, v_addInfo_2650_);
lean_inc(v_declName_2639_);
lean_inc_ref(v_env_2651_);
v___f_2653_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2653_, 0, v_env_2651_);
lean_closure_set(v___f_2653_, 1, v_declName_2639_);
lean_closure_set(v___f_2653_, 2, v___f_2652_);
lean_closure_set(v___f_2653_, 3, v_addInfo_2650_);
v___x_2654_ = lean_box(v___x_2649_);
lean_inc_ref(v_env_2651_);
lean_inc(v_declName_2639_);
lean_inc_ref(v___f_2653_);
v___f_2655_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed), 12, 4);
lean_closure_set(v___f_2655_, 0, v___f_2653_);
lean_closure_set(v___f_2655_, 1, v_declName_2639_);
lean_closure_set(v___f_2655_, 2, v___x_2654_);
lean_closure_set(v___f_2655_, 3, v_env_2651_);
v___x_2656_ = 1;
lean_inc(v_declName_2639_);
lean_inc_ref(v_env_2651_);
v___x_2657_ = l_Lean_Environment_contains(v_env_2651_, v_declName_2639_, v___x_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___f_2658_; lean_object* v___x_2659_; 
lean_dec_ref(v___f_2653_);
lean_dec(v_declName_2639_);
v___f_2658_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed), 8, 1);
lean_closure_set(v___f_2658_, 0, v___f_2655_);
v___x_2659_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2651_, v___f_2658_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2659_;
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___f_2662_; lean_object* v___x_2663_; 
v___x_2660_ = lean_box(v___x_2656_);
v___x_2661_ = lean_box(v___x_2649_);
lean_inc_ref(v_env_2651_);
v___f_2662_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed), 14, 7);
lean_closure_set(v___f_2662_, 0, v_addInfo_2650_);
lean_closure_set(v___f_2662_, 1, v_declName_2639_);
lean_closure_set(v___f_2662_, 2, v___x_2660_);
lean_closure_set(v___f_2662_, 3, v___f_2653_);
lean_closure_set(v___f_2662_, 4, v___x_2661_);
lean_closure_set(v___f_2662_, 5, v_env_2651_);
lean_closure_set(v___f_2662_, 6, v___f_2655_);
v___x_2663_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_2651_, v___f_2662_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___boxed(lean_object* v_declName_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(lean_object* v_modifiers_2673_, lean_object* v_declName_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; lean_object* v_env_2683_; uint8_t v_visibility_2684_; uint8_t v_isProtected_2685_; lean_object* v_declName_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; uint8_t v___x_2749_; 
v___x_2682_ = lean_st_ref_get(v___y_2680_);
v_env_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc_ref(v_env_2683_);
lean_dec(v___x_2682_);
v_visibility_2684_ = lean_ctor_get_uint8(v_modifiers_2673_, sizeof(void*)*3);
v_isProtected_2685_ = lean_ctor_get_uint8(v_modifiers_2673_, sizeof(void*)*3 + 1);
v___x_2749_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_2683_, v_visibility_2684_);
lean_dec_ref(v_env_2683_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v_env_2751_; lean_object* v_declName_2752_; 
v___x_2750_ = lean_st_ref_get(v___y_2680_);
v_env_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc_ref(v_env_2751_);
lean_dec(v___x_2750_);
v_declName_2752_ = l_Lean_mkPrivateName(v_env_2751_, v_declName_2674_);
lean_dec_ref(v_env_2751_);
v_declName_2687_ = v_declName_2752_;
v___y_2688_ = v___y_2675_;
v___y_2689_ = v___y_2676_;
v___y_2690_ = v___y_2677_;
v___y_2691_ = v___y_2678_;
v___y_2692_ = v___y_2679_;
v___y_2693_ = v___y_2680_;
goto v___jp_2686_;
}
else
{
v_declName_2687_ = v_declName_2674_;
v___y_2688_ = v___y_2675_;
v___y_2689_ = v___y_2676_;
v___y_2690_ = v___y_2677_;
v___y_2691_ = v___y_2678_;
v___y_2692_ = v___y_2679_;
v___y_2693_ = v___y_2680_;
goto v___jp_2686_;
}
v___jp_2686_:
{
lean_object* v___x_2694_; 
lean_inc(v___y_2693_);
lean_inc(v___y_2691_);
lean_inc(v_declName_2687_);
v___x_2694_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2739_; 
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2739_ == 0)
{
lean_object* v_unused_2740_; 
v_unused_2740_ = lean_ctor_get(v___x_2694_, 0);
lean_dec(v_unused_2740_);
v___x_2696_ = v___x_2694_;
v_isShared_2697_ = v_isSharedCheck_2739_;
goto v_resetjp_2695_;
}
else
{
lean_dec(v___x_2694_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2739_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
if (v_isProtected_2685_ == 0)
{
lean_object* v___x_2699_; 
lean_dec(v___y_2693_);
lean_dec(v___y_2691_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v_declName_2687_);
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_declName_2687_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
else
{
lean_object* v___x_2701_; lean_object* v_env_2702_; lean_object* v_nextMacroScope_2703_; lean_object* v_ngen_2704_; lean_object* v_auxDeclNGen_2705_; lean_object* v_traceState_2706_; lean_object* v_messages_2707_; lean_object* v_infoState_2708_; lean_object* v_snapshotTasks_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2737_; 
v___x_2701_ = lean_st_ref_take(v___y_2693_);
v_env_2702_ = lean_ctor_get(v___x_2701_, 0);
v_nextMacroScope_2703_ = lean_ctor_get(v___x_2701_, 1);
v_ngen_2704_ = lean_ctor_get(v___x_2701_, 2);
v_auxDeclNGen_2705_ = lean_ctor_get(v___x_2701_, 3);
v_traceState_2706_ = lean_ctor_get(v___x_2701_, 4);
v_messages_2707_ = lean_ctor_get(v___x_2701_, 6);
v_infoState_2708_ = lean_ctor_get(v___x_2701_, 7);
v_snapshotTasks_2709_ = lean_ctor_get(v___x_2701_, 8);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2737_ == 0)
{
lean_object* v_unused_2738_; 
v_unused_2738_ = lean_ctor_get(v___x_2701_, 5);
lean_dec(v_unused_2738_);
v___x_2711_ = v___x_2701_;
v_isShared_2712_ = v_isSharedCheck_2737_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_snapshotTasks_2709_);
lean_inc(v_infoState_2708_);
lean_inc(v_messages_2707_);
lean_inc(v_traceState_2706_);
lean_inc(v_auxDeclNGen_2705_);
lean_inc(v_ngen_2704_);
lean_inc(v_nextMacroScope_2703_);
lean_inc(v_env_2702_);
lean_dec(v___x_2701_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2737_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
lean_inc(v_declName_2687_);
v___x_2713_ = l_Lean_addProtected(v_env_2702_, v_declName_2687_);
v___x_2714_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 5, v___x_2714_);
lean_ctor_set(v___x_2711_, 0, v___x_2713_);
v___x_2716_ = v___x_2711_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2713_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_nextMacroScope_2703_);
lean_ctor_set(v_reuseFailAlloc_2736_, 2, v_ngen_2704_);
lean_ctor_set(v_reuseFailAlloc_2736_, 3, v_auxDeclNGen_2705_);
lean_ctor_set(v_reuseFailAlloc_2736_, 4, v_traceState_2706_);
lean_ctor_set(v_reuseFailAlloc_2736_, 5, v___x_2714_);
lean_ctor_set(v_reuseFailAlloc_2736_, 6, v_messages_2707_);
lean_ctor_set(v_reuseFailAlloc_2736_, 7, v_infoState_2708_);
lean_ctor_set(v_reuseFailAlloc_2736_, 8, v_snapshotTasks_2709_);
v___x_2716_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v_mctx_2719_; lean_object* v_zetaDeltaFVarIds_2720_; lean_object* v_postponed_2721_; lean_object* v_diag_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2734_; 
v___x_2717_ = lean_st_ref_set(v___y_2693_, v___x_2716_);
lean_dec(v___y_2693_);
v___x_2718_ = lean_st_ref_take(v___y_2691_);
v_mctx_2719_ = lean_ctor_get(v___x_2718_, 0);
v_zetaDeltaFVarIds_2720_ = lean_ctor_get(v___x_2718_, 2);
v_postponed_2721_ = lean_ctor_get(v___x_2718_, 3);
v_diag_2722_ = lean_ctor_get(v___x_2718_, 4);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2734_ == 0)
{
lean_object* v_unused_2735_; 
v_unused_2735_ = lean_ctor_get(v___x_2718_, 1);
lean_dec(v_unused_2735_);
v___x_2724_ = v___x_2718_;
v_isShared_2725_ = v_isSharedCheck_2734_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_diag_2722_);
lean_inc(v_postponed_2721_);
lean_inc(v_zetaDeltaFVarIds_2720_);
lean_inc(v_mctx_2719_);
lean_dec(v___x_2718_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2734_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2726_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 1, v___x_2726_);
v___x_2728_ = v___x_2724_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_mctx_2719_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v___x_2726_);
lean_ctor_set(v_reuseFailAlloc_2733_, 2, v_zetaDeltaFVarIds_2720_);
lean_ctor_set(v_reuseFailAlloc_2733_, 3, v_postponed_2721_);
lean_ctor_set(v_reuseFailAlloc_2733_, 4, v_diag_2722_);
v___x_2728_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2729_ = lean_st_ref_set(v___y_2691_, v___x_2728_);
lean_dec(v___y_2691_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v_declName_2687_);
v___x_2731_ = v___x_2696_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_declName_2687_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
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
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v___y_2693_);
lean_dec(v___y_2691_);
lean_dec(v_declName_2687_);
v_a_2741_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2694_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2694_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4___boxed(lean_object* v_modifiers_2753_, lean_object* v_declName_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2753_, v_declName_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec_ref(v_modifiers_2753_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(lean_object* v_pre_2763_, lean_object* v_declName_2764_, lean_object* v_as_2765_, size_t v_sz_2766_, size_t v_i_2767_, lean_object* v_b_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_a_2777_; uint8_t v___x_2781_; 
v___x_2781_ = lean_usize_dec_lt(v_i_2767_, v_sz_2766_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; 
lean_dec_ref(v___y_2769_);
lean_dec(v_declName_2764_);
lean_dec(v_pre_2763_);
v___x_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2782_, 0, v_b_2768_);
return v___x_2782_;
}
else
{
lean_object* v___x_2783_; lean_object* v_a_2784_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v___x_2783_ = lean_box(0);
v_a_2784_ = lean_array_uget_borrowed(v_as_2765_, v_i_2767_);
lean_inc(v_a_2784_);
lean_inc(v_pre_2763_);
v___x_2785_ = l_Lean_Name_append(v_pre_2763_, v_a_2784_);
v___x_2786_ = lean_name_eq(v___x_2785_, v_declName_2764_);
lean_dec(v___x_2785_);
if (v___x_2786_ == 0)
{
v_a_2777_ = v___x_2783_;
goto v___jp_2776_;
}
else
{
lean_object* v___x_2787_; uint8_t v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2787_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_2788_ = 0;
lean_inc(v_declName_2764_);
v___x_2789_ = l_Lean_MessageData_ofConstName(v_declName_2764_, v___x_2788_);
v___x_2790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2787_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
v___x_2792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2790_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
lean_inc(v_pre_2763_);
v___x_2793_ = l_Lean_MessageData_ofName(v_pre_2763_);
v___x_2794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
v___x_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2794_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
lean_inc(v_a_2784_);
v___x_2797_ = l_Lean_MessageData_ofName(v_a_2784_);
v___x_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2796_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
lean_inc_ref(v___y_2769_);
v___x_2801_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2800_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_dec_ref(v___x_2801_);
v_a_2777_ = v___x_2783_;
goto v___jp_2776_;
}
else
{
lean_dec_ref(v___y_2769_);
lean_dec(v_declName_2764_);
lean_dec(v_pre_2763_);
return v___x_2801_;
}
}
}
v___jp_2776_:
{
size_t v___x_2778_; size_t v___x_2779_; 
v___x_2778_ = ((size_t)1ULL);
v___x_2779_ = lean_usize_add(v_i_2767_, v___x_2778_);
v_i_2767_ = v___x_2779_;
v_b_2768_ = v_a_2777_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6___boxed(lean_object* v_pre_2802_, lean_object* v_declName_2803_, lean_object* v_as_2804_, lean_object* v_sz_2805_, lean_object* v_i_2806_, lean_object* v_b_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
size_t v_sz_boxed_2815_; size_t v_i_boxed_2816_; lean_object* v_res_2817_; 
v_sz_boxed_2815_ = lean_unbox_usize(v_sz_2805_);
lean_dec(v_sz_2805_);
v_i_boxed_2816_ = lean_unbox_usize(v_i_2806_);
lean_dec(v_i_2806_);
v_res_2817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2802_, v_declName_2803_, v_as_2804_, v_sz_boxed_2815_, v_i_boxed_2816_, v_b_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v_as_2804_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(lean_object* v_declName_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
if (lean_obj_tag(v_declName_2818_) == 1)
{
lean_object* v_pre_2826_; lean_object* v___x_2827_; lean_object* v_env_2828_; uint8_t v___x_2829_; 
v_pre_2826_ = lean_ctor_get(v_declName_2818_, 0);
lean_inc(v_pre_2826_);
v___x_2827_ = lean_st_ref_get(v___y_2824_);
v_env_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc_ref(v_env_2828_);
lean_dec(v___x_2827_);
lean_inc(v_pre_2826_);
v___x_2829_ = l_Lean_isStructure(v_env_2828_, v_pre_2826_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_dec_ref(v_declName_2818_);
lean_dec(v_pre_2826_);
lean_dec_ref(v___y_2819_);
v___x_2830_ = lean_box(0);
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
return v___x_2831_;
}
else
{
lean_object* v___x_2832_; lean_object* v_env_2833_; lean_object* v_fieldNames_2834_; lean_object* v___x_2835_; size_t v_sz_2836_; size_t v___x_2837_; lean_object* v___x_2838_; 
v___x_2832_ = lean_st_ref_get(v___y_2824_);
v_env_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc_ref(v_env_2833_);
lean_dec(v___x_2832_);
lean_inc(v_pre_2826_);
v_fieldNames_2834_ = l_Lean_getStructureFieldsFlattened(v_env_2833_, v_pre_2826_, v___x_2829_);
v___x_2835_ = lean_box(0);
v_sz_2836_ = lean_array_size(v_fieldNames_2834_);
v___x_2837_ = ((size_t)0ULL);
v___x_2838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_2826_, v_declName_2818_, v_fieldNames_2834_, v_sz_2836_, v___x_2837_, v___x_2835_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec_ref(v_fieldNames_2834_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; 
v_unused_2846_ = lean_ctor_get(v___x_2838_, 0);
lean_dec(v_unused_2846_);
v___x_2840_ = v___x_2838_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_dec(v___x_2838_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2835_);
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2835_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
else
{
return v___x_2838_;
}
}
}
else
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
lean_dec_ref(v___y_2819_);
lean_dec(v_declName_2818_);
v___x_2847_ = lean_box(0);
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
return v___x_2848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3___boxed(lean_object* v_declName_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v_declName_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(lean_object* v_currNamespace_2858_, lean_object* v_modifiers_2859_, lean_object* v_shortName_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2874_; lean_object* v_shortName_2875_; lean_object* v_currNamespace_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v_view_2936_; lean_object* v_name_2937_; lean_object* v_imported_2938_; lean_object* v_ctx_2939_; lean_object* v_scopes_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2998_; 
lean_inc(v_shortName_2860_);
v_view_2936_ = l_Lean_extractMacroScopes(v_shortName_2860_);
v_name_2937_ = lean_ctor_get(v_view_2936_, 0);
v_imported_2938_ = lean_ctor_get(v_view_2936_, 1);
v_ctx_2939_ = lean_ctor_get(v_view_2936_, 2);
v_scopes_2940_ = lean_ctor_get(v_view_2936_, 3);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_view_2936_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2942_ = v_view_2936_;
v_isShared_2943_ = v_isSharedCheck_2998_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_scopes_2940_);
lean_inc(v_ctx_2939_);
lean_inc(v_imported_2938_);
lean_inc(v_name_2937_);
lean_dec(v_view_2936_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2998_;
goto v_resetjp_2941_;
}
v___jp_2868_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___y_2870_);
lean_ctor_set(v___x_2871_, 1, v___y_2869_);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
v___jp_2873_:
{
lean_object* v___x_2883_; 
lean_inc_ref(v___y_2877_);
lean_inc(v___y_2874_);
v___x_2883_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v___y_2874_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v___x_2884_; 
lean_dec_ref(v___x_2883_);
lean_inc(v___y_2882_);
lean_inc_ref(v___y_2881_);
lean_inc(v___y_2880_);
lean_inc_ref(v___y_2879_);
lean_inc(v___y_2878_);
lean_inc_ref(v___y_2877_);
v___x_2884_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_2859_, v___y_2874_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2884_) == 0)
{
uint8_t v_isProtected_2885_; 
v_isProtected_2885_ = lean_ctor_get_uint8(v_modifiers_2859_, sizeof(void*)*3 + 1);
if (v_isProtected_2885_ == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2894_; 
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v_currNamespace_2876_);
v_a_2886_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2888_ = v___x_2884_;
v_isShared_2889_ = v_isSharedCheck_2894_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2884_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2894_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2890_, 0, v_a_2886_);
lean_ctor_set(v___x_2890_, 1, v_shortName_2875_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v___x_2890_);
v___x_2892_ = v___x_2888_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
else
{
if (lean_obj_tag(v_currNamespace_2876_) == 1)
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
v_a_2895_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2897_ = v___x_2884_;
v_isShared_2898_ = v_isSharedCheck_2907_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2884_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2907_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v_str_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2905_; 
v_str_2899_ = lean_ctor_get(v_currNamespace_2876_, 1);
lean_inc_ref(v_str_2899_);
lean_dec_ref(v_currNamespace_2876_);
v___x_2900_ = lean_box(0);
v___x_2901_ = l_Lean_Name_str___override(v___x_2900_, v_str_2899_);
v___x_2902_ = l_Lean_Name_append(v___x_2901_, v_shortName_2875_);
v___x_2903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2903_, 0, v_a_2895_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2903_);
v___x_2905_ = v___x_2897_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2903_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
else
{
lean_object* v_a_2908_; uint8_t v___x_2909_; 
lean_dec(v_currNamespace_2876_);
v_a_2908_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2908_);
lean_dec_ref(v___x_2884_);
v___x_2909_ = l_Lean_Name_isAtomic(v_shortName_2875_);
if (v___x_2909_ == 0)
{
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
v___y_2869_ = v_shortName_2875_;
v___y_2870_ = v_a_2908_;
goto v___jp_2868_;
}
else
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec(v_a_2908_);
lean_dec(v_shortName_2875_);
v___x_2910_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1, &l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
v___x_2911_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2910_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2911_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v_currNamespace_2876_);
lean_dec(v_shortName_2875_);
v_a_2920_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2884_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2884_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v_currNamespace_2876_);
lean_dec(v_shortName_2875_);
lean_dec(v___y_2874_);
v_a_2928_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2883_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2883_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
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
v_resetjp_2941_:
{
lean_object* v___x_2944_; uint8_t v_isRootName_2945_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; uint8_t v___x_2987_; 
v___x_2944_ = ((lean_object*)(l_Lean_Elab_mkDeclName___redArg___closed__1));
v_isRootName_2945_ = l_Lean_Name_isPrefixOf(v___x_2944_, v_name_2937_);
v___x_2987_ = lean_name_eq(v_name_2937_, v___x_2944_);
if (v___x_2987_ == 0)
{
v___y_2974_ = v___y_2861_;
v___y_2975_ = v___y_2862_;
v___y_2976_ = v___y_2863_;
v___y_2977_ = v___y_2864_;
v___y_2978_ = v___y_2865_;
v___y_2979_ = v___y_2866_;
goto v___jp_2973_;
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_del_object(v___x_2942_);
lean_dec(v_scopes_2940_);
lean_dec(v_ctx_2939_);
lean_dec(v_imported_2938_);
lean_dec(v_name_2937_);
lean_dec(v_shortName_2860_);
lean_dec(v_currNamespace_2858_);
v___x_2988_ = lean_obj_once(&l_Lean_Elab_mkDeclName___redArg___closed__3, &l_Lean_Elab_mkDeclName___redArg___closed__3_once, _init_l_Lean_Elab_mkDeclName___redArg___closed__3);
v___x_2989_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2988_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
v___jp_2946_:
{
if (v_isRootName_2945_ == 0)
{
lean_dec(v_name_2937_);
v___y_2874_ = v___y_2953_;
v_shortName_2875_ = v_shortName_2860_;
v_currNamespace_2876_ = v_currNamespace_2858_;
v___y_2877_ = v___y_2950_;
v___y_2878_ = v___y_2949_;
v___y_2879_ = v___y_2951_;
v___y_2880_ = v___y_2952_;
v___y_2881_ = v___y_2947_;
v___y_2882_ = v___y_2948_;
goto v___jp_2873_;
}
else
{
lean_dec(v_shortName_2860_);
lean_dec(v_currNamespace_2858_);
if (lean_obj_tag(v_name_2937_) == 1)
{
lean_object* v_pre_2954_; lean_object* v_str_2955_; lean_object* v___x_2956_; lean_object* v_shortName_2957_; lean_object* v_currNamespace_2958_; 
v_pre_2954_ = lean_ctor_get(v_name_2937_, 0);
lean_inc(v_pre_2954_);
v_str_2955_ = lean_ctor_get(v_name_2937_, 1);
lean_inc_ref(v_str_2955_);
lean_dec_ref(v_name_2937_);
v___x_2956_ = lean_box(0);
v_shortName_2957_ = l_Lean_Name_str___override(v___x_2956_, v_str_2955_);
v_currNamespace_2958_ = l_Lean_Name_replacePrefix(v_pre_2954_, v___x_2944_, v___x_2956_);
v___y_2874_ = v___y_2953_;
v_shortName_2875_ = v_shortName_2957_;
v_currNamespace_2876_ = v_currNamespace_2958_;
v___y_2877_ = v___y_2950_;
v___y_2878_ = v___y_2949_;
v___y_2879_ = v___y_2951_;
v___y_2880_ = v___y_2952_;
v___y_2881_ = v___y_2947_;
v___y_2882_ = v___y_2948_;
goto v___jp_2873_;
}
else
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec(v___y_2953_);
v___x_2959_ = lean_obj_once(&l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1, &l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
v___x_2960_ = l_Lean_MessageData_ofName(v_name_2937_);
v___x_2961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2959_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
v___x_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2961_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_2963_, v___y_2950_, v___y_2949_, v___y_2951_, v___y_2952_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2949_);
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2964_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2964_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
}
v___jp_2973_:
{
if (v_isRootName_2945_ == 0)
{
lean_object* v___x_2980_; 
lean_del_object(v___x_2942_);
lean_dec(v_scopes_2940_);
lean_dec(v_ctx_2939_);
lean_dec(v_imported_2938_);
lean_inc(v_shortName_2860_);
lean_inc(v_currNamespace_2858_);
v___x_2980_ = l_Lean_Name_append(v_currNamespace_2858_, v_shortName_2860_);
v___y_2947_ = v___y_2978_;
v___y_2948_ = v___y_2979_;
v___y_2949_ = v___y_2975_;
v___y_2950_ = v___y_2974_;
v___y_2951_ = v___y_2976_;
v___y_2952_ = v___y_2977_;
v___y_2953_ = v___x_2980_;
goto v___jp_2946_;
}
else
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2984_; 
v___x_2981_ = lean_box(0);
lean_inc(v_name_2937_);
v___x_2982_ = l_Lean_Name_replacePrefix(v_name_2937_, v___x_2944_, v___x_2981_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2982_);
v___x_2984_ = v___x_2942_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2982_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_imported_2938_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_ctx_2939_);
lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_scopes_2940_);
v___x_2984_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Lean_MacroScopesView_review(v___x_2984_);
v___y_2947_ = v___y_2978_;
v___y_2948_ = v___y_2979_;
v___y_2949_ = v___y_2975_;
v___y_2950_ = v___y_2974_;
v___y_2951_ = v___y_2976_;
v___y_2952_ = v___y_2977_;
v___y_2953_ = v___x_2985_;
goto v___jp_2946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2___boxed(lean_object* v_currNamespace_2999_, lean_object* v_modifiers_3000_, lean_object* v_shortName_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_2999_, v_modifiers_3000_, v_shortName_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec_ref(v_modifiers_3000_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(uint8_t v___x_3010_, lean_object* v_as_3011_, size_t v_i_3012_, size_t v_stop_3013_, lean_object* v_b_3014_){
_start:
{
lean_object* v___y_3016_; uint8_t v___x_3020_; 
v___x_3020_ = lean_usize_dec_eq(v_i_3012_, v_stop_3013_);
if (v___x_3020_ == 0)
{
lean_object* v_fst_3021_; uint8_t v___x_3022_; 
v_fst_3021_ = lean_ctor_get(v_b_3014_, 0);
v___x_3022_ = lean_unbox(v_fst_3021_);
if (v___x_3022_ == 0)
{
lean_object* v_snd_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3032_; 
v_snd_3023_ = lean_ctor_get(v_b_3014_, 1);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_b_3014_);
if (v_isSharedCheck_3032_ == 0)
{
lean_object* v_unused_3033_; 
v_unused_3033_ = lean_ctor_get(v_b_3014_, 0);
lean_dec(v_unused_3033_);
v___x_3025_ = v_b_3014_;
v_isShared_3026_ = v_isSharedCheck_3032_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_snd_3023_);
lean_dec(v_b_3014_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3032_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
uint8_t v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3027_ = 1;
v___x_3028_ = lean_box(v___x_3027_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v___x_3028_);
v___x_3030_ = v___x_3025_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3028_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_snd_3023_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
v___y_3016_ = v___x_3030_;
goto v___jp_3015_;
}
}
}
else
{
lean_object* v_snd_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3044_; 
v_snd_3034_ = lean_ctor_get(v_b_3014_, 1);
v_isSharedCheck_3044_ = !lean_is_exclusive(v_b_3014_);
if (v_isSharedCheck_3044_ == 0)
{
lean_object* v_unused_3045_; 
v_unused_3045_ = lean_ctor_get(v_b_3014_, 0);
lean_dec(v_unused_3045_);
v___x_3036_ = v_b_3014_;
v_isShared_3037_ = v_isSharedCheck_3044_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_snd_3034_);
lean_dec(v_b_3014_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3044_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3038_ = lean_array_uget_borrowed(v_as_3011_, v_i_3012_);
lean_inc(v___x_3038_);
v___x_3039_ = lean_array_push(v_snd_3034_, v___x_3038_);
v___x_3040_ = lean_box(v___x_3010_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 1, v___x_3039_);
lean_ctor_set(v___x_3036_, 0, v___x_3040_);
v___x_3042_ = v___x_3036_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3043_, 1, v___x_3039_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
v___y_3016_ = v___x_3042_;
goto v___jp_3015_;
}
}
}
}
else
{
return v_b_3014_;
}
v___jp_3015_:
{
size_t v___x_3017_; size_t v___x_3018_; 
v___x_3017_ = ((size_t)1ULL);
v___x_3018_ = lean_usize_add(v_i_3012_, v___x_3017_);
v_i_3012_ = v___x_3018_;
v_b_3014_ = v___y_3016_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4___boxed(lean_object* v___x_3046_, lean_object* v_as_3047_, lean_object* v_i_3048_, lean_object* v_stop_3049_, lean_object* v_b_3050_){
_start:
{
uint8_t v___x_19836__boxed_3051_; size_t v_i_boxed_3052_; size_t v_stop_boxed_3053_; lean_object* v_res_3054_; 
v___x_19836__boxed_3051_ = lean_unbox(v___x_3046_);
v_i_boxed_3052_ = lean_unbox_usize(v_i_3048_);
lean_dec(v_i_3048_);
v_stop_boxed_3053_ = lean_unbox_usize(v_stop_3049_);
lean_dec(v_stop_3049_);
v_res_3054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_19836__boxed_3051_, v_as_3047_, v_i_boxed_3052_, v_stop_boxed_3053_, v_b_3050_);
lean_dec_ref(v_as_3047_);
return v_res_3054_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(lean_object* v_a_3055_, lean_object* v_x_3056_){
_start:
{
if (lean_obj_tag(v_x_3056_) == 0)
{
uint8_t v___x_3057_; 
v___x_3057_ = 0;
return v___x_3057_;
}
else
{
lean_object* v_head_3058_; lean_object* v_tail_3059_; uint8_t v___x_3060_; 
v_head_3058_ = lean_ctor_get(v_x_3056_, 0);
v_tail_3059_ = lean_ctor_get(v_x_3056_, 1);
v___x_3060_ = lean_name_eq(v_a_3055_, v_head_3058_);
if (v___x_3060_ == 0)
{
v_x_3056_ = v_tail_3059_;
goto _start;
}
else
{
return v___x_3060_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_expandDeclId_spec__0___boxed(lean_object* v_a_3062_, lean_object* v_x_3063_){
_start:
{
uint8_t v_res_3064_; lean_object* v_r_3065_; 
v_res_3064_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_a_3062_, v_x_3063_);
lean_dec(v_x_3063_);
lean_dec(v_a_3062_);
v_r_3065_ = lean_box(v_res_3064_);
return v_r_3065_;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = ((lean_object*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0));
v___x_3068_ = l_Lean_stringToMessageData(v___x_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(lean_object* v_u_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3077_ = lean_obj_once(&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1, &l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1);
v___x_3078_ = l_Lean_MessageData_ofName(v_u_3069_);
v___x_3079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3077_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
v___x_3080_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
v___x_3081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_3081_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___boxed(lean_object* v_u_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(lean_object* v_as_3092_, size_t v_i_3093_, size_t v_stop_3094_, lean_object* v_b_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_a_3104_; uint8_t v___x_3108_; 
v___x_3108_ = lean_usize_dec_eq(v_i_3093_, v_stop_3094_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; lean_object* v_id_3110_; uint8_t v___x_3111_; 
v___x_3109_ = lean_array_uget_borrowed(v_as_3092_, v_i_3093_);
v_id_3110_ = l_Lean_Syntax_getId(v___x_3109_);
v___x_3111_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_id_3110_, v_b_3095_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; 
v___x_3112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3112_, 0, v_id_3110_);
lean_ctor_set(v___x_3112_, 1, v_b_3095_);
v_a_3104_ = v___x_3112_;
goto v___jp_3103_;
}
else
{
lean_object* v_fileName_3113_; lean_object* v_fileMap_3114_; lean_object* v_options_3115_; lean_object* v_currRecDepth_3116_; lean_object* v_maxRecDepth_3117_; lean_object* v_ref_3118_; lean_object* v_currNamespace_3119_; lean_object* v_openDecls_3120_; lean_object* v_initHeartbeats_3121_; lean_object* v_maxHeartbeats_3122_; lean_object* v_quotContext_3123_; lean_object* v_currMacroScope_3124_; uint8_t v_diag_3125_; lean_object* v_cancelTk_x3f_3126_; uint8_t v_suppressElabErrors_3127_; lean_object* v_inheritedTraceOptions_3128_; lean_object* v_ref_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
lean_dec(v_b_3095_);
v_fileName_3113_ = lean_ctor_get(v___y_3100_, 0);
v_fileMap_3114_ = lean_ctor_get(v___y_3100_, 1);
v_options_3115_ = lean_ctor_get(v___y_3100_, 2);
v_currRecDepth_3116_ = lean_ctor_get(v___y_3100_, 3);
v_maxRecDepth_3117_ = lean_ctor_get(v___y_3100_, 4);
v_ref_3118_ = lean_ctor_get(v___y_3100_, 5);
v_currNamespace_3119_ = lean_ctor_get(v___y_3100_, 6);
v_openDecls_3120_ = lean_ctor_get(v___y_3100_, 7);
v_initHeartbeats_3121_ = lean_ctor_get(v___y_3100_, 8);
v_maxHeartbeats_3122_ = lean_ctor_get(v___y_3100_, 9);
v_quotContext_3123_ = lean_ctor_get(v___y_3100_, 10);
v_currMacroScope_3124_ = lean_ctor_get(v___y_3100_, 11);
v_diag_3125_ = lean_ctor_get_uint8(v___y_3100_, sizeof(void*)*14);
v_cancelTk_x3f_3126_ = lean_ctor_get(v___y_3100_, 12);
v_suppressElabErrors_3127_ = lean_ctor_get_uint8(v___y_3100_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3128_ = lean_ctor_get(v___y_3100_, 13);
v_ref_3129_ = l_Lean_replaceRef(v___x_3109_, v_ref_3118_);
lean_inc_ref(v_inheritedTraceOptions_3128_);
lean_inc(v_cancelTk_x3f_3126_);
lean_inc(v_currMacroScope_3124_);
lean_inc(v_quotContext_3123_);
lean_inc(v_maxHeartbeats_3122_);
lean_inc(v_initHeartbeats_3121_);
lean_inc(v_openDecls_3120_);
lean_inc(v_currNamespace_3119_);
lean_inc(v_maxRecDepth_3117_);
lean_inc(v_currRecDepth_3116_);
lean_inc_ref(v_options_3115_);
lean_inc_ref(v_fileMap_3114_);
lean_inc_ref(v_fileName_3113_);
v___x_3130_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3130_, 0, v_fileName_3113_);
lean_ctor_set(v___x_3130_, 1, v_fileMap_3114_);
lean_ctor_set(v___x_3130_, 2, v_options_3115_);
lean_ctor_set(v___x_3130_, 3, v_currRecDepth_3116_);
lean_ctor_set(v___x_3130_, 4, v_maxRecDepth_3117_);
lean_ctor_set(v___x_3130_, 5, v_ref_3129_);
lean_ctor_set(v___x_3130_, 6, v_currNamespace_3119_);
lean_ctor_set(v___x_3130_, 7, v_openDecls_3120_);
lean_ctor_set(v___x_3130_, 8, v_initHeartbeats_3121_);
lean_ctor_set(v___x_3130_, 9, v_maxHeartbeats_3122_);
lean_ctor_set(v___x_3130_, 10, v_quotContext_3123_);
lean_ctor_set(v___x_3130_, 11, v_currMacroScope_3124_);
lean_ctor_set(v___x_3130_, 12, v_cancelTk_x3f_3126_);
lean_ctor_set(v___x_3130_, 13, v_inheritedTraceOptions_3128_);
lean_ctor_set_uint8(v___x_3130_, sizeof(void*)*14, v_diag_3125_);
lean_ctor_set_uint8(v___x_3130_, sizeof(void*)*14 + 1, v_suppressElabErrors_3127_);
lean_inc_ref(v___y_3096_);
v___x_3131_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_id_3110_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___x_3130_, v___y_3101_);
lean_dec_ref(v___x_3130_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref(v___x_3131_);
v_a_3104_ = v_a_3132_;
goto v___jp_3103_;
}
else
{
lean_dec_ref(v___y_3096_);
return v___x_3131_;
}
}
}
else
{
lean_object* v___x_3133_; 
lean_dec_ref(v___y_3096_);
v___x_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3133_, 0, v_b_3095_);
return v___x_3133_;
}
v___jp_3103_:
{
size_t v___x_3105_; size_t v___x_3106_; 
v___x_3105_ = ((size_t)1ULL);
v___x_3106_ = lean_usize_add(v_i_3093_, v___x_3105_);
v_i_3093_ = v___x_3106_;
v_b_3095_ = v_a_3104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3___boxed(lean_object* v_as_3134_, lean_object* v_i_3135_, lean_object* v_stop_3136_, lean_object* v_b_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
size_t v_i_boxed_3145_; size_t v_stop_boxed_3146_; lean_object* v_res_3147_; 
v_i_boxed_3145_ = lean_unbox_usize(v_i_3135_);
lean_dec(v_i_3135_);
v_stop_boxed_3146_ = lean_unbox_usize(v_stop_3136_);
lean_dec(v_stop_3136_);
v_res_3147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v_as_3134_, v_i_boxed_3145_, v_stop_boxed_3146_, v_b_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v_as_3134_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId(lean_object* v_currNamespace_3148_, lean_object* v_currLevelNames_3149_, lean_object* v_declId_3150_, lean_object* v_modifiers_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v___x_3159_; lean_object* v_fst_3160_; lean_object* v_snd_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3262_; 
v___x_3159_ = l_Lean_Elab_expandDeclIdCore(v_declId_3150_);
v_fst_3160_ = lean_ctor_get(v___x_3159_, 0);
v_snd_3161_ = lean_ctor_get(v___x_3159_, 1);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3163_ = v___x_3159_;
v_isShared_3164_ = v_isSharedCheck_3262_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_snd_3161_);
lean_inc(v_fst_3160_);
lean_dec(v___x_3159_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3262_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v_levelNames_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3219_; lean_object* v___y_3230_; uint8_t v___x_3241_; 
v___x_3241_ = l_Lean_Syntax_isNone(v_snd_3161_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; uint8_t v___x_3248_; 
v___x_3242_ = lean_unsigned_to_nat(1u);
v___x_3243_ = l_Lean_Syntax_getArg(v_snd_3161_, v___x_3242_);
lean_dec(v_snd_3161_);
v___x_3244_ = l_Lean_Syntax_getArgs(v___x_3243_);
lean_dec(v___x_3243_);
v___x_3245_ = lean_unsigned_to_nat(0u);
v___x_3246_ = ((lean_object*)(l_Lean_Elab_expandDeclIdCore___closed__0));
v___x_3247_ = lean_array_get_size(v___x_3244_);
v___x_3248_ = lean_nat_dec_lt(v___x_3245_, v___x_3247_);
if (v___x_3248_ == 0)
{
lean_dec_ref(v___x_3244_);
lean_del_object(v___x_3163_);
v___y_3230_ = v___x_3246_;
goto v___jp_3229_;
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3251_; 
v___x_3249_ = lean_box(v___x_3248_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 1, v___x_3246_);
lean_ctor_set(v___x_3163_, 0, v___x_3249_);
v___x_3251_ = v___x_3163_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v___x_3246_);
v___x_3251_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
uint8_t v___x_3252_; 
v___x_3252_ = lean_nat_dec_le(v___x_3247_, v___x_3247_);
if (v___x_3252_ == 0)
{
if (v___x_3248_ == 0)
{
lean_dec_ref(v___x_3251_);
lean_dec_ref(v___x_3244_);
v___y_3230_ = v___x_3246_;
goto v___jp_3229_;
}
else
{
size_t v___x_3253_; size_t v___x_3254_; lean_object* v___x_3255_; lean_object* v_snd_3256_; 
v___x_3253_ = ((size_t)0ULL);
v___x_3254_ = lean_usize_of_nat(v___x_3247_);
v___x_3255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3241_, v___x_3244_, v___x_3253_, v___x_3254_, v___x_3251_);
lean_dec_ref(v___x_3244_);
v_snd_3256_ = lean_ctor_get(v___x_3255_, 1);
lean_inc(v_snd_3256_);
lean_dec_ref(v___x_3255_);
v___y_3230_ = v_snd_3256_;
goto v___jp_3229_;
}
}
else
{
size_t v___x_3257_; size_t v___x_3258_; lean_object* v___x_3259_; lean_object* v_snd_3260_; 
v___x_3257_ = ((size_t)0ULL);
v___x_3258_ = lean_usize_of_nat(v___x_3247_);
v___x_3259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_3241_, v___x_3244_, v___x_3257_, v___x_3258_, v___x_3251_);
lean_dec_ref(v___x_3244_);
v_snd_3260_ = lean_ctor_get(v___x_3259_, 1);
lean_inc(v_snd_3260_);
lean_dec_ref(v___x_3259_);
v___y_3230_ = v_snd_3260_;
goto v___jp_3229_;
}
}
}
}
else
{
lean_del_object(v___x_3163_);
lean_dec(v_snd_3161_);
v_levelNames_3166_ = v_currLevelNames_3149_;
v___y_3167_ = v_a_3152_;
v___y_3168_ = v_a_3153_;
v___y_3169_ = v_a_3154_;
v___y_3170_ = v_a_3155_;
v___y_3171_ = v_a_3156_;
v___y_3172_ = v_a_3157_;
goto v___jp_3165_;
}
v___jp_3165_:
{
lean_object* v_fileName_3173_; lean_object* v_fileMap_3174_; lean_object* v_options_3175_; lean_object* v_currRecDepth_3176_; lean_object* v_maxRecDepth_3177_; lean_object* v_ref_3178_; lean_object* v_currNamespace_3179_; lean_object* v_openDecls_3180_; lean_object* v_initHeartbeats_3181_; lean_object* v_maxHeartbeats_3182_; lean_object* v_quotContext_3183_; lean_object* v_currMacroScope_3184_; uint8_t v_diag_3185_; lean_object* v_cancelTk_x3f_3186_; uint8_t v_suppressElabErrors_3187_; lean_object* v_inheritedTraceOptions_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3217_; 
v_fileName_3173_ = lean_ctor_get(v___y_3171_, 0);
v_fileMap_3174_ = lean_ctor_get(v___y_3171_, 1);
v_options_3175_ = lean_ctor_get(v___y_3171_, 2);
v_currRecDepth_3176_ = lean_ctor_get(v___y_3171_, 3);
v_maxRecDepth_3177_ = lean_ctor_get(v___y_3171_, 4);
v_ref_3178_ = lean_ctor_get(v___y_3171_, 5);
v_currNamespace_3179_ = lean_ctor_get(v___y_3171_, 6);
v_openDecls_3180_ = lean_ctor_get(v___y_3171_, 7);
v_initHeartbeats_3181_ = lean_ctor_get(v___y_3171_, 8);
v_maxHeartbeats_3182_ = lean_ctor_get(v___y_3171_, 9);
v_quotContext_3183_ = lean_ctor_get(v___y_3171_, 10);
v_currMacroScope_3184_ = lean_ctor_get(v___y_3171_, 11);
v_diag_3185_ = lean_ctor_get_uint8(v___y_3171_, sizeof(void*)*14);
v_cancelTk_x3f_3186_ = lean_ctor_get(v___y_3171_, 12);
v_suppressElabErrors_3187_ = lean_ctor_get_uint8(v___y_3171_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3188_ = lean_ctor_get(v___y_3171_, 13);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___y_3171_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3190_ = v___y_3171_;
v_isShared_3191_ = v_isSharedCheck_3217_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_inheritedTraceOptions_3188_);
lean_inc(v_cancelTk_x3f_3186_);
lean_inc(v_currMacroScope_3184_);
lean_inc(v_quotContext_3183_);
lean_inc(v_maxHeartbeats_3182_);
lean_inc(v_initHeartbeats_3181_);
lean_inc(v_openDecls_3180_);
lean_inc(v_currNamespace_3179_);
lean_inc(v_ref_3178_);
lean_inc(v_maxRecDepth_3177_);
lean_inc(v_currRecDepth_3176_);
lean_inc(v_options_3175_);
lean_inc(v_fileMap_3174_);
lean_inc(v_fileName_3173_);
lean_dec(v___y_3171_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3217_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v_ref_3192_; lean_object* v___x_3194_; 
v_ref_3192_ = l_Lean_replaceRef(v_declId_3150_, v_ref_3178_);
lean_dec(v_ref_3178_);
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 5, v_ref_3192_);
v___x_3194_ = v___x_3190_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_fileName_3173_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v_fileMap_3174_);
lean_ctor_set(v_reuseFailAlloc_3216_, 2, v_options_3175_);
lean_ctor_set(v_reuseFailAlloc_3216_, 3, v_currRecDepth_3176_);
lean_ctor_set(v_reuseFailAlloc_3216_, 4, v_maxRecDepth_3177_);
lean_ctor_set(v_reuseFailAlloc_3216_, 5, v_ref_3192_);
lean_ctor_set(v_reuseFailAlloc_3216_, 6, v_currNamespace_3179_);
lean_ctor_set(v_reuseFailAlloc_3216_, 7, v_openDecls_3180_);
lean_ctor_set(v_reuseFailAlloc_3216_, 8, v_initHeartbeats_3181_);
lean_ctor_set(v_reuseFailAlloc_3216_, 9, v_maxHeartbeats_3182_);
lean_ctor_set(v_reuseFailAlloc_3216_, 10, v_quotContext_3183_);
lean_ctor_set(v_reuseFailAlloc_3216_, 11, v_currMacroScope_3184_);
lean_ctor_set(v_reuseFailAlloc_3216_, 12, v_cancelTk_x3f_3186_);
lean_ctor_set(v_reuseFailAlloc_3216_, 13, v_inheritedTraceOptions_3188_);
lean_ctor_set_uint8(v_reuseFailAlloc_3216_, sizeof(void*)*14, v_diag_3185_);
lean_ctor_set_uint8(v_reuseFailAlloc_3216_, sizeof(void*)*14 + 1, v_suppressElabErrors_3187_);
v___x_3194_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(v_currNamespace_3148_, v_modifiers_3151_, v_fst_3160_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___x_3194_, v___y_3172_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3207_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3198_ = v___x_3195_;
v_isShared_3199_ = v_isSharedCheck_3207_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3195_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3207_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v_fst_3200_; lean_object* v_snd_3201_; lean_object* v_docString_x3f_3202_; lean_object* v___x_3203_; lean_object* v___x_3205_; 
v_fst_3200_ = lean_ctor_get(v_a_3196_, 0);
lean_inc(v_fst_3200_);
v_snd_3201_ = lean_ctor_get(v_a_3196_, 1);
lean_inc(v_snd_3201_);
lean_dec(v_a_3196_);
v_docString_x3f_3202_ = lean_ctor_get(v_modifiers_3151_, 1);
lean_inc(v_docString_x3f_3202_);
v___x_3203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3203_, 0, v_snd_3201_);
lean_ctor_set(v___x_3203_, 1, v_fst_3200_);
lean_ctor_set(v___x_3203_, 2, v_levelNames_3166_);
lean_ctor_set(v___x_3203_, 3, v_docString_x3f_3202_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 0, v___x_3203_);
v___x_3205_ = v___x_3198_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec(v_levelNames_3166_);
v_a_3208_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3195_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3195_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
}
v___jp_3218_:
{
if (lean_obj_tag(v___y_3219_) == 0)
{
lean_object* v_a_3220_; 
v_a_3220_ = lean_ctor_get(v___y_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref(v___y_3219_);
v_levelNames_3166_ = v_a_3220_;
v___y_3167_ = v_a_3152_;
v___y_3168_ = v_a_3153_;
v___y_3169_ = v_a_3154_;
v___y_3170_ = v_a_3155_;
v___y_3171_ = v_a_3156_;
v___y_3172_ = v_a_3157_;
goto v___jp_3165_;
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v_fst_3160_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec(v_currNamespace_3148_);
v_a_3221_ = lean_ctor_get(v___y_3219_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___y_3219_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___y_3219_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___y_3219_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
v___jp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; uint8_t v___x_3233_; 
v___x_3231_ = lean_unsigned_to_nat(0u);
v___x_3232_ = lean_array_get_size(v___y_3230_);
v___x_3233_ = lean_nat_dec_lt(v___x_3231_, v___x_3232_);
if (v___x_3233_ == 0)
{
lean_dec_ref(v___y_3230_);
v_levelNames_3166_ = v_currLevelNames_3149_;
v___y_3167_ = v_a_3152_;
v___y_3168_ = v_a_3153_;
v___y_3169_ = v_a_3154_;
v___y_3170_ = v_a_3155_;
v___y_3171_ = v_a_3156_;
v___y_3172_ = v_a_3157_;
goto v___jp_3165_;
}
else
{
uint8_t v___x_3234_; 
v___x_3234_ = lean_nat_dec_le(v___x_3232_, v___x_3232_);
if (v___x_3234_ == 0)
{
if (v___x_3233_ == 0)
{
lean_dec_ref(v___y_3230_);
v_levelNames_3166_ = v_currLevelNames_3149_;
v___y_3167_ = v_a_3152_;
v___y_3168_ = v_a_3153_;
v___y_3169_ = v_a_3154_;
v___y_3170_ = v_a_3155_;
v___y_3171_ = v_a_3156_;
v___y_3172_ = v_a_3157_;
goto v___jp_3165_;
}
else
{
size_t v___x_3235_; size_t v___x_3236_; lean_object* v___x_3237_; 
v___x_3235_ = ((size_t)0ULL);
v___x_3236_ = lean_usize_of_nat(v___x_3232_);
lean_inc_ref(v_a_3152_);
v___x_3237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3230_, v___x_3235_, v___x_3236_, v_currLevelNames_3149_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_);
lean_dec_ref(v___y_3230_);
v___y_3219_ = v___x_3237_;
goto v___jp_3218_;
}
}
else
{
size_t v___x_3238_; size_t v___x_3239_; lean_object* v___x_3240_; 
v___x_3238_ = ((size_t)0ULL);
v___x_3239_ = lean_usize_of_nat(v___x_3232_);
lean_inc_ref(v_a_3152_);
v___x_3240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_3230_, v___x_3238_, v___x_3239_, v_currLevelNames_3149_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_);
lean_dec_ref(v___y_3230_);
v___y_3219_ = v___x_3240_;
goto v___jp_3218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___boxed(lean_object* v_currNamespace_3263_, lean_object* v_currLevelNames_3264_, lean_object* v_declId_3265_, lean_object* v_modifiers_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Lean_Elab_expandDeclId(v_currNamespace_3263_, v_currLevelNames_3264_, v_declId_3265_, v_modifiers_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_);
lean_dec_ref(v_modifiers_3266_);
lean_dec(v_declId_3265_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(lean_object* v_00_u03b1_3275_, lean_object* v_u_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___boxed(lean_object* v_00_u03b1_3285_, lean_object* v_u_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(v_00_u03b1_3285_, v_u_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec(v___y_3288_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(lean_object* v_00_u03b1_3295_, lean_object* v_msg_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3305_, lean_object* v_msg_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(v_00_u03b1_3305_, v_msg_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(lean_object* v_msgData_3315_, lean_object* v_macroStack_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_3315_, v_macroStack_3316_, v___y_3321_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_3325_, lean_object* v_macroStack_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(v_msgData_3325_, v_macroStack_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(lean_object* v_t_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_3335_, v___y_3341_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___boxed(lean_object* v_t_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(v_t_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(lean_object* v_env_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_3353_, v___y_3357_, v___y_3359_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___boxed(lean_object* v_env_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(v_env_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(lean_object* v_00_u03b1_3371_, lean_object* v_env_3372_, lean_object* v_x_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v___x_3381_; 
v___x_3381_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_3372_, v_x_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3382_, lean_object* v_env_3383_, lean_object* v_x_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(v_00_u03b1_3382_, v_env_3383_, v_x_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(lean_object* v_00_u03b1_3393_, lean_object* v_constName_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___boxed(lean_object* v_00_u03b1_3403_, lean_object* v_constName_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(v_00_u03b1_3403_, v_constName_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
lean_dec(v___y_3410_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(lean_object* v_00_u03b1_3413_, lean_object* v_ref_3414_, lean_object* v_constName_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_3414_, v_constName_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___boxed(lean_object* v_00_u03b1_3424_, lean_object* v_ref_3425_, lean_object* v_constName_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(v_00_u03b1_3424_, v_ref_3425_, v_constName_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
lean_dec(v___y_3432_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec(v_ref_3425_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(lean_object* v_00_u03b1_3435_, lean_object* v_ref_3436_, lean_object* v_msg_3437_, lean_object* v_declHint_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v___x_3446_; 
v___x_3446_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_3436_, v_msg_3437_, v_declHint_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___boxed(lean_object* v_00_u03b1_3447_, lean_object* v_ref_3448_, lean_object* v_msg_3449_, lean_object* v_declHint_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(v_00_u03b1_3447_, v_ref_3448_, v_msg_3449_, v_declHint_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec(v_ref_3448_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(lean_object* v_msg_3459_, lean_object* v_declHint_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v___x_3468_; 
v___x_3468_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_3459_, v_declHint_3460_, v___y_3466_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___boxed(lean_object* v_msg_3469_, lean_object* v_declHint_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(v_msg_3469_, v_declHint_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(lean_object* v_00_u03b1_3479_, lean_object* v_ref_3480_, lean_object* v_msg_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v___x_3489_; 
v___x_3489_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_3480_, v_msg_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___boxed(lean_object* v_00_u03b1_3490_, lean_object* v_ref_3491_, lean_object* v_msg_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(v_00_u03b1_3490_, v_ref_3491_, v_msg_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec(v_ref_3491_);
return v_res_3500_;
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
