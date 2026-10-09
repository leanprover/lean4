// Lean compiler output
// Module: Init.Meta.Defs
// Imports: import all Init.Prelude public import Init.Data.Array.Basic public import Init.MetaTypes import Init.Data.Array.GetLit import Init.Data.Char.Basic meta import Init.MetaTypes import Init.WFTactics
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_any(lean_object*, lean_object*);
lean_object* lean_substring_drop(lean_object*, lean_object*);
uint8_t lean_substring_all(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_string_contains(lean_object*, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t lean_string_isprefixof(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_string_isempty(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint32_t l_Char_ofNat(lean_object*);
lean_object* lean_string_nextwhile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instReprSourceInfo_repr(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_substring_tostring(lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*, uint8_t);
uint32_t lean_substring_front(lean_object*);
uint8_t lean_substring_isempty(lean_object*);
lean_object* lean_substring_takewhile(lean_object*, lean_object*);
lean_object* lean_substring_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_pos_min(lean_object*, lean_object*);
lean_object* lean_substring_prev(lean_object*, lean_object*);
uint32_t lean_substring_get(lean_object*, lean_object*);
uint32_t lean_string_front(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(lean_object*);
lean_object* lean_string_drop(lean_object*, lean_object*);
lean_object* lean_string_dropright(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_substring_beq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Lean_Macro_expandMacro_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* lean_nat_pred(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Char_quote(uint32_t);
lean_object* lean_string_trim(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getTrailing_x3f(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntaxArray_mkImpl___boxed(lean_object*, lean_object*);
lean_object* lean_string_capitalize(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* lean_version_get_major(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMajor___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_major___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_version_major___closed__0;
LEAN_EXPORT lean_object* l_Lean_version_major;
lean_object* lean_version_get_minor(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMinor___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_minor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_version_minor___closed__0;
LEAN_EXPORT lean_object* l_Lean_version_minor;
lean_object* lean_version_get_patch(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getPatch___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_patch___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_version_patch___closed__0;
LEAN_EXPORT lean_object* l_Lean_version_patch;
lean_object* lean_get_githash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getGithash___boxed(lean_object*);
static lean_once_cell_t l_Lean_githash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_githash___closed__0;
LEAN_EXPORT lean_object* l_Lean_githash;
uint8_t lean_version_get_is_release(lean_object*);
LEAN_EXPORT lean_object* l_Lean_version_getIsRelease___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_isRelease___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_version_isRelease___closed__0;
LEAN_EXPORT uint8_t l_Lean_version_isRelease;
lean_object* lean_version_get_special_desc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_version_getSpecialDesc___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_specialDesc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_version_specialDesc___closed__0;
LEAN_EXPORT lean_object* l_Lean_version_specialDesc;
static lean_once_cell_t l_Lean_versionStringCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__0;
static const lean_string_object l_Lean_versionStringCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_versionStringCore___closed__1 = (const lean_object*)&l_Lean_versionStringCore___closed__1_value;
static lean_once_cell_t l_Lean_versionStringCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__2;
static lean_once_cell_t l_Lean_versionStringCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__3;
static lean_once_cell_t l_Lean_versionStringCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__4;
static lean_once_cell_t l_Lean_versionStringCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__5;
static lean_once_cell_t l_Lean_versionStringCore___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__6;
static lean_once_cell_t l_Lean_versionStringCore___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__7;
LEAN_EXPORT lean_object* l_Lean_versionStringCore;
static const lean_string_object l_Lean_versionString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_versionString___closed__0 = (const lean_object*)&l_Lean_versionString___closed__0_value;
static lean_once_cell_t l_Lean_versionString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_versionString___closed__1;
static const lean_string_object l_Lean_versionString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_versionString___closed__2 = (const lean_object*)&l_Lean_versionString___closed__2_value;
static lean_once_cell_t l_Lean_versionString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionString___closed__3;
static lean_once_cell_t l_Lean_versionString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionString___closed__4;
static const lean_string_object l_Lean_versionString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", commit "};
static const lean_object* l_Lean_versionString___closed__5 = (const lean_object*)&l_Lean_versionString___closed__5_value;
static lean_once_cell_t l_Lean_versionString___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionString___closed__6;
static lean_once_cell_t l_Lean_versionString___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionString___closed__7;
LEAN_EXPORT lean_object* l_Lean_versionString;
static const lean_string_object l_Lean_origin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "leanprover/lean4"};
static const lean_object* l_Lean_origin___closed__0 = (const lean_object*)&l_Lean_origin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_origin = (const lean_object*)&l_Lean_origin___closed__0_value;
static const lean_string_object l_Lean_toolchain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_toolchain___closed__0 = (const lean_object*)&l_Lean_toolchain___closed__0_value;
static lean_once_cell_t l_Lean_toolchain___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__1;
static lean_once_cell_t l_Lean_toolchain___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__2;
static const lean_string_object l_Lean_toolchain___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":v"};
static const lean_object* l_Lean_toolchain___closed__3 = (const lean_object*)&l_Lean_toolchain___closed__3_value;
static lean_once_cell_t l_Lean_toolchain___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__4;
static lean_once_cell_t l_Lean_toolchain___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__5;
static lean_once_cell_t l_Lean_toolchain___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__6;
static lean_once_cell_t l_Lean_toolchain___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__7;
LEAN_EXPORT lean_object* l_Lean_toolchain;
uint8_t lean_internal_is_stage0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Internal_isStage0___boxed(lean_object*);
uint8_t lean_internal_has_llvm_backend(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Internal_hasLLVMBackend___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isGreek(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isGreek___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isLetterLike(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isLetterLike___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isNumericSubscript(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isNumericSubscript___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isSubScriptAlnum(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIdFirst(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isIdFirst___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIdFirstAscii(uint8_t);
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIdRest(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIdRestAscii(uint8_t);
LEAN_EXPORT lean_object* l_Lean_isIdRestAscii___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_idBeginEscape;
LEAN_EXPORT uint32_t l_Lean_idEndEscape;
LEAN_EXPORT uint8_t l_Lean_isIdBeginEscape(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isIdBeginEscape___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIdEndEscape(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isIdEndEscape___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getRoot___boxed(lean_object*);
static const lean_string_object l_Lean_Name_isInaccessibleUserName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "_inaccessible"};
static const lean_object* l_Lean_Name_isInaccessibleUserName___closed__0 = (const lean_object*)&l_Lean_Name_isInaccessibleUserName___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Name_isInaccessibleUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isInaccessibleUserName___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_isIdRest___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "«"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "»"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___boxed(lean_object*);
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_isIdEndEscape___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object*);
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0_value;
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed(lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0_value;
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3_value;
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_hasNum(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_hasNum___boxed(lean_object*);
static const lean_string_object l_Lean_Name_reprPrec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Name.anonymous"};
static const lean_object* l_Lean_Name_reprPrec___closed__0 = (const lean_object*)&l_Lean_Name_reprPrec___closed__0_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__0_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__1 = (const lean_object*)&l_Lean_Name_reprPrec___closed__1_value;
static const lean_string_object l_Lean_Name_reprPrec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Name_reprPrec___closed__2 = (const lean_object*)&l_Lean_Name_reprPrec___closed__2_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__2_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__3 = (const lean_object*)&l_Lean_Name_reprPrec___closed__3_value;
static const lean_string_object l_Lean_Name_reprPrec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Name.mkStr "};
static const lean_object* l_Lean_Name_reprPrec___closed__4 = (const lean_object*)&l_Lean_Name_reprPrec___closed__4_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__4_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__5 = (const lean_object*)&l_Lean_Name_reprPrec___closed__5_value;
static const lean_string_object l_Lean_Name_reprPrec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Name_reprPrec___closed__6 = (const lean_object*)&l_Lean_Name_reprPrec___closed__6_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__6_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__7 = (const lean_object*)&l_Lean_Name_reprPrec___closed__7_value;
static const lean_string_object l_Lean_Name_reprPrec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Name.mkNum "};
static const lean_object* l_Lean_Name_reprPrec___closed__8 = (const lean_object*)&l_Lean_Name_reprPrec___closed__8_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__8_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__9 = (const lean_object*)&l_Lean_Name_reprPrec___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Name_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_reprPrec___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Name_instRepr___closed__0 = (const lean_object*)&l_Lean_Name_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Name_instRepr = (const lean_object*)&l_Lean_Name_instRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_name_append_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_instDecidableEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2_value;
static const lean_string_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5_value;
static const lean_string_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7;
static lean_once_cell_t l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Lean_Syntax_instReprPreresolved_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Syntax.Preresolved.namespace"};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__0 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instReprPreresolved_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__1 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_instReprPreresolved_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__2 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__2_value;
static lean_once_cell_t l_Lean_Syntax_instReprPreresolved_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__3;
static lean_once_cell_t l_Lean_Syntax_instReprPreresolved_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__4;
static const lean_string_object l_Lean_Syntax_instReprPreresolved_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Syntax.Preresolved.decl"};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__5 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__5_value;
static const lean_ctor_object l_Lean_Syntax_instReprPreresolved_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__5_value)}};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__6 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__6_value;
static const lean_ctor_object l_Lean_Syntax_instReprPreresolved_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__7 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instReprPreresolved___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instReprPreresolved_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instReprPreresolved___closed__0 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instReprPreresolved = (const lean_object*)&l_Lean_Syntax_instReprPreresolved___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object*);
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Syntax.missing"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__0 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__1 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__1_value;
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Syntax.node"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__2 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__2_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__2_value)}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__3 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__3_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__4 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__4_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1;
static lean_once_cell_t l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2;
static const lean_ctor_object l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Syntax.atom"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__5 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__5_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__5_value)}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__6 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__6_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__7 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__7_value;
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Syntax.ident"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__8 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__8_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__8_value)}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__9 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__9_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__10 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__10_value;
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ".toRawSubstring"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__11 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instRepr_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instRepr___closed__0 = (const lean_object*)&l_Lean_Syntax_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instRepr = (const lean_object*)&l_Lean_Syntax_instRepr___closed__0_value;
static const lean_string_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "raw"};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7;
static const lean_string_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9;
static lean_once_cell_t l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0 = (const lean_object*)&l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg();
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg();
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_TSyntax_instCoeIdentTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TSyntax_instCoeIdentTerm___closed__0 = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeIdentTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeStrLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeNameLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeScientificLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeNumLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeCharLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeIdentLevel = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeNumLitPrio = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeNumLitPrec = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg();
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instBEqPreresolved___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instBEqPreresolved_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instBEqPreresolved___closed__0 = (const lean_object*)&l_Lean_Syntax_instBEqPreresolved___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instBEqPreresolved = (const lean_object*)&l_Lean_Syntax_instBEqPreresolved___closed__0_value;
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_structEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instBEq___closed__0 = (const lean_object*)&l_Lean_Syntax_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instBEq = (const lean_object*)&l_Lean_Syntax_instBEq___closed__0_value;
static const lean_closure_object l_Lean_Syntax_instBEqTSyntax___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_structEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instBEqTSyntax___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instBEqTSyntax___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg();
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_expandMacros___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_expandMacros___lam__0___closed__0 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value;
static const lean_string_object l_Lean_expandMacros___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_expandMacros___lam__0___closed__1 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value;
static const lean_string_object l_Lean_expandMacros___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_expandMacros___lam__0___closed__2 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value;
static const lean_string_object l_Lean_expandMacros___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lean_expandMacros___lam__0___closed__3 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_expandMacros___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_expandMacros___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_expandMacros___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_expandMacros___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_expandMacros___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_expandMacros___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_expandMacros___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_expandMacros___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Lean_expandMacros___lam__0___closed__4 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__4_value;
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_expandMacros___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_expandMacros___closed__0 = (const lean_object*)&l_Lean_expandMacros___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkMarkdownDocCommentFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_mkMarkdownDocCommentFrom___closed__0 = (const lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__0_value;
static const lean_string_object l_Lean_mkMarkdownDocCommentFrom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "commentBody"};
static const lean_object* l_Lean_mkMarkdownDocCommentFrom___closed__1 = (const lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__1_value;
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__2_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__2_value_aux_1),((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__2_value_aux_2),((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 50, 60, 220, 73, 28, 0, 197)}};
static const lean_object* l_Lean_mkMarkdownDocCommentFrom___closed__2 = (const lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__2_value;
static const lean_string_object l_Lean_mkMarkdownDocCommentFrom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-/"};
static const lean_object* l_Lean_mkMarkdownDocCommentFrom___closed__3 = (const lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__3_value;
static const lean_string_object l_Lean_mkMarkdownDocCommentFrom___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_mkMarkdownDocCommentFrom___closed__4 = (const lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__4_value;
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__5_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__5_value_aux_1),((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_mkMarkdownDocCommentFrom___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__5_value_aux_2),((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__4_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_mkMarkdownDocCommentFrom___closed__5 = (const lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__5_value;
static const lean_string_object l_Lean_mkMarkdownDocCommentFrom___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "/--"};
static const lean_object* l_Lean_mkMarkdownDocCommentFrom___closed__6 = (const lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocComment(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCIdentFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_internal"};
static const lean_object* l_Lean_mkCIdentFrom___closed__0 = (const lean_object*)&l_Lean_mkCIdentFrom___closed__0_value;
static const lean_ctor_object l_Lean_mkCIdentFrom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCIdentFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 131, 204, 40, 20, 233, 244, 88)}};
static const lean_object* l_Lean_mkCIdentFrom___closed__1 = (const lean_object*)&l_Lean_mkCIdentFrom___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdent(lean_object*);
static const lean_string_object l_Lean_mkGroupNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_mkGroupNode___closed__0 = (const lean_object*)&l_Lean_mkGroupNode___closed__0_value;
static const lean_ctor_object l_Lean_mkGroupNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkGroupNode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_mkGroupNode___closed__1 = (const lean_object*)&l_Lean_mkGroupNode___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_mkSepArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_mkSepArray___closed__0 = (const lean_object*)&l_Lean_mkSepArray___closed__0_value;
static const lean_ctor_object l_Lean_mkSepArray___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkSepArray___closed__0_value)}};
static const lean_object* l_Lean_mkSepArray___closed__1 = (const lean_object*)&l_Lean_mkSepArray___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkOptionalNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_mkOptionalNode___closed__0 = (const lean_object*)&l_Lean_mkOptionalNode___closed__0_value;
static const lean_ctor_object l_Lean_mkOptionalNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkOptionalNode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_mkOptionalNode___closed__1 = (const lean_object*)&l_Lean_mkOptionalNode___closed__1_value;
static const lean_ctor_object l_Lean_mkOptionalNode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_mkOptionalNode___closed__1_value),((lean_object*)&l_Lean_mkSepArray___closed__0_value)}};
static const lean_object* l_Lean_mkOptionalNode___closed__2 = (const lean_object*)&l_Lean_mkOptionalNode___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object*);
static const lean_string_object l_Lean_mkHole___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_mkHole___closed__0 = (const lean_object*)&l_Lean_mkHole___closed__0_value;
static const lean_ctor_object l_Lean_mkHole___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_mkHole___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkHole___closed__1_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_mkHole___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkHole___closed__1_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_mkHole___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkHole___closed__1_value_aux_2),((lean_object*)&l_Lean_mkHole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_mkHole___closed__1 = (const lean_object*)&l_Lean_mkHole___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Syntax_SepArray_ofElems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_SepArray_ofElems___closed__0 = (const lean_object*)&l_Lean_Syntax_SepArray_ofElems___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_SepArray_ofElems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_mkOptionalNode___closed__1_value),((lean_object*)&l_Lean_Syntax_SepArray_ofElems___closed__0_value)}};
static const lean_object* l_Lean_Syntax_SepArray_ofElems___closed__1 = (const lean_object*)&l_Lean_Syntax_SepArray_ofElems___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Syntax_mkApp___closed__0 = (const lean_object*)&l_Lean_Syntax_mkApp___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkApp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_mkApp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkApp___closed__1_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Syntax_mkApp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkApp___closed__1_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Syntax_mkApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkApp___closed__1_value_aux_2),((lean_object*)&l_Lean_Syntax_mkApp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Syntax_mkApp___closed__1 = (const lean_object*)&l_Lean_Syntax_mkApp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkCharLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l_Lean_Syntax_mkCharLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkCharLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkCharLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkCharLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l_Lean_Syntax_mkCharLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkCharLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkStrLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Syntax_mkStrLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkStrLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkStrLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkStrLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Syntax_mkStrLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkStrLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkNumLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Syntax_mkNumLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkNumLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkNumLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkNumLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Syntax_mkNumLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkNumLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkScientificLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l_Lean_Syntax_mkScientificLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkScientificLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkScientificLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkScientificLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l_Lean_Syntax_mkScientificLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkScientificLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkNameLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Syntax_mkNameLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkNameLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkNameLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkNameLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_Syntax_mkNameLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkNameLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Syntax_decodeNatLitVal_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_decodeNatLitVal_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Syntax_isFieldIdx_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fieldIdx"};
static const lean_object* l_Lean_Syntax_isFieldIdx_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_isFieldIdx_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_isFieldIdx_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_isFieldIdx_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 141, 165, 29, 238, 211, 61, 163)}};
static const lean_object* l_Lean_Syntax_isFieldIdx_x3f___closed__1 = (const lean_object*)&l_Lean_Syntax_isFieldIdx_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_decodeStringGap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_decodeStringGap___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_decodeStringGap___closed__0 = (const lean_object*)&l_Lean_Syntax_decodeStringGap___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t, uint8_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object*);
static const lean_string_object l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Init.Meta.Defs"};
static const lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0 = (const lean_object*)&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0_value;
static const lean_string_object l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Substring.Raw.toName"};
static const lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1 = (const lean_object*)&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1_value;
static const lean_string_object l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2 = (const lean_object*)&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2_value;
static lean_once_cell_t l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3;
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object*);
LEAN_EXPORT lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object*);
static const lean_ctor_object l_Lean_TSyntax_getScientific___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_TSyntax_getScientific___closed__0 = (const lean_object*)&l_Lean_TSyntax_getScientific___closed__0_value;
static const lean_ctor_object l_Lean_TSyntax_getScientific___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_TSyntax_getScientific___closed__0_value)}};
static const lean_object* l_Lean_TSyntax_getScientific___closed__1 = (const lean_object*)&l_Lean_TSyntax_getScientific___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instQuoteTermMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_instQuoteTermMkStr1___closed__0 = (const lean_object*)&l_Lean_instQuoteTermMkStr1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteTermMkStr1 = (const lean_object*)&l_Lean_instQuoteTermMkStr1___closed__0_value;
static const lean_string_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__0 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__0_value;
static const lean_string_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__1 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__2 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__3;
static const lean_string_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__4 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__5 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instQuoteBoolMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteBoolMkStr1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteBoolMkStr1___closed__0 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteBoolMkStr1 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instQuoteCharCharLitKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteCharCharLitKind___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteCharCharLitKind___closed__0 = (const lean_object*)&l_Lean_instQuoteCharCharLitKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteCharCharLitKind = (const lean_object*)&l_Lean_instQuoteCharCharLitKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object*);
static const lean_closure_object l_Lean_instQuoteStringStrLitKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteStringStrLitKind___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteStringStrLitKind___closed__0 = (const lean_object*)&l_Lean_instQuoteStringStrLitKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteStringStrLitKind = (const lean_object*)&l_Lean_instQuoteStringStrLitKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object*);
static const lean_closure_object l_Lean_instQuoteNatNumLitKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteNatNumLitKind___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteNatNumLitKind___closed__0 = (const lean_object*)&l_Lean_instQuoteNatNumLitKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteNatNumLitKind = (const lean_object*)&l_Lean_instQuoteNatNumLitKind___closed__0_value;
static const lean_string_object l_Lean_instQuoteRawMkStr1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_instQuoteRawMkStr1___lam__0___closed__0 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__0_value;
static const lean_string_object l_Lean_instQuoteRawMkStr1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "toRawSubstring'"};
static const lean_object* l_Lean_instQuoteRawMkStr1___lam__0___closed__1 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instQuoteRawMkStr1___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_Lean_instQuoteRawMkStr1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(190, 31, 121, 163, 121, 213, 247, 150)}};
static const lean_object* l_Lean_instQuoteRawMkStr1___lam__0___closed__2 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object*);
static const lean_closure_object l_Lean_instQuoteRawMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteRawMkStr1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteRawMkStr1___closed__0 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteRawMkStr1 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
static const lean_string_object l_Lean_quoteNameMk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l_Lean_quoteNameMk___closed__0 = (const lean_object*)&l_Lean_quoteNameMk___closed__0_value;
static const lean_string_object l_Lean_quoteNameMk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "anonymous"};
static const lean_object* l_Lean_quoteNameMk___closed__1 = (const lean_object*)&l_Lean_quoteNameMk___closed__1_value;
static const lean_ctor_object l_Lean_quoteNameMk___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__2_value_aux_0),((lean_object*)&l_Lean_quoteNameMk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__2_value_aux_1),((lean_object*)&l_Lean_quoteNameMk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(155, 163, 3, 148, 15, 163, 84, 121)}};
static const lean_object* l_Lean_quoteNameMk___closed__2 = (const lean_object*)&l_Lean_quoteNameMk___closed__2_value;
static lean_once_cell_t l_Lean_quoteNameMk___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_quoteNameMk___closed__3;
static const lean_string_object l_Lean_quoteNameMk___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mkStr"};
static const lean_object* l_Lean_quoteNameMk___closed__4 = (const lean_object*)&l_Lean_quoteNameMk___closed__4_value;
static const lean_ctor_object l_Lean_quoteNameMk___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__5_value_aux_0),((lean_object*)&l_Lean_quoteNameMk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__5_value_aux_1),((lean_object*)&l_Lean_quoteNameMk___closed__4_value),LEAN_SCALAR_PTR_LITERAL(66, 239, 13, 154, 0, 241, 98, 75)}};
static const lean_object* l_Lean_quoteNameMk___closed__5 = (const lean_object*)&l_Lean_quoteNameMk___closed__5_value;
static const lean_string_object l_Lean_quoteNameMk___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mkNum"};
static const lean_object* l_Lean_quoteNameMk___closed__6 = (const lean_object*)&l_Lean_quoteNameMk___closed__6_value;
static const lean_ctor_object l_Lean_quoteNameMk___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__7_value_aux_0),((lean_object*)&l_Lean_quoteNameMk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__7_value_aux_1),((lean_object*)&l_Lean_quoteNameMk___closed__6_value),LEAN_SCALAR_PTR_LITERAL(247, 141, 7, 17, 149, 107, 178, 15)}};
static const lean_object* l_Lean_quoteNameMk___closed__7 = (const lean_object*)&l_Lean_quoteNameMk___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object*);
static const lean_string_object l_Lean_instQuoteNameMkStr1___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean_instQuoteNameMkStr1___private__1___closed__0 = (const lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__0_value;
static const lean_ctor_object l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_instQuoteNameMkStr1___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_2),((lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lean_instQuoteNameMkStr1___private__1___closed__1 = (const lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object*);
static const lean_closure_object l_Lean_instQuoteNameMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteNameMkStr1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteNameMkStr1___closed__0 = (const lean_object*)&l_Lean_instQuoteNameMkStr1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteNameMkStr1 = (const lean_object*)&l_Lean_instQuoteNameMkStr1___closed__0_value;
static const lean_string_object l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mkArray"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Option_hasQuote___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Option_hasQuote___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Option_hasQuote___redArg___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Option_hasQuote___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__3;
static const lean_string_object l_Lean_Option_hasQuote___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Option_hasQuote___redArg___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Option_hasQuote___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_evalPrec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected precedence"};
static const lean_object* l_Lean_evalPrec___closed__0 = (const lean_object*)&l_Lean_evalPrec___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_evalPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unexpected priority"};
static const lean_object* l_Lean_evalPrio___closed__0 = (const lean_object*)&l_Lean_evalPrio___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_getSepElems___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_getSepElems___redArg___closed__0 = (const lean_object*)&l_Array_getSepElems___redArg___closed__0_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__1 = (const lean_object*)&l_Array_getSepElems___redArg___closed__1_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__2 = (const lean_object*)&l_Array_getSepElems___redArg___closed__2_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__3 = (const lean_object*)&l_Array_getSepElems___redArg___closed__3_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__4 = (const lean_object*)&l_Array_getSepElems___redArg___closed__4_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__5 = (const lean_object*)&l_Array_getSepElems___redArg___closed__5_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__6 = (const lean_object*)&l_Array_getSepElems___redArg___closed__6_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__7 = (const lean_object*)&l_Array_getSepElems___redArg___closed__7_value;
static const lean_ctor_object l_Array_getSepElems___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_getSepElems___redArg___closed__1_value),((lean_object*)&l_Array_getSepElems___redArg___closed__2_value)}};
static const lean_object* l_Array_getSepElems___redArg___closed__8 = (const lean_object*)&l_Array_getSepElems___redArg___closed__8_value;
static const lean_ctor_object l_Array_getSepElems___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_getSepElems___redArg___closed__8_value),((lean_object*)&l_Array_getSepElems___redArg___closed__3_value),((lean_object*)&l_Array_getSepElems___redArg___closed__4_value),((lean_object*)&l_Array_getSepElems___redArg___closed__5_value),((lean_object*)&l_Array_getSepElems___redArg___closed__6_value)}};
static const lean_object* l_Array_getSepElems___redArg___closed__9 = (const lean_object*)&l_Array_getSepElems___redArg___closed__9_value;
static const lean_ctor_object l_Array_getSepElems___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_getSepElems___redArg___closed__9_value),((lean_object*)&l_Array_getSepElems___redArg___closed__7_value)}};
static const lean_object* l_Array_getSepElems___redArg___closed__10 = (const lean_object*)&l_Array_getSepElems___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Syntax_instEmptyCollectionSepArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___closed__0;
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0;
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg();
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg();
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object*);
static const lean_string_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_mkMarkdownDocCommentFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instCoeTermTSyntaxConsSyntaxNodeKindMkStr4Nil = (const lean_object*)&l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object*);
static const lean_string_object l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "interpolatedStrLitKind"};
static const lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 181, 130, 246, 88, 58, 26, 43)}};
static const lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1 = (const lean_object*)&l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_++_"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 69, 86, 178, 149, 48, 216, 23)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "++"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_TSyntax_expandInterpolatedStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__0 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__0_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__1 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__1_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_2),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__2 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__2_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__3 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__3_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_2),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__4 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__4_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__5 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__5_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__6 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__6_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__7 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__7_value;
static lean_once_cell_t l_Lean_TSyntax_expandInterpolatedStr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__8;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "TSyntax"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__9 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__9_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__10_value_aux_0),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(208, 86, 51, 178, 37, 75, 0, 6)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__10 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__10_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__10_value)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__11 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__11_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Compat"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__12 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__12_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__13_value_aux_0),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(208, 86, 51, 178, 37, 75, 0, 6)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__13_value_aux_1),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__12_value),LEAN_SCALAR_PTR_LITERAL(233, 134, 124, 217, 96, 118, 79, 86)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__13 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__13_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__13_value)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__14 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__14_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__15 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__15_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__11_value),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__15_value)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__16 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__16_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__17 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.TransparencyMode.all"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__0 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__1 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.TransparencyMode.default"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__2 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__3 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.TransparencyMode.reducible"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__4 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__5 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__5_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.TransparencyMode.instances"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__6 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__6_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__7 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__7_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.TransparencyMode.none"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__8 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__8_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__9 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__9_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.TransparencyMode.implicit"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__10 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__10_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__10_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__11 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprTransparencyMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprTransparencyMode_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprTransparencyMode___closed__0 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprTransparencyMode = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode___closed__0_value;
static const lean_string_object l_Lean_Meta_instReprEtaStructMode_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.EtaStructMode.all"};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__0 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprEtaStructMode_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__1 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_instReprEtaStructMode_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.EtaStructMode.notClasses"};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__2 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprEtaStructMode_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__3 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprEtaStructMode_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.EtaStructMode.none"};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__4 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprEtaStructMode_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__5 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprEtaStructMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprEtaStructMode_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprEtaStructMode___closed__0 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprEtaStructMode = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode___closed__0_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zeta"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__4;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "beta"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__6_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eta"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "etaStruct"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__9_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__11;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iota"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__13_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__15_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__18;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "autoUnfold"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__19_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__19_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__20_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__21;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "failIfUnchanged"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__22 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__22_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__22_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__23 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__23_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__24;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unfoldPartialApp"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__25 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__25_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__25_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__26 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__26_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__27;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "zetaDelta"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__28 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__28_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__28_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__29 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__29_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "index"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__30 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__30_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__30_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__31 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__31_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__32;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "zetaUnused"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__33 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__33_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__33_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__34 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__34_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "zetaHave"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__35 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__35_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__35_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__36 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__36_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__37;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "locals"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__38 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__38_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__38_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__39 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__39_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instances"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__40 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__40_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__40_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__41 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__41_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprConfig_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprConfig___closed__0 = (const lean_object*)&l_Lean_Meta_instReprConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprConfig = (const lean_object*)&l_Lean_Meta_instReprConfig___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__1_value)}};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0_value;
static const lean_string_object l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__1_value)}};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "maxSteps"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "maxDischargeDepth"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "contextual"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "memoize"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "singlePass"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arith"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ground"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "implicitDefEqProofs"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "catchRuntime"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letToHave"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "congrConsts"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bitVecOfNat"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "warnExponents"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "suggestions"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "maxSuggestions"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__38 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__38_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__38_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprConfig__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprConfig__1_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprConfig__1___closed__0 = (const lean_object*)&l_Lean_Meta_instReprConfig__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprConfig__1 = (const lean_object*)&l_Lean_Meta_instReprConfig__1___closed__0_value;
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_getConfigItems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_getConfigItems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__1_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_getConfigItems___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 254, 59, 95, 54, 234, 162, 220)}};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object*, lean_object*);
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_version_getMajor_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1_ = stack[0].m_obj;
lean_object* v_res_2_;
v_res_2_ = lean_version_get_major(v_u_1_);
stack->m_obj
 = v_res_2_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMajor___boxed(lean_object* v_u_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lean_version_get_major(v_u_3_);
return v_res_4_;
}
}
static lean_object* _init_l_Lean_version_major___closed__0(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_version_get_major(v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_version_major(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Lean_version_major___closed__0, &l_Lean_version_major___closed__0_once, _init_l_Lean_version_major___closed__0);
return v___x_7_;
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_version_getMinor_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_8_ = stack[0].m_obj;
lean_object* v_res_9_;
v_res_9_ = lean_version_get_minor(v_u_8_);
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMinor___boxed(lean_object* v_u_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lean_version_get_minor(v_u_10_);
return v_res_11_;
}
}
static lean_object* _init_l_Lean_version_minor___closed__0(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_box(0);
v___x_13_ = lean_version_get_minor(v___x_12_);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_version_minor(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_Lean_version_minor___closed__0, &l_Lean_version_minor___closed__0_once, _init_l_Lean_version_minor___closed__0);
return v___x_14_;
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_version_getPatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_15_ = stack[0].m_obj;
lean_object* v_res_16_;
v_res_16_ = lean_version_get_patch(v_u_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getPatch___boxed(lean_object* v_u_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lean_version_get_patch(v_u_17_);
return v_res_18_;
}
}
static lean_object* _init_l_Lean_version_patch___closed__0(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_box(0);
v___x_20_ = lean_version_get_patch(v___x_19_);
return v___x_20_;
}
}
static lean_object* _init_l_Lean_version_patch(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&l_Lean_version_patch___closed__0, &l_Lean_version_patch___closed__0_once, _init_l_Lean_version_patch___closed__0);
return v___x_21_;
}
}
LEAN_EXPORT void l_Lean_getGithash_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_22_ = stack[0].m_obj;
lean_object* v_res_23_;
v_res_23_ = lean_get_githash(v_u_22_);
stack->m_obj
 = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lean_getGithash___boxed(lean_object* v_u_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lean_get_githash(v_u_24_);
return v_res_25_;
}
}
static lean_object* _init_l_Lean_githash___closed__0(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_box(0);
v___x_27_ = lean_get_githash(v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_l_Lean_githash(void){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l_Lean_githash___closed__0, &l_Lean_githash___closed__0_once, _init_l_Lean_githash___closed__0);
return v___x_28_;
}
}
LEAN_EXPORT void l_Lean_version_getIsRelease_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_29_ = stack[0].m_obj;
uint8_t v_res_30_;
v_res_30_ = lean_version_get_is_release(v_u_29_);
stack->m_num = v_res_30_;
}
LEAN_EXPORT lean_object* l_Lean_version_getIsRelease___boxed(lean_object* v_u_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = lean_version_get_is_release(v_u_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
static uint8_t _init_l_Lean_version_isRelease___closed__0(void){
_start:
{
lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_34_ = lean_box(0);
v___x_35_ = lean_version_get_is_release(v___x_34_);
return v___x_35_;
}
}
static uint8_t _init_l_Lean_version_isRelease(void){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = lean_uint8_once(&l_Lean_version_isRelease___closed__0, &l_Lean_version_isRelease___closed__0_once, _init_l_Lean_version_isRelease___closed__0);
return v___x_36_;
}
}
LEAN_EXPORT void l_Lean_version_getSpecialDesc_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_37_ = stack[0].m_obj;
lean_object* v_res_38_;
v_res_38_ = lean_version_get_special_desc(v_u_37_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lean_version_getSpecialDesc___boxed(lean_object* v_u_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lean_version_get_special_desc(v_u_39_);
return v_res_40_;
}
}
static lean_object* _init_l_Lean_version_specialDesc___closed__0(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_box(0);
v___x_42_ = lean_version_get_special_desc(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_version_specialDesc(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&l_Lean_version_specialDesc___closed__0, &l_Lean_version_specialDesc___closed__0_once, _init_l_Lean_version_specialDesc___closed__0);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__0(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = l_Lean_version_major;
v___x_45_ = l_Nat_reprFast(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__2(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_47_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_48_ = lean_obj_once(&l_Lean_versionStringCore___closed__0, &l_Lean_versionStringCore___closed__0_once, _init_l_Lean_versionStringCore___closed__0);
v___x_49_ = lean_string_append(v___x_48_, v___x_47_);
return v___x_49_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__3(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = l_Lean_version_minor;
v___x_51_ = l_Nat_reprFast(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__4(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_obj_once(&l_Lean_versionStringCore___closed__3, &l_Lean_versionStringCore___closed__3_once, _init_l_Lean_versionStringCore___closed__3);
v___x_53_ = lean_obj_once(&l_Lean_versionStringCore___closed__2, &l_Lean_versionStringCore___closed__2_once, _init_l_Lean_versionStringCore___closed__2);
v___x_54_ = lean_string_append(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__5(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_56_ = lean_obj_once(&l_Lean_versionStringCore___closed__4, &l_Lean_versionStringCore___closed__4_once, _init_l_Lean_versionStringCore___closed__4);
v___x_57_ = lean_string_append(v___x_56_, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__6(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = l_Lean_version_patch;
v___x_59_ = l_Nat_reprFast(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__7(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Lean_versionStringCore___closed__6, &l_Lean_versionStringCore___closed__6_once, _init_l_Lean_versionStringCore___closed__6);
v___x_61_ = lean_obj_once(&l_Lean_versionStringCore___closed__5, &l_Lean_versionStringCore___closed__5_once, _init_l_Lean_versionStringCore___closed__5);
v___x_62_ = lean_string_append(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_versionStringCore(void){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_obj_once(&l_Lean_versionStringCore___closed__7, &l_Lean_versionStringCore___closed__7_once, _init_l_Lean_versionStringCore___closed__7);
return v___x_63_;
}
}
static uint8_t _init_l_Lean_versionString___closed__1(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_65_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_66_ = l_Lean_version_specialDesc;
v___x_67_ = lean_string_dec_eq(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_versionString___closed__3(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = ((lean_object*)(l_Lean_versionString___closed__2));
v___x_70_ = l_Lean_versionStringCore;
v___x_71_ = lean_string_append(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_versionString___closed__4(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = l_Lean_version_specialDesc;
v___x_73_ = lean_obj_once(&l_Lean_versionString___closed__3, &l_Lean_versionString___closed__3_once, _init_l_Lean_versionString___closed__3);
v___x_74_ = lean_string_append(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_versionString___closed__6(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = ((lean_object*)(l_Lean_versionString___closed__5));
v___x_77_ = l_Lean_versionStringCore;
v___x_78_ = lean_string_append(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_versionString___closed__7(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = l_Lean_githash;
v___x_80_ = lean_obj_once(&l_Lean_versionString___closed__6, &l_Lean_versionString___closed__6_once, _init_l_Lean_versionString___closed__6);
v___x_81_ = lean_string_append(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_versionString(void){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = lean_uint8_once(&l_Lean_versionString___closed__1, &l_Lean_versionString___closed__1_once, _init_l_Lean_versionString___closed__1);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; 
v___x_83_ = lean_obj_once(&l_Lean_versionString___closed__4, &l_Lean_versionString___closed__4_once, _init_l_Lean_versionString___closed__4);
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = l_Lean_version_isRelease;
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&l_Lean_versionString___closed__7, &l_Lean_versionString___closed__7_once, _init_l_Lean_versionString___closed__7);
return v___x_85_;
}
else
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_versionStringCore;
return v___x_86_;
}
}
}
}
static lean_object* _init_l_Lean_toolchain___closed__1(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_91_ = ((lean_object*)(l_Lean_origin___closed__0));
v___x_92_ = lean_string_append(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__2(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = l_Lean_version_specialDesc;
v___x_94_ = lean_obj_once(&l_Lean_toolchain___closed__1, &l_Lean_toolchain___closed__1_once, _init_l_Lean_toolchain___closed__1);
v___x_95_ = lean_string_append(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__4(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = ((lean_object*)(l_Lean_toolchain___closed__3));
v___x_98_ = ((lean_object*)(l_Lean_origin___closed__0));
v___x_99_ = lean_string_append(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__5(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = l_Lean_versionStringCore;
v___x_101_ = lean_obj_once(&l_Lean_toolchain___closed__4, &l_Lean_toolchain___closed__4_once, _init_l_Lean_toolchain___closed__4);
v___x_102_ = lean_string_append(v___x_101_, v___x_100_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__6(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = ((lean_object*)(l_Lean_versionString___closed__2));
v___x_104_ = lean_obj_once(&l_Lean_toolchain___closed__5, &l_Lean_toolchain___closed__5_once, _init_l_Lean_toolchain___closed__5);
v___x_105_ = lean_string_append(v___x_104_, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__7(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = l_Lean_version_specialDesc;
v___x_107_ = lean_obj_once(&l_Lean_toolchain___closed__6, &l_Lean_toolchain___closed__6_once, _init_l_Lean_toolchain___closed__6);
v___x_108_ = lean_string_append(v___x_107_, v___x_106_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_toolchain(void){
_start:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_110_ = lean_uint8_once(&l_Lean_versionString___closed__1, &l_Lean_versionString___closed__1_once, _init_l_Lean_versionString___closed__1);
if (v___x_110_ == 0)
{
uint8_t v___x_111_; 
v___x_111_ = l_Lean_version_isRelease;
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lean_toolchain___closed__2, &l_Lean_toolchain___closed__2_once, _init_l_Lean_toolchain___closed__2);
return v___x_112_;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lean_toolchain___closed__7, &l_Lean_toolchain___closed__7_once, _init_l_Lean_toolchain___closed__7);
return v___x_113_;
}
}
else
{
uint8_t v___x_114_; 
v___x_114_ = l_Lean_version_isRelease;
if (v___x_114_ == 0)
{
return v___x_109_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Lean_toolchain___closed__5, &l_Lean_toolchain___closed__5_once, _init_l_Lean_toolchain___closed__5);
return v___x_115_;
}
}
}
}
LEAN_EXPORT void l_Lean_Internal_isStage0_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_116_ = stack[0].m_obj;
uint8_t v_res_117_;
v_res_117_ = lean_internal_is_stage0(v_u_116_);
stack->m_num = v_res_117_;
}
LEAN_EXPORT lean_object* l_Lean_Internal_isStage0___boxed(lean_object* v_u_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = lean_internal_is_stage0(v_u_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT void l_Lean_Internal_hasLLVMBackend_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_121_ = stack[0].m_obj;
uint8_t v_res_122_;
v_res_122_ = lean_internal_has_llvm_backend(v_u_121_);
stack->m_num = v_res_122_;
}
LEAN_EXPORT lean_object* l_Lean_Internal_hasLLVMBackend___boxed(lean_object* v_u_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = lean_internal_has_llvm_backend(v_u_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
uint8_t l_Lean_isGreek(uint32_t v_c_126_){
_start:
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 913;
v___x_128_ = lean_uint32_dec_le(v___x_127_, v_c_126_);
if (v___x_128_ == 0)
{
return v___x_128_;
}
else
{
uint32_t v___x_129_; uint8_t v___x_130_; 
v___x_129_ = 989;
v___x_130_ = lean_uint32_dec_le(v_c_126_, v___x_129_);
return v___x_130_;
}
}
}
LEAN_EXPORT void l_Lean_isGreek_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_126_ = stack[0].m_num;
uint8_t v_res_131_;
v_res_131_ = l_Lean_isGreek(v_c_126_);
stack->m_num = v_res_131_;
}
LEAN_EXPORT lean_object* l_Lean_isGreek___boxed(lean_object* v_c_132_){
_start:
{
uint32_t v_c_boxed_133_; uint8_t v_res_134_; lean_object* v_r_135_; 
v_c_boxed_133_ = lean_unbox_uint32(v_c_132_);
lean_dec(v_c_132_);
v_res_134_ = l_Lean_isGreek(v_c_boxed_133_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
uint8_t l_Lean_isLetterLike(uint32_t v_c_136_){
_start:
{
uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_180_ = 945;
v___x_181_ = lean_uint32_dec_le(v___x_180_, v_c_136_);
if (v___x_181_ == 0)
{
goto v___jp_171_;
}
else
{
uint32_t v___x_182_; uint8_t v___x_183_; 
v___x_182_ = 969;
v___x_183_ = lean_uint32_dec_le(v_c_136_, v___x_182_);
if (v___x_183_ == 0)
{
goto v___jp_171_;
}
else
{
uint32_t v___x_184_; uint8_t v___x_185_; 
v___x_184_ = 955;
v___x_185_ = lean_uint32_dec_eq(v_c_136_, v___x_184_);
if (v___x_185_ == 0)
{
if (v___x_183_ == 0)
{
goto v___jp_171_;
}
else
{
return v___x_183_;
}
}
else
{
goto v___jp_171_;
}
}
}
v___jp_137_:
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 256;
v___x_139_ = lean_uint32_dec_le(v___x_138_, v_c_136_);
if (v___x_139_ == 0)
{
return v___x_139_;
}
else
{
uint32_t v___x_140_; uint8_t v___x_141_; 
v___x_140_ = 383;
v___x_141_ = lean_uint32_dec_le(v_c_136_, v___x_140_);
return v___x_141_;
}
}
v___jp_142_:
{
uint32_t v___x_143_; uint8_t v___x_144_; 
v___x_143_ = 192;
v___x_144_ = lean_uint32_dec_le(v___x_143_, v_c_136_);
if (v___x_144_ == 0)
{
goto v___jp_137_;
}
else
{
uint32_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = 255;
v___x_146_ = lean_uint32_dec_le(v_c_136_, v___x_145_);
if (v___x_146_ == 0)
{
goto v___jp_137_;
}
else
{
uint32_t v___x_147_; uint8_t v___x_148_; 
v___x_147_ = 215;
v___x_148_ = lean_uint32_dec_eq(v_c_136_, v___x_147_);
if (v___x_148_ == 0)
{
if (v___x_146_ == 0)
{
goto v___jp_137_;
}
else
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 247;
v___x_150_ = lean_uint32_dec_eq(v_c_136_, v___x_149_);
if (v___x_150_ == 0)
{
return v___x_146_;
}
else
{
goto v___jp_137_;
}
}
}
else
{
goto v___jp_137_;
}
}
}
}
v___jp_151_:
{
uint32_t v___x_152_; uint8_t v___x_153_; 
v___x_152_ = 119964;
v___x_153_ = lean_uint32_dec_le(v___x_152_, v_c_136_);
if (v___x_153_ == 0)
{
goto v___jp_142_;
}
else
{
uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = 120223;
v___x_155_ = lean_uint32_dec_le(v_c_136_, v___x_154_);
if (v___x_155_ == 0)
{
goto v___jp_142_;
}
else
{
return v___x_155_;
}
}
}
v___jp_156_:
{
uint32_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 8448;
v___x_158_ = lean_uint32_dec_le(v___x_157_, v_c_136_);
if (v___x_158_ == 0)
{
goto v___jp_151_;
}
else
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 8527;
v___x_160_ = lean_uint32_dec_le(v_c_136_, v___x_159_);
if (v___x_160_ == 0)
{
goto v___jp_151_;
}
else
{
return v___x_160_;
}
}
}
v___jp_161_:
{
uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 7936;
v___x_163_ = lean_uint32_dec_le(v___x_162_, v_c_136_);
if (v___x_163_ == 0)
{
goto v___jp_156_;
}
else
{
uint32_t v___x_164_; uint8_t v___x_165_; 
v___x_164_ = 8190;
v___x_165_ = lean_uint32_dec_le(v_c_136_, v___x_164_);
if (v___x_165_ == 0)
{
goto v___jp_156_;
}
else
{
return v___x_165_;
}
}
}
v___jp_166_:
{
uint32_t v___x_167_; uint8_t v___x_168_; 
v___x_167_ = 970;
v___x_168_ = lean_uint32_dec_le(v___x_167_, v_c_136_);
if (v___x_168_ == 0)
{
goto v___jp_161_;
}
else
{
uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_169_ = 1019;
v___x_170_ = lean_uint32_dec_le(v_c_136_, v___x_169_);
if (v___x_170_ == 0)
{
goto v___jp_161_;
}
else
{
return v___x_170_;
}
}
}
v___jp_171_:
{
uint32_t v___x_172_; uint8_t v___x_173_; 
v___x_172_ = 913;
v___x_173_ = lean_uint32_dec_le(v___x_172_, v_c_136_);
if (v___x_173_ == 0)
{
goto v___jp_166_;
}
else
{
uint32_t v___x_174_; uint8_t v___x_175_; 
v___x_174_ = 937;
v___x_175_ = lean_uint32_dec_le(v_c_136_, v___x_174_);
if (v___x_175_ == 0)
{
goto v___jp_166_;
}
else
{
uint32_t v___x_176_; uint8_t v___x_177_; 
v___x_176_ = 928;
v___x_177_ = lean_uint32_dec_eq(v_c_136_, v___x_176_);
if (v___x_177_ == 0)
{
if (v___x_175_ == 0)
{
goto v___jp_166_;
}
else
{
uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = 931;
v___x_179_ = lean_uint32_dec_eq(v_c_136_, v___x_178_);
if (v___x_179_ == 0)
{
return v___x_175_;
}
else
{
goto v___jp_166_;
}
}
}
else
{
goto v___jp_166_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_isLetterLike_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_136_ = stack[0].m_num;
uint8_t v_res_186_;
v_res_186_ = l_Lean_isLetterLike(v_c_136_);
stack->m_num = v_res_186_;
}
LEAN_EXPORT lean_object* l_Lean_isLetterLike___boxed(lean_object* v_c_187_){
_start:
{
uint32_t v_c_boxed_188_; uint8_t v_res_189_; lean_object* v_r_190_; 
v_c_boxed_188_ = lean_unbox_uint32(v_c_187_);
lean_dec(v_c_187_);
v_res_189_ = l_Lean_isLetterLike(v_c_boxed_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
uint8_t l_Lean_isNumericSubscript(uint32_t v_c_191_){
_start:
{
uint32_t v___x_192_; uint8_t v___x_193_; 
v___x_192_ = 8320;
v___x_193_ = lean_uint32_dec_le(v___x_192_, v_c_191_);
if (v___x_193_ == 0)
{
return v___x_193_;
}
else
{
uint32_t v___x_194_; uint8_t v___x_195_; 
v___x_194_ = 8329;
v___x_195_ = lean_uint32_dec_le(v_c_191_, v___x_194_);
return v___x_195_;
}
}
}
LEAN_EXPORT void l_Lean_isNumericSubscript_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_191_ = stack[0].m_num;
uint8_t v_res_196_;
v_res_196_ = l_Lean_isNumericSubscript(v_c_191_);
stack->m_num = v_res_196_;
}
LEAN_EXPORT lean_object* l_Lean_isNumericSubscript___boxed(lean_object* v_c_197_){
_start:
{
uint32_t v_c_boxed_198_; uint8_t v_res_199_; lean_object* v_r_200_; 
v_c_boxed_198_ = lean_unbox_uint32(v_c_197_);
lean_dec(v_c_197_);
v_res_199_ = l_Lean_isNumericSubscript(v_c_boxed_198_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
uint8_t l_Lean_isSubScriptAlnum(uint32_t v_c_201_){
_start:
{
uint32_t v___x_215_; uint8_t v___x_216_; 
v___x_215_ = 8320;
v___x_216_ = lean_uint32_dec_le(v___x_215_, v_c_201_);
if (v___x_216_ == 0)
{
goto v___jp_210_;
}
else
{
uint32_t v___x_217_; uint8_t v___x_218_; 
v___x_217_ = 8329;
v___x_218_ = lean_uint32_dec_le(v_c_201_, v___x_217_);
if (v___x_218_ == 0)
{
goto v___jp_210_;
}
else
{
return v___x_218_;
}
}
v___jp_202_:
{
uint32_t v___x_203_; uint8_t v___x_204_; 
v___x_203_ = 11388;
v___x_204_ = lean_uint32_dec_eq(v_c_201_, v___x_203_);
return v___x_204_;
}
v___jp_205_:
{
uint32_t v___x_206_; uint8_t v___x_207_; 
v___x_206_ = 7522;
v___x_207_ = lean_uint32_dec_le(v___x_206_, v_c_201_);
if (v___x_207_ == 0)
{
goto v___jp_202_;
}
else
{
uint32_t v___x_208_; uint8_t v___x_209_; 
v___x_208_ = 7530;
v___x_209_ = lean_uint32_dec_le(v_c_201_, v___x_208_);
if (v___x_209_ == 0)
{
goto v___jp_202_;
}
else
{
return v___x_209_;
}
}
}
v___jp_210_:
{
uint32_t v___x_211_; uint8_t v___x_212_; 
v___x_211_ = 8336;
v___x_212_ = lean_uint32_dec_le(v___x_211_, v_c_201_);
if (v___x_212_ == 0)
{
goto v___jp_205_;
}
else
{
uint32_t v___x_213_; uint8_t v___x_214_; 
v___x_213_ = 8348;
v___x_214_ = lean_uint32_dec_le(v_c_201_, v___x_213_);
if (v___x_214_ == 0)
{
goto v___jp_205_;
}
else
{
return v___x_214_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_isSubScriptAlnum_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_201_ = stack[0].m_num;
uint8_t v_res_219_;
v_res_219_ = l_Lean_isSubScriptAlnum(v_c_201_);
stack->m_num = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object* v_c_220_){
_start:
{
uint32_t v_c_boxed_221_; uint8_t v_res_222_; lean_object* v_r_223_; 
v_c_boxed_221_ = lean_unbox_uint32(v_c_220_);
lean_dec(v_c_220_);
v_res_222_ = l_Lean_isSubScriptAlnum(v_c_boxed_221_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
uint8_t l_Lean_isIdFirst(uint32_t v_c_224_){
_start:
{
uint32_t v___x_234_; uint8_t v___x_235_; 
v___x_234_ = 65;
v___x_235_ = lean_uint32_dec_le(v___x_234_, v_c_224_);
if (v___x_235_ == 0)
{
goto v___jp_229_;
}
else
{
uint32_t v___x_236_; uint8_t v___x_237_; 
v___x_236_ = 90;
v___x_237_ = lean_uint32_dec_le(v_c_224_, v___x_236_);
if (v___x_237_ == 0)
{
goto v___jp_229_;
}
else
{
return v___x_237_;
}
}
v___jp_225_:
{
uint32_t v___x_226_; uint8_t v___x_227_; 
v___x_226_ = 95;
v___x_227_ = lean_uint32_dec_eq(v_c_224_, v___x_226_);
if (v___x_227_ == 0)
{
uint8_t v___x_228_; 
v___x_228_ = l_Lean_isLetterLike(v_c_224_);
return v___x_228_;
}
else
{
return v___x_227_;
}
}
v___jp_229_:
{
uint32_t v___x_230_; uint8_t v___x_231_; 
v___x_230_ = 97;
v___x_231_ = lean_uint32_dec_le(v___x_230_, v_c_224_);
if (v___x_231_ == 0)
{
goto v___jp_225_;
}
else
{
uint32_t v___x_232_; uint8_t v___x_233_; 
v___x_232_ = 122;
v___x_233_ = lean_uint32_dec_le(v_c_224_, v___x_232_);
if (v___x_233_ == 0)
{
goto v___jp_225_;
}
else
{
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_isIdFirst_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_224_ = stack[0].m_num;
uint8_t v_res_238_;
v_res_238_ = l_Lean_isIdFirst(v_c_224_);
stack->m_num = v_res_238_;
}
LEAN_EXPORT lean_object* l_Lean_isIdFirst___boxed(lean_object* v_c_239_){
_start:
{
uint32_t v_c_boxed_240_; uint8_t v_res_241_; lean_object* v_r_242_; 
v_c_boxed_240_ = lean_unbox_uint32(v_c_239_);
lean_dec(v_c_239_);
v_res_241_ = l_Lean_isIdFirst(v_c_boxed_240_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t v_c_243_){
_start:
{
uint8_t v___x_249_; uint8_t v___x_250_; 
v___x_249_ = 97;
v___x_250_ = lean_uint8_dec_le(v___x_249_, v_c_243_);
if (v___x_250_ == 0)
{
goto v___jp_244_;
}
else
{
uint8_t v___x_251_; uint8_t v___x_252_; 
v___x_251_ = 122;
v___x_252_ = lean_uint8_dec_le(v_c_243_, v___x_251_);
if (v___x_252_ == 0)
{
goto v___jp_244_;
}
else
{
return v___x_252_;
}
}
v___jp_244_:
{
uint8_t v___x_245_; uint8_t v___x_246_; 
v___x_245_ = 65;
v___x_246_ = lean_uint8_dec_le(v___x_245_, v_c_243_);
if (v___x_246_ == 0)
{
return v___x_246_;
}
else
{
uint8_t v___x_247_; uint8_t v___x_248_; 
v___x_247_ = 90;
v___x_248_ = lean_uint8_dec_le(v_c_243_, v___x_247_);
return v___x_248_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_isAlphaAscii_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_243_ = stack[0].m_num;
uint8_t v_res_253_;
v_res_253_ = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(v_c_243_);
stack->m_num = v_res_253_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object* v_c_254_){
_start:
{
uint8_t v_c_boxed_255_; uint8_t v_res_256_; lean_object* v_r_257_; 
v_c_boxed_255_ = lean_unbox(v_c_254_);
v_res_256_ = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(v_c_boxed_255_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
uint8_t l_Lean_isIdFirstAscii(uint8_t v_c_258_){
_start:
{
uint8_t v___x_267_; uint8_t v___x_268_; 
v___x_267_ = 97;
v___x_268_ = lean_uint8_dec_le(v___x_267_, v_c_258_);
if (v___x_268_ == 0)
{
goto v___jp_262_;
}
else
{
uint8_t v___x_269_; uint8_t v___x_270_; 
v___x_269_ = 122;
v___x_270_ = lean_uint8_dec_le(v_c_258_, v___x_269_);
if (v___x_270_ == 0)
{
goto v___jp_262_;
}
else
{
return v___x_270_;
}
}
v___jp_259_:
{
uint8_t v___x_260_; uint8_t v___x_261_; 
v___x_260_ = 95;
v___x_261_ = lean_uint8_dec_eq(v_c_258_, v___x_260_);
return v___x_261_;
}
v___jp_262_:
{
uint8_t v___x_263_; uint8_t v___x_264_; 
v___x_263_ = 65;
v___x_264_ = lean_uint8_dec_le(v___x_263_, v_c_258_);
if (v___x_264_ == 0)
{
goto v___jp_259_;
}
else
{
uint8_t v___x_265_; uint8_t v___x_266_; 
v___x_265_ = 90;
v___x_266_ = lean_uint8_dec_le(v_c_258_, v___x_265_);
if (v___x_266_ == 0)
{
goto v___jp_259_;
}
else
{
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_isIdFirstAscii_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_258_ = stack[0].m_num;
uint8_t v_res_271_;
v_res_271_ = l_Lean_isIdFirstAscii(v_c_258_);
stack->m_num = v_res_271_;
}
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object* v_c_272_){
_start:
{
uint8_t v_c_boxed_273_; uint8_t v_res_274_; lean_object* v_r_275_; 
v_c_boxed_273_ = lean_unbox(v_c_272_);
v_res_274_ = l_Lean_isIdFirstAscii(v_c_boxed_273_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t v_c_276_){
_start:
{
uint8_t v___x_287_; uint8_t v___x_288_; 
v___x_287_ = 97;
v___x_288_ = lean_uint8_dec_le(v___x_287_, v_c_276_);
if (v___x_288_ == 0)
{
goto v___jp_282_;
}
else
{
uint8_t v___x_289_; uint8_t v___x_290_; 
v___x_289_ = 122;
v___x_290_ = lean_uint8_dec_le(v_c_276_, v___x_289_);
if (v___x_290_ == 0)
{
goto v___jp_282_;
}
else
{
return v___x_290_;
}
}
v___jp_277_:
{
uint8_t v___x_278_; uint8_t v___x_279_; 
v___x_278_ = 48;
v___x_279_ = lean_uint8_dec_le(v___x_278_, v_c_276_);
if (v___x_279_ == 0)
{
return v___x_279_;
}
else
{
uint8_t v___x_280_; uint8_t v___x_281_; 
v___x_280_ = 57;
v___x_281_ = lean_uint8_dec_le(v_c_276_, v___x_280_);
return v___x_281_;
}
}
v___jp_282_:
{
uint8_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = 65;
v___x_284_ = lean_uint8_dec_le(v___x_283_, v_c_276_);
if (v___x_284_ == 0)
{
goto v___jp_277_;
}
else
{
uint8_t v___x_285_; uint8_t v___x_286_; 
v___x_285_ = 90;
v___x_286_ = lean_uint8_dec_le(v_c_276_, v___x_285_);
if (v___x_286_ == 0)
{
goto v___jp_277_;
}
else
{
return v___x_286_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_276_ = stack[0].m_num;
uint8_t v_res_291_;
v_res_291_ = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(v_c_276_);
stack->m_num = v_res_291_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object* v_c_292_){
_start:
{
uint8_t v_c_boxed_293_; uint8_t v_res_294_; lean_object* v_r_295_; 
v_c_boxed_293_ = lean_unbox(v_c_292_);
v_res_294_ = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(v_c_boxed_293_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
uint8_t l_Lean_isIdRest(uint32_t v_c_296_){
_start:
{
uint32_t v___x_318_; uint8_t v___x_319_; 
v___x_318_ = 65;
v___x_319_ = lean_uint32_dec_le(v___x_318_, v_c_296_);
if (v___x_319_ == 0)
{
goto v___jp_313_;
}
else
{
uint32_t v___x_320_; uint8_t v___x_321_; 
v___x_320_ = 90;
v___x_321_ = lean_uint32_dec_le(v_c_296_, v___x_320_);
if (v___x_321_ == 0)
{
goto v___jp_313_;
}
else
{
return v___x_321_;
}
}
v___jp_297_:
{
uint32_t v___x_298_; uint8_t v___x_299_; 
v___x_298_ = 95;
v___x_299_ = lean_uint32_dec_eq(v_c_296_, v___x_298_);
if (v___x_299_ == 0)
{
uint32_t v___x_300_; uint8_t v___x_301_; 
v___x_300_ = 39;
v___x_301_ = lean_uint32_dec_eq(v_c_296_, v___x_300_);
if (v___x_301_ == 0)
{
uint32_t v___x_302_; uint8_t v___x_303_; 
v___x_302_ = 33;
v___x_303_ = lean_uint32_dec_eq(v_c_296_, v___x_302_);
if (v___x_303_ == 0)
{
uint32_t v___x_304_; uint8_t v___x_305_; 
v___x_304_ = 63;
v___x_305_ = lean_uint32_dec_eq(v_c_296_, v___x_304_);
if (v___x_305_ == 0)
{
uint8_t v___x_306_; 
v___x_306_ = l_Lean_isLetterLike(v_c_296_);
if (v___x_306_ == 0)
{
uint8_t v___x_307_; 
v___x_307_ = l_Lean_isSubScriptAlnum(v_c_296_);
return v___x_307_;
}
else
{
return v___x_306_;
}
}
else
{
return v___x_305_;
}
}
else
{
return v___x_303_;
}
}
else
{
return v___x_301_;
}
}
else
{
return v___x_299_;
}
}
v___jp_308_:
{
uint32_t v___x_309_; uint8_t v___x_310_; 
v___x_309_ = 48;
v___x_310_ = lean_uint32_dec_le(v___x_309_, v_c_296_);
if (v___x_310_ == 0)
{
goto v___jp_297_;
}
else
{
uint32_t v___x_311_; uint8_t v___x_312_; 
v___x_311_ = 57;
v___x_312_ = lean_uint32_dec_le(v_c_296_, v___x_311_);
if (v___x_312_ == 0)
{
goto v___jp_297_;
}
else
{
return v___x_312_;
}
}
}
v___jp_313_:
{
uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = 97;
v___x_315_ = lean_uint32_dec_le(v___x_314_, v_c_296_);
if (v___x_315_ == 0)
{
goto v___jp_308_;
}
else
{
uint32_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 122;
v___x_317_ = lean_uint32_dec_le(v_c_296_, v___x_316_);
if (v___x_317_ == 0)
{
goto v___jp_308_;
}
else
{
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_isIdRest_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_296_ = stack[0].m_num;
uint8_t v_res_322_;
v_res_322_ = l_Lean_isIdRest(v_c_296_);
stack->m_num = v_res_322_;
}
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object* v_c_323_){
_start:
{
uint32_t v_c_boxed_324_; uint8_t v_res_325_; lean_object* v_r_326_; 
v_c_boxed_324_ = lean_unbox_uint32(v_c_323_);
lean_dec(v_c_323_);
v_res_325_ = l_Lean_isIdRest(v_c_boxed_324_);
v_r_326_ = lean_box(v_res_325_);
return v_r_326_;
}
}
uint8_t l_Lean_isIdRestAscii(uint8_t v_c_327_){
_start:
{
uint8_t v___x_347_; uint8_t v___x_348_; 
v___x_347_ = 97;
v___x_348_ = lean_uint8_dec_le(v___x_347_, v_c_327_);
if (v___x_348_ == 0)
{
goto v___jp_342_;
}
else
{
uint8_t v___x_349_; uint8_t v___x_350_; 
v___x_349_ = 122;
v___x_350_ = lean_uint8_dec_le(v_c_327_, v___x_349_);
if (v___x_350_ == 0)
{
goto v___jp_342_;
}
else
{
return v___x_350_;
}
}
v___jp_328_:
{
uint8_t v___x_329_; uint8_t v___x_330_; 
v___x_329_ = 95;
v___x_330_ = lean_uint8_dec_eq(v_c_327_, v___x_329_);
if (v___x_330_ == 0)
{
uint8_t v___x_331_; uint8_t v___x_332_; 
v___x_331_ = 39;
v___x_332_ = lean_uint8_dec_eq(v_c_327_, v___x_331_);
if (v___x_332_ == 0)
{
uint8_t v___x_333_; uint8_t v___x_334_; 
v___x_333_ = 33;
v___x_334_ = lean_uint8_dec_eq(v_c_327_, v___x_333_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; uint8_t v___x_336_; 
v___x_335_ = 63;
v___x_336_ = lean_uint8_dec_eq(v_c_327_, v___x_335_);
return v___x_336_;
}
else
{
return v___x_334_;
}
}
else
{
return v___x_332_;
}
}
else
{
return v___x_330_;
}
}
v___jp_337_:
{
uint8_t v___x_338_; uint8_t v___x_339_; 
v___x_338_ = 48;
v___x_339_ = lean_uint8_dec_le(v___x_338_, v_c_327_);
if (v___x_339_ == 0)
{
goto v___jp_328_;
}
else
{
uint8_t v___x_340_; uint8_t v___x_341_; 
v___x_340_ = 57;
v___x_341_ = lean_uint8_dec_le(v_c_327_, v___x_340_);
if (v___x_341_ == 0)
{
goto v___jp_328_;
}
else
{
return v___x_341_;
}
}
}
v___jp_342_:
{
uint8_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 65;
v___x_344_ = lean_uint8_dec_le(v___x_343_, v_c_327_);
if (v___x_344_ == 0)
{
goto v___jp_337_;
}
else
{
uint8_t v___x_345_; uint8_t v___x_346_; 
v___x_345_ = 90;
v___x_346_ = lean_uint8_dec_le(v_c_327_, v___x_345_);
if (v___x_346_ == 0)
{
goto v___jp_337_;
}
else
{
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_isIdRestAscii_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_327_ = stack[0].m_num;
uint8_t v_res_351_;
v_res_351_ = l_Lean_isIdRestAscii(v_c_327_);
stack->m_num = v_res_351_;
}
LEAN_EXPORT lean_object* l_Lean_isIdRestAscii___boxed(lean_object* v_c_352_){
_start:
{
uint8_t v_c_boxed_353_; uint8_t v_res_354_; lean_object* v_r_355_; 
v_c_boxed_353_ = lean_unbox(v_c_352_);
v_res_354_ = l_Lean_isIdRestAscii(v_c_boxed_353_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
static uint32_t _init_l_Lean_idBeginEscape(void){
_start:
{
uint32_t v___x_356_; 
v___x_356_ = 171;
return v___x_356_;
}
}
static uint32_t _init_l_Lean_idEndEscape(void){
_start:
{
uint32_t v___x_357_; 
v___x_357_ = 187;
return v___x_357_;
}
}
uint8_t l_Lean_isIdBeginEscape(uint32_t v_c_358_){
_start:
{
uint32_t v___x_359_; uint8_t v___x_360_; 
v___x_359_ = 171;
v___x_360_ = lean_uint32_dec_eq(v_c_358_, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT void l_Lean_isIdBeginEscape_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_358_ = stack[0].m_num;
uint8_t v_res_361_;
v_res_361_ = l_Lean_isIdBeginEscape(v_c_358_);
stack->m_num = v_res_361_;
}
LEAN_EXPORT lean_object* l_Lean_isIdBeginEscape___boxed(lean_object* v_c_362_){
_start:
{
uint32_t v_c_boxed_363_; uint8_t v_res_364_; lean_object* v_r_365_; 
v_c_boxed_363_ = lean_unbox_uint32(v_c_362_);
lean_dec(v_c_362_);
v_res_364_ = l_Lean_isIdBeginEscape(v_c_boxed_363_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
uint8_t l_Lean_isIdEndEscape(uint32_t v_c_366_){
_start:
{
uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = 187;
v___x_368_ = lean_uint32_dec_eq(v_c_366_, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT void l_Lean_isIdEndEscape_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_366_ = stack[0].m_num;
uint8_t v_res_369_;
v_res_369_ = l_Lean_isIdEndEscape(v_c_366_);
stack->m_num = v_res_369_;
}
LEAN_EXPORT lean_object* l_Lean_isIdEndEscape___boxed(lean_object* v_c_370_){
_start:
{
uint32_t v_c_boxed_371_; uint8_t v_res_372_; lean_object* v_r_373_; 
v_c_boxed_371_ = lean_unbox_uint32(v_c_370_);
lean_dec(v_c_370_);
v_res_372_ = l_Lean_isIdEndEscape(v_c_boxed_371_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot(lean_object* v_x_374_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
return v_x_374_;
}
else
{
lean_object* v_pre_375_; 
v_pre_375_ = lean_ctor_get(v_x_374_, 0);
if (lean_obj_tag(v_pre_375_) == 0)
{
lean_inc(v_x_374_);
return v_x_374_;
}
else
{
v_x_374_ = v_pre_375_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot___boxed(lean_object* v_x_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Name_getRoot(v_x_377_);
lean_dec(v_x_377_);
return v_res_378_;
}
}
uint8_t l_Lean_Name_isInaccessibleUserName(lean_object* v_x_380_){
_start:
{
switch(lean_obj_tag(v_x_380_))
{
case 1:
{
lean_object* v_str_381_; uint32_t v___x_382_; uint8_t v___x_383_; 
v_str_381_ = lean_ctor_get(v_x_380_, 1);
lean_inc_ref_n(v_str_381_, 2);
lean_dec_ref_known(v_x_380_, 2);
v___x_382_ = 10013;
v___x_383_ = lean_string_contains(v_str_381_, v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Name_isInaccessibleUserName___closed__0));
v___x_385_ = lean_string_dec_eq(v_str_381_, v___x_384_);
lean_dec_ref(v_str_381_);
return v___x_385_;
}
else
{
lean_dec_ref(v_str_381_);
return v___x_383_;
}
}
case 2:
{
lean_object* v_pre_386_; 
v_pre_386_ = lean_ctor_get(v_x_380_, 0);
lean_inc(v_pre_386_);
lean_dec_ref_known(v_x_380_, 2);
v_x_380_ = v_pre_386_;
goto _start;
}
default: 
{
uint8_t v___x_388_; 
lean_dec(v_x_380_);
v___x_388_ = 0;
return v___x_388_;
}
}
}
}
LEAN_EXPORT void l_Lean_Name_isInaccessibleUserName_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_380_ = stack[0].m_obj;
uint8_t v_res_389_;
v_res_389_ = l_Lean_Name_isInaccessibleUserName(v_x_380_);
stack->m_num = v_res_389_;
}
LEAN_EXPORT lean_object* l_Lean_Name_isInaccessibleUserName___boxed(lean_object* v_x_390_){
_start:
{
uint8_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l_Lean_Name_isInaccessibleUserName(v_x_390_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(lean_object* v_s_393_, lean_object* v_i_394_){
_start:
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = lean_string_utf8_byte_size(v_s_393_);
v___x_400_ = lean_nat_dec_lt(v_i_394_, v___x_399_);
if (v___x_400_ == 0)
{
uint8_t v___x_401_; 
lean_dec(v_i_394_);
v___x_401_ = 1;
return v___x_401_;
}
else
{
uint8_t v_c_402_; uint8_t v___x_422_; uint8_t v___x_423_; 
lean_inc(v_i_394_);
v_c_402_ = lean_string_get_byte_fast(v_s_393_, v_i_394_);
v___x_422_ = 97;
v___x_423_ = lean_uint8_dec_le(v___x_422_, v_c_402_);
if (v___x_423_ == 0)
{
goto v___jp_417_;
}
else
{
uint8_t v___x_424_; uint8_t v___x_425_; 
v___x_424_ = 122;
v___x_425_ = lean_uint8_dec_le(v_c_402_, v___x_424_);
if (v___x_425_ == 0)
{
goto v___jp_417_;
}
else
{
goto v___jp_395_;
}
}
v___jp_403_:
{
uint8_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = 95;
v___x_405_ = lean_uint8_dec_eq(v_c_402_, v___x_404_);
if (v___x_405_ == 0)
{
uint8_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = 39;
v___x_407_ = lean_uint8_dec_eq(v_c_402_, v___x_406_);
if (v___x_407_ == 0)
{
uint8_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 33;
v___x_409_ = lean_uint8_dec_eq(v_c_402_, v___x_408_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 63;
v___x_411_ = lean_uint8_dec_eq(v_c_402_, v___x_410_);
if (v___x_411_ == 0)
{
lean_dec(v_i_394_);
return v___x_411_;
}
else
{
goto v___jp_395_;
}
}
else
{
goto v___jp_395_;
}
}
else
{
goto v___jp_395_;
}
}
else
{
goto v___jp_395_;
}
}
v___jp_412_:
{
uint8_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = 48;
v___x_414_ = lean_uint8_dec_le(v___x_413_, v_c_402_);
if (v___x_414_ == 0)
{
goto v___jp_403_;
}
else
{
uint8_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 57;
v___x_416_ = lean_uint8_dec_le(v_c_402_, v___x_415_);
if (v___x_416_ == 0)
{
goto v___jp_403_;
}
else
{
goto v___jp_395_;
}
}
}
v___jp_417_:
{
uint8_t v___x_418_; uint8_t v___x_419_; 
v___x_418_ = 65;
v___x_419_ = lean_uint8_dec_le(v___x_418_, v_c_402_);
if (v___x_419_ == 0)
{
goto v___jp_412_;
}
else
{
uint8_t v___x_420_; uint8_t v___x_421_; 
v___x_420_ = 90;
v___x_421_ = lean_uint8_dec_le(v_c_402_, v___x_420_);
if (v___x_421_ == 0)
{
goto v___jp_412_;
}
else
{
goto v___jp_395_;
}
}
}
}
v___jp_395_:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_add(v_i_394_, v___x_396_);
lean_dec(v_i_394_);
v_i_394_ = v___x_397_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_393_ = stack[0].m_obj;
lean_object* v_i_394_ = stack[1].m_obj;
uint8_t v_res_426_;
v_res_426_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_393_, v_i_394_);
stack->m_num = v_res_426_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object* v_s_427_, lean_object* v_i_428_){
_start:
{
uint8_t v_res_429_; lean_object* v_r_430_; 
v_res_429_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_427_, v_i_428_);
lean_dec_ref(v_s_427_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object* v_s_431_){
_start:
{
lean_object* v___x_435_; uint8_t v_c_436_; uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_435_ = lean_unsigned_to_nat(0u);
v_c_436_ = lean_string_get_byte_fast(v_s_431_, v___x_435_);
v___x_445_ = 97;
v___x_446_ = lean_uint8_dec_le(v___x_445_, v_c_436_);
if (v___x_446_ == 0)
{
goto v___jp_440_;
}
else
{
uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = 122;
v___x_448_ = lean_uint8_dec_le(v_c_436_, v___x_447_);
if (v___x_448_ == 0)
{
goto v___jp_440_;
}
else
{
goto v___jp_432_;
}
}
v___jp_432_:
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_431_, v___x_433_);
return v___x_434_;
}
v___jp_437_:
{
uint8_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = 95;
v___x_439_ = lean_uint8_dec_eq(v_c_436_, v___x_438_);
if (v___x_439_ == 0)
{
return v___x_439_;
}
else
{
goto v___jp_432_;
}
}
v___jp_440_:
{
uint8_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 65;
v___x_442_ = lean_uint8_dec_le(v___x_441_, v_c_436_);
if (v___x_442_ == 0)
{
goto v___jp_437_;
}
else
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 90;
v___x_444_ = lean_uint8_dec_le(v_c_436_, v___x_443_);
if (v___x_444_ == 0)
{
goto v___jp_437_;
}
else
{
goto v___jp_432_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_431_ = stack[0].m_obj;
uint8_t v_res_449_;
v_res_449_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_431_);
stack->m_num = v_res_449_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object* v_s_450_){
_start:
{
uint8_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_450_);
lean_dec_ref(v_s_450_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(lean_object* v_s_453_, lean_object* v_h_454_){
_start:
{
lean_object* v___x_458_; uint8_t v_c_459_; uint8_t v___x_468_; uint8_t v___x_469_; 
v___x_458_ = lean_unsigned_to_nat(0u);
v_c_459_ = lean_string_get_byte_fast(v_s_453_, v___x_458_);
v___x_468_ = 97;
v___x_469_ = lean_uint8_dec_le(v___x_468_, v_c_459_);
if (v___x_469_ == 0)
{
goto v___jp_463_;
}
else
{
uint8_t v___x_470_; uint8_t v___x_471_; 
v___x_470_ = 122;
v___x_471_ = lean_uint8_dec_le(v_c_459_, v___x_470_);
if (v___x_471_ == 0)
{
goto v___jp_463_;
}
else
{
goto v___jp_455_;
}
}
v___jp_455_:
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_453_, v___x_456_);
return v___x_457_;
}
v___jp_460_:
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 95;
v___x_462_ = lean_uint8_dec_eq(v_c_459_, v___x_461_);
if (v___x_462_ == 0)
{
return v___x_462_;
}
else
{
goto v___jp_455_;
}
}
v___jp_463_:
{
uint8_t v___x_464_; uint8_t v___x_465_; 
v___x_464_ = 65;
v___x_465_ = lean_uint8_dec_le(v___x_464_, v_c_459_);
if (v___x_465_ == 0)
{
goto v___jp_460_;
}
else
{
uint8_t v___x_466_; uint8_t v___x_467_; 
v___x_466_ = 90;
v___x_467_ = lean_uint8_dec_le(v_c_459_, v___x_466_);
if (v___x_467_ == 0)
{
goto v___jp_460_;
}
else
{
goto v___jp_455_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_453_ = stack[0].m_obj;
uint8_t v_res_472_;
v_res_472_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(v_s_453_, lean_box(0));
stack->m_num = v_res_472_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object* v_s_473_, lean_object* v_h_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(v_s_473_, v_h_474_);
lean_dec_ref(v_s_473_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(lean_object* v_s_478_){
_start:
{
uint32_t v___y_488_; uint32_t v___y_493_; lean_object* v___x_508_; uint8_t v_c_509_; uint8_t v___x_518_; uint8_t v___x_519_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v_c_509_ = lean_string_get_byte_fast(v_s_478_, v___x_508_);
v___x_518_ = 97;
v___x_519_ = lean_uint8_dec_le(v___x_518_, v_c_509_);
if (v___x_519_ == 0)
{
goto v___jp_513_;
}
else
{
uint8_t v___x_520_; uint8_t v___x_521_; 
v___x_520_ = 122;
v___x_521_ = lean_uint8_dec_le(v_c_509_, v___x_520_);
if (v___x_521_ == 0)
{
goto v___jp_513_;
}
else
{
goto v___jp_505_;
}
}
v___jp_479_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_string_utf8_byte_size(v_s_478_);
v___x_482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_482_, 0, v_s_478_);
lean_ctor_set(v___x_482_, 1, v___x_480_);
lean_ctor_set(v___x_482_, 2, v___x_481_);
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_substring_drop(v___x_482_, v___x_483_);
v___x_485_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_486_ = lean_substring_all(v___x_484_, v___x_485_);
return v___x_486_;
}
v___jp_487_:
{
uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_489_ = 95;
v___x_490_ = lean_uint32_dec_eq(v___y_488_, v___x_489_);
if (v___x_490_ == 0)
{
uint8_t v___x_491_; 
v___x_491_ = l_Lean_isLetterLike(v___y_488_);
if (v___x_491_ == 0)
{
lean_dec_ref(v_s_478_);
return v___x_491_;
}
else
{
goto v___jp_479_;
}
}
else
{
goto v___jp_479_;
}
}
v___jp_492_:
{
uint32_t v___x_494_; uint8_t v___x_495_; 
v___x_494_ = 97;
v___x_495_ = lean_uint32_dec_le(v___x_494_, v___y_493_);
if (v___x_495_ == 0)
{
v___y_488_ = v___y_493_;
goto v___jp_487_;
}
else
{
uint32_t v___x_496_; uint8_t v___x_497_; 
v___x_496_ = 122;
v___x_497_ = lean_uint32_dec_le(v___y_493_, v___x_496_);
if (v___x_497_ == 0)
{
v___y_488_ = v___y_493_;
goto v___jp_487_;
}
else
{
goto v___jp_479_;
}
}
}
v___jp_498_:
{
lean_object* v___x_499_; uint32_t v___x_500_; uint32_t v___x_501_; uint8_t v___x_502_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = lean_string_utf8_get(v_s_478_, v___x_499_);
v___x_501_ = 65;
v___x_502_ = lean_uint32_dec_le(v___x_501_, v___x_500_);
if (v___x_502_ == 0)
{
v___y_493_ = v___x_500_;
goto v___jp_492_;
}
else
{
uint32_t v___x_503_; uint8_t v___x_504_; 
v___x_503_ = 90;
v___x_504_ = lean_uint32_dec_le(v___x_500_, v___x_503_);
if (v___x_504_ == 0)
{
v___y_493_ = v___x_500_;
goto v___jp_492_;
}
else
{
goto v___jp_479_;
}
}
}
v___jp_505_:
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_478_, v___x_506_);
if (v___x_507_ == 0)
{
goto v___jp_498_;
}
else
{
lean_dec_ref(v_s_478_);
return v___x_507_;
}
}
v___jp_510_:
{
uint8_t v___x_511_; uint8_t v___x_512_; 
v___x_511_ = 95;
v___x_512_ = lean_uint8_dec_eq(v_c_509_, v___x_511_);
if (v___x_512_ == 0)
{
goto v___jp_498_;
}
else
{
goto v___jp_505_;
}
}
v___jp_513_:
{
uint8_t v___x_514_; uint8_t v___x_515_; 
v___x_514_ = 65;
v___x_515_ = lean_uint8_dec_le(v___x_514_, v_c_509_);
if (v___x_515_ == 0)
{
goto v___jp_510_;
}
else
{
uint8_t v___x_516_; uint8_t v___x_517_; 
v___x_516_ = 90;
v___x_517_ = lean_uint8_dec_le(v_c_509_, v___x_516_);
if (v___x_517_ == 0)
{
goto v___jp_510_;
}
else
{
goto v___jp_505_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_478_ = stack[0].m_obj;
uint8_t v_res_522_;
v_res_522_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(v_s_478_);
stack->m_num = v_res_522_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(v_s_523_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(lean_object* v_s_526_, lean_object* v_h_527_){
_start:
{
uint32_t v___y_537_; uint32_t v___y_542_; lean_object* v___x_557_; uint8_t v_c_558_; uint8_t v___x_567_; uint8_t v___x_568_; 
v___x_557_ = lean_unsigned_to_nat(0u);
v_c_558_ = lean_string_get_byte_fast(v_s_526_, v___x_557_);
v___x_567_ = 97;
v___x_568_ = lean_uint8_dec_le(v___x_567_, v_c_558_);
if (v___x_568_ == 0)
{
goto v___jp_562_;
}
else
{
uint8_t v___x_569_; uint8_t v___x_570_; 
v___x_569_ = 122;
v___x_570_ = lean_uint8_dec_le(v_c_558_, v___x_569_);
if (v___x_570_ == 0)
{
goto v___jp_562_;
}
else
{
goto v___jp_554_;
}
}
v___jp_528_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_string_utf8_byte_size(v_s_526_);
v___x_531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_531_, 0, v_s_526_);
lean_ctor_set(v___x_531_, 1, v___x_529_);
lean_ctor_set(v___x_531_, 2, v___x_530_);
v___x_532_ = lean_unsigned_to_nat(1u);
v___x_533_ = lean_substring_drop(v___x_531_, v___x_532_);
v___x_534_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_535_ = lean_substring_all(v___x_533_, v___x_534_);
return v___x_535_;
}
v___jp_536_:
{
uint32_t v___x_538_; uint8_t v___x_539_; 
v___x_538_ = 95;
v___x_539_ = lean_uint32_dec_eq(v___y_537_, v___x_538_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; 
v___x_540_ = l_Lean_isLetterLike(v___y_537_);
if (v___x_540_ == 0)
{
lean_dec_ref(v_s_526_);
return v___x_540_;
}
else
{
goto v___jp_528_;
}
}
else
{
goto v___jp_528_;
}
}
v___jp_541_:
{
uint32_t v___x_543_; uint8_t v___x_544_; 
v___x_543_ = 97;
v___x_544_ = lean_uint32_dec_le(v___x_543_, v___y_542_);
if (v___x_544_ == 0)
{
v___y_537_ = v___y_542_;
goto v___jp_536_;
}
else
{
uint32_t v___x_545_; uint8_t v___x_546_; 
v___x_545_ = 122;
v___x_546_ = lean_uint32_dec_le(v___y_542_, v___x_545_);
if (v___x_546_ == 0)
{
v___y_537_ = v___y_542_;
goto v___jp_536_;
}
else
{
goto v___jp_528_;
}
}
}
v___jp_547_:
{
lean_object* v___x_548_; uint32_t v___x_549_; uint32_t v___x_550_; uint8_t v___x_551_; 
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_string_utf8_get(v_s_526_, v___x_548_);
v___x_550_ = 65;
v___x_551_ = lean_uint32_dec_le(v___x_550_, v___x_549_);
if (v___x_551_ == 0)
{
v___y_542_ = v___x_549_;
goto v___jp_541_;
}
else
{
uint32_t v___x_552_; uint8_t v___x_553_; 
v___x_552_ = 90;
v___x_553_ = lean_uint32_dec_le(v___x_549_, v___x_552_);
if (v___x_553_ == 0)
{
v___y_542_ = v___x_549_;
goto v___jp_541_;
}
else
{
goto v___jp_528_;
}
}
}
v___jp_554_:
{
lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_526_, v___x_555_);
if (v___x_556_ == 0)
{
goto v___jp_547_;
}
else
{
lean_dec_ref(v_s_526_);
return v___x_556_;
}
}
v___jp_559_:
{
uint8_t v___x_560_; uint8_t v___x_561_; 
v___x_560_ = 95;
v___x_561_ = lean_uint8_dec_eq(v_c_558_, v___x_560_);
if (v___x_561_ == 0)
{
goto v___jp_547_;
}
else
{
goto v___jp_554_;
}
}
v___jp_562_:
{
uint8_t v___x_563_; uint8_t v___x_564_; 
v___x_563_ = 65;
v___x_564_ = lean_uint8_dec_le(v___x_563_, v_c_558_);
if (v___x_564_ == 0)
{
goto v___jp_559_;
}
else
{
uint8_t v___x_565_; uint8_t v___x_566_; 
v___x_565_ = 90;
v___x_566_ = lean_uint8_dec_le(v_c_558_, v___x_565_);
if (v___x_566_ == 0)
{
goto v___jp_559_;
}
else
{
goto v___jp_554_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_526_ = stack[0].m_obj;
uint8_t v_res_571_;
v_res_571_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(v_s_526_, lean_box(0));
stack->m_num = v_res_571_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_572_, lean_object* v_h_573_){
_start:
{
uint8_t v_res_574_; lean_object* v_r_575_; 
v_res_574_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(v_s_572_, v_h_573_);
v_r_575_ = lean_box(v_res_574_);
return v_r_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape(lean_object* v_s_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_579_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_580_ = lean_string_append(v___x_579_, v_s_578_);
v___x_581_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_582_ = lean_string_append(v___x_580_, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___boxed(lean_object* v_s_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___private_Init_Meta_Defs_0__Lean_Name_escape(v_s_583_);
lean_dec_ref(v_s_583_);
return v_res_584_;
}
}
lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(lean_object* v_s_586_, uint8_t v_force_587_){
_start:
{
uint8_t v___y_598_; uint32_t v___y_609_; uint32_t v___y_614_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_string_utf8_byte_size(v_s_586_);
v___x_631_ = lean_nat_dec_lt(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_632_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_633_ = lean_string_append(v___x_632_, v_s_586_);
lean_dec_ref(v_s_586_);
v___x_634_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_635_ = lean_string_append(v___x_633_, v___x_634_);
v___x_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
else
{
if (v_force_587_ == 0)
{
uint8_t v_c_637_; uint8_t v___x_646_; uint8_t v___x_647_; 
v_c_637_ = lean_string_get_byte_fast(v_s_586_, v___x_629_);
v___x_646_ = 97;
v___x_647_ = lean_uint8_dec_le(v___x_646_, v_c_637_);
if (v___x_647_ == 0)
{
goto v___jp_641_;
}
else
{
uint8_t v___x_648_; uint8_t v___x_649_; 
v___x_648_ = 122;
v___x_649_ = lean_uint8_dec_le(v_c_637_, v___x_648_);
if (v___x_649_ == 0)
{
goto v___jp_641_;
}
else
{
goto v___jp_626_;
}
}
v___jp_638_:
{
uint8_t v___x_639_; uint8_t v___x_640_; 
v___x_639_ = 95;
v___x_640_ = lean_uint8_dec_eq(v_c_637_, v___x_639_);
if (v___x_640_ == 0)
{
goto v___jp_619_;
}
else
{
goto v___jp_626_;
}
}
v___jp_641_:
{
uint8_t v___x_642_; uint8_t v___x_643_; 
v___x_642_ = 65;
v___x_643_ = lean_uint8_dec_le(v___x_642_, v_c_637_);
if (v___x_643_ == 0)
{
goto v___jp_638_;
}
else
{
uint8_t v___x_644_; uint8_t v___x_645_; 
v___x_644_ = 90;
v___x_645_ = lean_uint8_dec_le(v_c_637_, v___x_644_);
if (v___x_645_ == 0)
{
goto v___jp_638_;
}
else
{
goto v___jp_626_;
}
}
}
}
else
{
goto v___jp_588_;
}
}
v___jp_588_:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0));
lean_inc_ref(v_s_586_);
v___x_590_ = lean_string_any(v_s_586_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_591_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_592_ = lean_string_append(v___x_591_, v_s_586_);
lean_dec_ref(v_s_586_);
v___x_593_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_594_ = lean_string_append(v___x_592_, v___x_593_);
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
else
{
lean_object* v___x_596_; 
lean_dec_ref(v_s_586_);
v___x_596_ = lean_box(0);
return v___x_596_;
}
}
v___jp_597_:
{
if (v___y_598_ == 0)
{
goto v___jp_588_;
}
else
{
lean_object* v___x_599_; 
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v_s_586_);
return v___x_599_;
}
}
v___jp_600_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_string_utf8_byte_size(v_s_586_);
lean_inc_ref(v_s_586_);
v___x_603_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_603_, 0, v_s_586_);
lean_ctor_set(v___x_603_, 1, v___x_601_);
lean_ctor_set(v___x_603_, 2, v___x_602_);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_substring_drop(v___x_603_, v___x_604_);
v___x_606_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_607_ = lean_substring_all(v___x_605_, v___x_606_);
v___y_598_ = v___x_607_;
goto v___jp_597_;
}
v___jp_608_:
{
uint32_t v___x_610_; uint8_t v___x_611_; 
v___x_610_ = 95;
v___x_611_ = lean_uint32_dec_eq(v___y_609_, v___x_610_);
if (v___x_611_ == 0)
{
uint8_t v___x_612_; 
v___x_612_ = l_Lean_isLetterLike(v___y_609_);
if (v___x_612_ == 0)
{
v___y_598_ = v___x_612_;
goto v___jp_597_;
}
else
{
goto v___jp_600_;
}
}
else
{
goto v___jp_600_;
}
}
v___jp_613_:
{
uint32_t v___x_615_; uint8_t v___x_616_; 
v___x_615_ = 97;
v___x_616_ = lean_uint32_dec_le(v___x_615_, v___y_614_);
if (v___x_616_ == 0)
{
v___y_609_ = v___y_614_;
goto v___jp_608_;
}
else
{
uint32_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = 122;
v___x_618_ = lean_uint32_dec_le(v___y_614_, v___x_617_);
if (v___x_618_ == 0)
{
v___y_609_ = v___y_614_;
goto v___jp_608_;
}
else
{
goto v___jp_600_;
}
}
}
v___jp_619_:
{
lean_object* v___x_620_; uint32_t v___x_621_; uint32_t v___x_622_; uint8_t v___x_623_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_string_utf8_get(v_s_586_, v___x_620_);
v___x_622_ = 65;
v___x_623_ = lean_uint32_dec_le(v___x_622_, v___x_621_);
if (v___x_623_ == 0)
{
v___y_614_ = v___x_621_;
goto v___jp_613_;
}
else
{
uint32_t v___x_624_; uint8_t v___x_625_; 
v___x_624_ = 90;
v___x_625_ = lean_uint32_dec_le(v___x_621_, v___x_624_);
if (v___x_625_ == 0)
{
v___y_614_ = v___x_621_;
goto v___jp_613_;
}
else
{
goto v___jp_600_;
}
}
}
v___jp_626_:
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_586_, v___x_627_);
if (v___x_628_ == 0)
{
goto v___jp_619_;
}
else
{
v___y_598_ = v___x_628_;
goto v___jp_597_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_586_ = stack[0].m_obj;
uint8_t v_force_587_ = stack[1].m_num;
lean_object* v_res_650_;
v_res_650_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(v_s_586_, v_force_587_);
stack->m_obj
 = v_res_650_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object* v_s_651_, lean_object* v_force_652_){
_start:
{
uint8_t v_force_boxed_653_; lean_object* v_res_654_; 
v_force_boxed_653_ = lean_unbox(v_force_652_);
v_res_654_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(v_s_651_, v_force_boxed_653_);
return v_res_654_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t v___y_655_){
_start:
{
uint32_t v___x_656_; uint8_t v___x_657_; 
v___x_656_ = 187;
v___x_657_ = lean_uint32_dec_eq(v___y_655_, v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v___y_655_ = stack[0].m_num;
uint8_t v_res_658_;
v_res_658_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(v___y_655_);
stack->m_num = v_res_658_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object* v___y_659_){
_start:
{
uint32_t v___y_272__boxed_660_; uint8_t v_res_661_; lean_object* v_r_662_; 
v___y_272__boxed_660_ = lean_unbox_uint32(v___y_659_);
lean_dec(v___y_659_);
v_res_661_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(v___y_272__boxed_660_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t v___y_663_){
_start:
{
uint32_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = 65;
v___x_686_ = lean_uint32_dec_le(v___x_685_, v___y_663_);
if (v___x_686_ == 0)
{
goto v___jp_680_;
}
else
{
uint32_t v___x_687_; uint8_t v___x_688_; 
v___x_687_ = 90;
v___x_688_ = lean_uint32_dec_le(v___y_663_, v___x_687_);
if (v___x_688_ == 0)
{
goto v___jp_680_;
}
else
{
return v___x_688_;
}
}
v___jp_664_:
{
uint32_t v___x_665_; uint8_t v___x_666_; 
v___x_665_ = 95;
v___x_666_ = lean_uint32_dec_eq(v___y_663_, v___x_665_);
if (v___x_666_ == 0)
{
uint32_t v___x_667_; uint8_t v___x_668_; 
v___x_667_ = 39;
v___x_668_ = lean_uint32_dec_eq(v___y_663_, v___x_667_);
if (v___x_668_ == 0)
{
uint32_t v___x_669_; uint8_t v___x_670_; 
v___x_669_ = 33;
v___x_670_ = lean_uint32_dec_eq(v___y_663_, v___x_669_);
if (v___x_670_ == 0)
{
uint32_t v___x_671_; uint8_t v___x_672_; 
v___x_671_ = 63;
v___x_672_ = lean_uint32_dec_eq(v___y_663_, v___x_671_);
if (v___x_672_ == 0)
{
uint8_t v___x_673_; 
v___x_673_ = l_Lean_isLetterLike(v___y_663_);
if (v___x_673_ == 0)
{
uint8_t v___x_674_; 
v___x_674_ = l_Lean_isSubScriptAlnum(v___y_663_);
return v___x_674_;
}
else
{
return v___x_673_;
}
}
else
{
return v___x_672_;
}
}
else
{
return v___x_670_;
}
}
else
{
return v___x_668_;
}
}
else
{
return v___x_666_;
}
}
v___jp_675_:
{
uint32_t v___x_676_; uint8_t v___x_677_; 
v___x_676_ = 48;
v___x_677_ = lean_uint32_dec_le(v___x_676_, v___y_663_);
if (v___x_677_ == 0)
{
goto v___jp_664_;
}
else
{
uint32_t v___x_678_; uint8_t v___x_679_; 
v___x_678_ = 57;
v___x_679_ = lean_uint32_dec_le(v___y_663_, v___x_678_);
if (v___x_679_ == 0)
{
goto v___jp_664_;
}
else
{
return v___x_679_;
}
}
}
v___jp_680_:
{
uint32_t v___x_681_; uint8_t v___x_682_; 
v___x_681_ = 97;
v___x_682_ = lean_uint32_dec_le(v___x_681_, v___y_663_);
if (v___x_682_ == 0)
{
goto v___jp_675_;
}
else
{
uint32_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = 122;
v___x_684_ = lean_uint32_dec_le(v___y_663_, v___x_683_);
if (v___x_684_ == 0)
{
goto v___jp_675_;
}
else
{
return v___x_684_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1_0interp(lean_interpreter_value* stack)
{
uint32_t v___y_663_ = stack[0].m_num;
uint8_t v_res_689_;
v_res_689_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(v___y_663_);
stack->m_num = v_res_689_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object* v___y_690_){
_start:
{
uint32_t v___y_283__boxed_691_; uint8_t v_res_692_; lean_object* v_r_693_; 
v___y_283__boxed_691_ = lean_unbox_uint32(v___y_690_);
lean_dec(v___y_690_);
v_res_692_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(v___y_283__boxed_691_);
v_r_693_ = lean_box(v_res_692_);
return v_r_693_;
}
}
lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t v_escape_696_, lean_object* v_s_697_, uint8_t v_force_698_){
_start:
{
if (v_escape_696_ == 0)
{
return v_s_697_;
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_string_utf8_byte_size(v_s_697_);
v___x_701_ = lean_nat_dec_lt(v___x_699_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_702_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_703_ = lean_string_append(v___x_702_, v_s_697_);
lean_dec_ref(v_s_697_);
v___x_704_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_705_ = lean_string_append(v___x_703_, v___x_704_);
return v___x_705_;
}
else
{
lean_object* v___f_706_; uint8_t v___y_714_; 
v___f_706_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
if (v_force_698_ == 0)
{
lean_object* v___f_715_; uint32_t v___y_722_; uint32_t v___y_727_; uint8_t v_c_741_; uint8_t v___x_750_; uint8_t v___x_751_; 
v___f_715_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_741_ = lean_string_get_byte_fast(v_s_697_, v___x_699_);
v___x_750_ = 97;
v___x_751_ = lean_uint8_dec_le(v___x_750_, v_c_741_);
if (v___x_751_ == 0)
{
goto v___jp_745_;
}
else
{
uint8_t v___x_752_; uint8_t v___x_753_; 
v___x_752_ = 122;
v___x_753_ = lean_uint8_dec_le(v_c_741_, v___x_752_);
if (v___x_753_ == 0)
{
goto v___jp_745_;
}
else
{
goto v___jp_738_;
}
}
v___jp_716_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
lean_inc_ref(v_s_697_);
v___x_717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_717_, 0, v_s_697_);
lean_ctor_set(v___x_717_, 1, v___x_699_);
lean_ctor_set(v___x_717_, 2, v___x_700_);
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_substring_drop(v___x_717_, v___x_718_);
v___x_720_ = lean_substring_all(v___x_719_, v___f_715_);
v___y_714_ = v___x_720_;
goto v___jp_713_;
}
v___jp_721_:
{
uint32_t v___x_723_; uint8_t v___x_724_; 
v___x_723_ = 95;
v___x_724_ = lean_uint32_dec_eq(v___y_722_, v___x_723_);
if (v___x_724_ == 0)
{
uint8_t v___x_725_; 
v___x_725_ = l_Lean_isLetterLike(v___y_722_);
if (v___x_725_ == 0)
{
v___y_714_ = v___x_725_;
goto v___jp_713_;
}
else
{
goto v___jp_716_;
}
}
else
{
goto v___jp_716_;
}
}
v___jp_726_:
{
uint32_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 97;
v___x_729_ = lean_uint32_dec_le(v___x_728_, v___y_727_);
if (v___x_729_ == 0)
{
v___y_722_ = v___y_727_;
goto v___jp_721_;
}
else
{
uint32_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = 122;
v___x_731_ = lean_uint32_dec_le(v___y_727_, v___x_730_);
if (v___x_731_ == 0)
{
v___y_722_ = v___y_727_;
goto v___jp_721_;
}
else
{
goto v___jp_716_;
}
}
}
v___jp_732_:
{
uint32_t v___x_733_; uint32_t v___x_734_; uint8_t v___x_735_; 
v___x_733_ = lean_string_utf8_get(v_s_697_, v___x_699_);
v___x_734_ = 65;
v___x_735_ = lean_uint32_dec_le(v___x_734_, v___x_733_);
if (v___x_735_ == 0)
{
v___y_727_ = v___x_733_;
goto v___jp_726_;
}
else
{
uint32_t v___x_736_; uint8_t v___x_737_; 
v___x_736_ = 90;
v___x_737_ = lean_uint32_dec_le(v___x_733_, v___x_736_);
if (v___x_737_ == 0)
{
v___y_727_ = v___x_733_;
goto v___jp_726_;
}
else
{
goto v___jp_716_;
}
}
}
v___jp_738_:
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_697_, v___x_739_);
if (v___x_740_ == 0)
{
goto v___jp_732_;
}
else
{
v___y_714_ = v___x_740_;
goto v___jp_713_;
}
}
v___jp_742_:
{
uint8_t v___x_743_; uint8_t v___x_744_; 
v___x_743_ = 95;
v___x_744_ = lean_uint8_dec_eq(v_c_741_, v___x_743_);
if (v___x_744_ == 0)
{
goto v___jp_732_;
}
else
{
goto v___jp_738_;
}
}
v___jp_745_:
{
uint8_t v___x_746_; uint8_t v___x_747_; 
v___x_746_ = 65;
v___x_747_ = lean_uint8_dec_le(v___x_746_, v_c_741_);
if (v___x_747_ == 0)
{
goto v___jp_742_;
}
else
{
uint8_t v___x_748_; uint8_t v___x_749_; 
v___x_748_ = 90;
v___x_749_ = lean_uint8_dec_le(v_c_741_, v___x_748_);
if (v___x_749_ == 0)
{
goto v___jp_742_;
}
else
{
goto v___jp_738_;
}
}
}
}
else
{
goto v___jp_707_;
}
v___jp_707_:
{
uint8_t v___x_708_; 
lean_inc_ref(v_s_697_);
v___x_708_ = lean_string_any(v_s_697_, v___f_706_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_709_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_710_ = lean_string_append(v___x_709_, v_s_697_);
lean_dec_ref(v_s_697_);
v___x_711_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_712_ = lean_string_append(v___x_710_, v___x_711_);
return v___x_712_;
}
else
{
return v_s_697_;
}
}
v___jp_713_:
{
if (v___y_714_ == 0)
{
goto v___jp_707_;
}
else
{
return v_s_697_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape_0interp(lean_interpreter_value* stack)
{
uint8_t v_escape_696_ = stack[0].m_num;
lean_object* v_s_697_ = stack[1].m_obj;
uint8_t v_force_698_ = stack[2].m_num;
lean_object* v_res_754_;
v_res_754_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_696_, v_s_697_, v_force_698_);
stack->m_obj
 = v_res_754_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_755_, lean_object* v_s_756_, lean_object* v_force_757_){
_start:
{
uint8_t v_escape_boxed_758_; uint8_t v_force_boxed_759_; lean_object* v_res_760_; 
v_escape_boxed_758_ = lean_unbox(v_escape_755_);
v_force_boxed_759_ = lean_unbox(v_force_757_);
v_res_760_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_boxed_758_, v_s_756_, v_force_boxed_759_);
return v_res_760_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object* v_x_761_){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = 0;
return v___x_762_;
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_761_ = stack[0].m_obj;
uint8_t v_res_763_;
v_res_763_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(v_x_761_);
stack->m_num = v_res_763_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed(lean_object* v_x_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(v_x_764_);
lean_dec_ref(v_x_764_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object* v_sep_769_, uint8_t v_escape_770_, lean_object* v_n_771_, lean_object* v_isToken_772_){
_start:
{
switch(lean_obj_tag(v_n_771_))
{
case 0:
{
lean_object* v___x_773_; 
lean_dec_ref(v_isToken_772_);
v___x_773_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_773_;
}
case 1:
{
lean_object* v_pre_774_; 
v_pre_774_ = lean_ctor_get(v_n_771_, 0);
if (lean_obj_tag(v_pre_774_) == 0)
{
lean_object* v_str_775_; lean_object* v___x_776_; uint8_t v___x_777_; lean_object* v___x_778_; 
v_str_775_ = lean_ctor_get(v_n_771_, 1);
lean_inc_ref_n(v_str_775_, 2);
lean_dec_ref_known(v_n_771_, 2);
v___x_776_ = lean_apply_1(v_isToken_772_, v_str_775_);
v___x_777_ = lean_unbox(v___x_776_);
v___x_778_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_770_, v_str_775_, v___x_777_);
return v___x_778_;
}
else
{
lean_object* v_str_779_; lean_object* v_r_780_; lean_object* v___x_781_; uint8_t v___x_782_; lean_object* v___x_783_; lean_object* v_r_x27_784_; 
lean_inc(v_pre_774_);
v_str_779_ = lean_ctor_get(v_n_771_, 1);
lean_inc_ref_n(v_str_779_, 2);
lean_dec_ref_known(v_n_771_, 2);
lean_inc_ref(v_isToken_772_);
v_r_780_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_769_, v_escape_770_, v_pre_774_, v_isToken_772_);
v___x_781_ = lean_string_append(v_r_780_, v_sep_769_);
v___x_782_ = 0;
v___x_783_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_770_, v_str_779_, v___x_782_);
lean_inc_ref(v___x_781_);
v_r_x27_784_ = lean_string_append(v___x_781_, v___x_783_);
lean_dec_ref(v___x_783_);
if (v_escape_770_ == 0)
{
lean_dec_ref(v___x_781_);
lean_dec_ref(v_str_779_);
lean_dec_ref(v_isToken_772_);
return v_r_x27_784_;
}
else
{
lean_object* v___x_785_; uint8_t v___x_786_; 
lean_inc_ref(v_r_x27_784_);
v___x_785_ = lean_apply_1(v_isToken_772_, v_r_x27_784_);
v___x_786_ = lean_unbox(v___x_785_);
if (v___x_786_ == 0)
{
lean_dec_ref(v___x_781_);
lean_dec_ref(v_str_779_);
return v_r_x27_784_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref(v_r_x27_784_);
v___x_787_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_770_, v_str_779_, v_escape_770_);
v___x_788_ = lean_string_append(v___x_781_, v___x_787_);
lean_dec_ref(v___x_787_);
return v___x_788_;
}
}
}
}
default: 
{
lean_object* v_pre_789_; 
lean_dec_ref(v_isToken_772_);
v_pre_789_ = lean_ctor_get(v_n_771_, 0);
if (lean_obj_tag(v_pre_789_) == 0)
{
lean_object* v_i_790_; lean_object* v___x_791_; 
v_i_790_ = lean_ctor_get(v_n_771_, 1);
lean_inc(v_i_790_);
lean_dec_ref_known(v_n_771_, 2);
v___x_791_ = l_Nat_reprFast(v_i_790_);
return v___x_791_;
}
else
{
lean_object* v_i_792_; lean_object* v___f_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_inc(v_pre_789_);
v_i_792_ = lean_ctor_get(v_n_771_, 1);
lean_inc(v_i_792_);
lean_dec_ref_known(v_n_771_, 2);
v___f_793_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1));
v___x_794_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_769_, v_escape_770_, v_pre_789_, v___f_793_);
v___x_795_ = lean_string_append(v___x_794_, v_sep_769_);
v___x_796_ = l_Nat_reprFast(v_i_792_);
v___x_797_ = lean_string_append(v___x_795_, v___x_796_);
lean_dec_ref(v___x_796_);
return v___x_797_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_0interp(lean_interpreter_value* stack)
{
lean_object* v_sep_769_ = stack[0].m_obj;
uint8_t v_escape_770_ = stack[1].m_num;
lean_object* v_n_771_ = stack[2].m_obj;
lean_object* v_isToken_772_ = stack[3].m_obj;
lean_object* v_res_798_;
v_res_798_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_769_, v_escape_770_, v_n_771_, v_isToken_772_);
stack->m_obj
 = v_res_798_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object* v_sep_799_, lean_object* v_escape_800_, lean_object* v_n_801_, lean_object* v_isToken_802_){
_start:
{
uint8_t v_escape_boxed_803_; lean_object* v_res_804_; 
v_escape_boxed_803_ = lean_unbox(v_escape_800_);
v_res_804_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_799_, v_escape_boxed_803_, v_n_801_, v_isToken_802_);
lean_dec_ref(v_sep_799_);
return v_res_804_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object* v_n_810_){
_start:
{
lean_object* v___x_811_; uint8_t v___x_812_; uint8_t v___x_813_; 
v___x_811_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_812_ = lean_name_eq(v_n_810_, v___x_811_);
v___x_813_ = 1;
if (v___x_812_ == 0)
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Name_getRoot(v_n_810_);
if (lean_obj_tag(v___x_814_) == 1)
{
lean_object* v_str_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_str_815_ = lean_ctor_get(v___x_814_, 1);
lean_inc_ref_n(v_str_815_, 2);
lean_dec_ref_known(v___x_814_, 2);
v___x_816_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_817_ = lean_string_isprefixof(v___x_816_, v_str_815_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3));
v___x_819_ = lean_string_isprefixof(v___x_818_, v_str_815_);
return v___x_819_;
}
else
{
lean_dec_ref(v_str_815_);
return v___x_813_;
}
}
else
{
lean_dec(v___x_814_);
return v___x_812_;
}
}
else
{
return v___x_813_;
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_810_ = stack[0].m_obj;
uint8_t v_res_820_;
v_res_820_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_810_);
stack->m_num = v_res_820_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_821_);
lean_dec(v_n_821_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object* v_n_824_, uint8_t v_escape_825_, lean_object* v_isToken_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_825_ == 0)
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_827_, v_escape_825_, v_n_824_, v_isToken_826_);
return v___x_828_;
}
else
{
uint8_t v___x_829_; 
lean_inc(v_n_824_);
v___x_829_ = l_Lean_Name_isInaccessibleUserName(v_n_824_);
if (v___x_829_ == 0)
{
uint8_t v___x_830_; 
v___x_830_ = l_Lean_Name_hasMacroScopes(v_n_824_);
if (v___x_830_ == 0)
{
uint8_t v___x_831_; 
v___x_831_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_824_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
v___x_832_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_827_, v_escape_825_, v_n_824_, v_isToken_826_);
return v___x_832_;
}
else
{
lean_object* v___x_833_; 
v___x_833_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_827_, v___x_830_, v_n_824_, v_isToken_826_);
return v___x_833_;
}
}
else
{
lean_object* v___x_834_; 
v___x_834_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_827_, v___x_829_, v_n_824_, v_isToken_826_);
return v___x_834_;
}
}
else
{
uint8_t v___x_835_; lean_object* v___x_836_; 
v___x_835_ = 0;
v___x_836_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_827_, v___x_835_, v_n_824_, v_isToken_826_);
return v___x_836_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_824_ = stack[0].m_obj;
uint8_t v_escape_825_ = stack[1].m_num;
lean_object* v_isToken_826_ = stack[2].m_obj;
lean_object* v_res_837_;
v_res_837_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(v_n_824_, v_escape_825_, v_isToken_826_);
stack->m_obj
 = v_res_837_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object* v_n_838_, lean_object* v_escape_839_, lean_object* v_isToken_840_){
_start:
{
uint8_t v_escape_boxed_841_; lean_object* v_res_842_; 
v_escape_boxed_841_ = lean_unbox(v_escape_839_);
v_res_842_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(v_n_838_, v_escape_boxed_841_, v_isToken_840_);
return v_res_842_;
}
}
lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object* v_sep_843_, uint8_t v_escape_844_, lean_object* v_n_845_){
_start:
{
switch(lean_obj_tag(v_n_845_))
{
case 0:
{
lean_object* v___x_846_; 
v___x_846_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_846_;
}
case 1:
{
lean_object* v_pre_847_; 
v_pre_847_ = lean_ctor_get(v_n_845_, 0);
if (lean_obj_tag(v_pre_847_) == 0)
{
lean_object* v_str_848_; uint8_t v___x_849_; lean_object* v___x_850_; 
v_str_848_ = lean_ctor_get(v_n_845_, 1);
lean_inc_ref(v_str_848_);
lean_dec_ref_known(v_n_845_, 2);
v___x_849_ = 0;
v___x_850_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_844_, v_str_848_, v___x_849_);
return v___x_850_;
}
else
{
lean_object* v_str_851_; lean_object* v_r_852_; lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v_r_x27_856_; 
lean_inc(v_pre_847_);
v_str_851_ = lean_ctor_get(v_n_845_, 1);
lean_inc_ref(v_str_851_);
lean_dec_ref_known(v_n_845_, 2);
v_r_852_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_843_, v_escape_844_, v_pre_847_);
v___x_853_ = lean_string_append(v_r_852_, v_sep_843_);
v___x_854_ = 0;
v___x_855_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_844_, v_str_851_, v___x_854_);
v_r_x27_856_ = lean_string_append(v___x_853_, v___x_855_);
lean_dec_ref(v___x_855_);
return v_r_x27_856_;
}
}
default: 
{
lean_object* v_pre_857_; 
v_pre_857_ = lean_ctor_get(v_n_845_, 0);
if (lean_obj_tag(v_pre_857_) == 0)
{
lean_object* v_i_858_; lean_object* v___x_859_; 
v_i_858_ = lean_ctor_get(v_n_845_, 1);
lean_inc(v_i_858_);
lean_dec_ref_known(v_n_845_, 2);
v___x_859_ = l_Nat_reprFast(v_i_858_);
return v___x_859_;
}
else
{
lean_object* v_i_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_inc(v_pre_857_);
v_i_860_ = lean_ctor_get(v_n_845_, 1);
lean_inc(v_i_860_);
lean_dec_ref_known(v_n_845_, 2);
v___x_861_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_843_, v_escape_844_, v_pre_857_);
v___x_862_ = lean_string_append(v___x_861_, v_sep_843_);
v___x_863_ = l_Nat_reprFast(v_i_860_);
v___x_864_ = lean_string_append(v___x_862_, v___x_863_);
lean_dec_ref(v___x_863_);
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_sep_843_ = stack[0].m_obj;
uint8_t v_escape_844_ = stack[1].m_num;
lean_object* v_n_845_ = stack[2].m_obj;
lean_object* v_res_865_;
v_res_865_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_843_, v_escape_844_, v_n_845_);
stack->m_obj
 = v_res_865_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object* v_sep_866_, lean_object* v_escape_867_, lean_object* v_n_868_){
_start:
{
uint8_t v_escape_boxed_869_; lean_object* v_res_870_; 
v_escape_boxed_869_ = lean_unbox(v_escape_867_);
v_res_870_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_866_, v_escape_boxed_869_, v_n_868_);
lean_dec_ref(v_sep_866_);
return v_res_870_;
}
}
lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object* v_n_871_, uint8_t v_escape_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_872_ == 0)
{
lean_object* v___x_874_; 
v___x_874_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_873_, v_escape_872_, v_n_871_);
return v___x_874_;
}
else
{
uint8_t v___x_875_; 
lean_inc(v_n_871_);
v___x_875_ = l_Lean_Name_isInaccessibleUserName(v_n_871_);
if (v___x_875_ == 0)
{
uint8_t v___x_876_; 
v___x_876_ = l_Lean_Name_hasMacroScopes(v_n_871_);
if (v___x_876_ == 0)
{
uint8_t v___x_877_; 
v___x_877_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_871_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
v___x_878_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_873_, v_escape_872_, v_n_871_);
return v___x_878_;
}
else
{
lean_object* v___x_879_; 
v___x_879_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_873_, v___x_876_, v_n_871_);
return v___x_879_;
}
}
else
{
lean_object* v___x_880_; 
v___x_880_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_873_, v___x_875_, v_n_871_);
return v___x_880_;
}
}
else
{
uint8_t v___x_881_; lean_object* v___x_882_; 
v___x_881_ = 0;
v___x_882_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_873_, v___x_881_, v_n_871_);
return v___x_882_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_871_ = stack[0].m_obj;
uint8_t v_escape_872_ = stack[1].m_num;
lean_object* v_res_883_;
v_res_883_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_871_, v_escape_872_);
stack->m_obj
 = v_res_883_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object* v_n_884_, lean_object* v_escape_885_){
_start:
{
uint8_t v_escape_boxed_886_; lean_object* v_res_887_; 
v_escape_boxed_886_ = lean_unbox(v_escape_885_);
v_res_887_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_884_, v_escape_boxed_886_);
return v_res_887_;
}
}
lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object* v_n_888_, uint8_t v_escape_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_888_, v_escape_889_);
return v___x_890_;
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_888_ = stack[0].m_obj;
uint8_t v_escape_889_ = stack[1].m_num;
lean_object* v_res_891_;
v_res_891_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(v_n_888_, v_escape_889_);
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object* v_n_892_, lean_object* v_escape_893_){
_start:
{
uint8_t v_escape_boxed_894_; lean_object* v_res_895_; 
v_escape_boxed_894_ = lean_unbox(v_escape_893_);
v_res_895_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(v_n_892_, v_escape_boxed_894_);
return v_res_895_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_Name_hasNum(lean_object* v_x_896_){
_start:
{
switch(lean_obj_tag(v_x_896_))
{
case 0:
{
uint8_t v___x_897_; 
v___x_897_ = 0;
return v___x_897_;
}
case 1:
{
lean_object* v_pre_898_; 
v_pre_898_ = lean_ctor_get(v_x_896_, 0);
v_x_896_ = v_pre_898_;
goto _start;
}
default: 
{
uint8_t v___x_900_; 
v___x_900_ = 1;
return v___x_900_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Name_hasNum_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_896_ = stack[0].m_obj;
uint8_t v_res_901_;
v_res_901_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_x_896_);
stack->m_num = v_res_901_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_hasNum___boxed(lean_object* v_x_902_){
_start:
{
uint8_t v_res_903_; lean_object* v_r_904_; 
v_res_903_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_x_902_);
lean_dec(v_x_902_);
v_r_904_ = lean_box(v_res_903_);
return v_r_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object* v_n_920_, lean_object* v_prec_921_){
_start:
{
switch(lean_obj_tag(v_n_920_))
{
case 0:
{
lean_object* v___x_922_; 
v___x_922_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__1));
return v___x_922_;
}
case 1:
{
lean_object* v_pre_923_; lean_object* v_str_924_; uint8_t v___x_925_; 
v_pre_923_ = lean_ctor_get(v_n_920_, 0);
v_str_924_ = lean_ctor_get(v_n_920_, 1);
v___x_925_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_pre_923_);
if (v___x_925_ == 0)
{
uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_926_ = 1;
v___x_927_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__3));
v___x_928_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_920_, v___x_926_);
v___x_929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
v___x_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_927_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
lean_inc_ref(v_str_924_);
lean_inc(v_pre_923_);
lean_dec_ref_known(v_n_920_, 2);
v___x_931_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__5));
v___x_932_ = lean_unsigned_to_nat(1024u);
v___x_933_ = l_Lean_Name_reprPrec(v_pre_923_, v___x_932_);
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_931_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = l_String_quote(v_str_924_);
v___x_938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
v___x_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_936_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = l_Repr_addAppParen(v___x_939_, v_prec_921_);
return v___x_940_;
}
}
default: 
{
lean_object* v_pre_941_; lean_object* v_i_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_pre_941_ = lean_ctor_get(v_n_920_, 0);
lean_inc(v_pre_941_);
v_i_942_ = lean_ctor_get(v_n_920_, 1);
lean_inc(v_i_942_);
lean_dec_ref_known(v_n_920_, 2);
v___x_943_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__9));
v___x_944_ = lean_unsigned_to_nat(1024u);
v___x_945_ = l_Lean_Name_reprPrec(v_pre_941_, v___x_944_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_943_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = l_Nat_reprFast(v_i_942_);
v___x_950_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
v___x_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_948_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = l_Repr_addAppParen(v___x_951_, v_prec_921_);
return v___x_952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object* v_n_953_, lean_object* v_prec_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_Name_reprPrec(v_n_953_, v_prec_954_);
lean_dec(v_prec_954_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object* v_x_958_){
_start:
{
if (lean_obj_tag(v_x_958_) == 1)
{
lean_object* v_pre_959_; lean_object* v_str_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_pre_959_ = lean_ctor_get(v_x_958_, 0);
lean_inc(v_pre_959_);
v_str_960_ = lean_ctor_get(v_x_958_, 1);
lean_inc_ref(v_str_960_);
lean_dec_ref_known(v_x_958_, 2);
v___x_961_ = lean_string_capitalize(v_str_960_);
v___x_962_ = l_Lean_Name_str___override(v_pre_959_, v___x_961_);
return v___x_962_;
}
else
{
return v_x_958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object* v_x_963_, lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
switch(lean_obj_tag(v_x_963_))
{
case 0:
{
if (lean_obj_tag(v_x_964_) == 0)
{
lean_inc(v_x_965_);
return v_x_965_;
}
else
{
return v_x_963_;
}
}
case 1:
{
lean_object* v_pre_966_; lean_object* v_str_967_; uint8_t v___x_968_; 
v_pre_966_ = lean_ctor_get(v_x_963_, 0);
lean_inc(v_pre_966_);
v_str_967_ = lean_ctor_get(v_x_963_, 1);
lean_inc_ref(v_str_967_);
v___x_968_ = lean_name_eq(v_x_963_, v_x_964_);
lean_dec_ref_known(v_x_963_, 2);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = l_Lean_Name_replacePrefix(v_pre_966_, v_x_964_, v_x_965_);
v___x_970_ = l_Lean_Name_str___override(v___x_969_, v_str_967_);
return v___x_970_;
}
else
{
lean_dec_ref(v_str_967_);
lean_dec(v_pre_966_);
lean_inc(v_x_965_);
return v_x_965_;
}
}
default: 
{
lean_object* v_pre_971_; lean_object* v_i_972_; uint8_t v___x_973_; 
v_pre_971_ = lean_ctor_get(v_x_963_, 0);
lean_inc(v_pre_971_);
v_i_972_ = lean_ctor_get(v_x_963_, 1);
lean_inc(v_i_972_);
v___x_973_ = lean_name_eq(v_x_963_, v_x_964_);
lean_dec_ref_known(v_x_963_, 2);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = l_Lean_Name_replacePrefix(v_pre_971_, v_x_964_, v_x_965_);
v___x_975_ = l_Lean_Name_num___override(v___x_974_, v_i_972_);
return v___x_975_;
}
else
{
lean_dec(v_i_972_);
lean_dec(v_pre_971_);
lean_inc(v_x_965_);
return v_x_965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object* v_x_976_, lean_object* v_x_977_, lean_object* v_x_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Name_replacePrefix(v_x_976_, v_x_977_, v_x_978_);
lean_dec(v_x_978_);
lean_dec(v_x_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object* v_x_980_, lean_object* v_x_981_){
_start:
{
switch(lean_obj_tag(v_x_981_))
{
case 0:
{
lean_object* v___x_982_; 
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v_x_980_);
return v___x_982_;
}
case 1:
{
if (lean_obj_tag(v_x_980_) == 1)
{
lean_object* v_pre_983_; lean_object* v_str_984_; lean_object* v_pre_985_; lean_object* v_str_986_; uint8_t v___x_987_; 
v_pre_983_ = lean_ctor_get(v_x_981_, 0);
v_str_984_ = lean_ctor_get(v_x_981_, 1);
v_pre_985_ = lean_ctor_get(v_x_980_, 0);
lean_inc(v_pre_985_);
v_str_986_ = lean_ctor_get(v_x_980_, 1);
lean_inc_ref(v_str_986_);
lean_dec_ref_known(v_x_980_, 2);
v___x_987_ = lean_string_dec_eq(v_str_986_, v_str_984_);
lean_dec_ref(v_str_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
lean_dec(v_pre_985_);
v___x_988_ = lean_box(0);
return v___x_988_;
}
else
{
v_x_980_ = v_pre_985_;
v_x_981_ = v_pre_983_;
goto _start;
}
}
else
{
lean_object* v___x_990_; 
lean_dec(v_x_980_);
v___x_990_ = lean_box(0);
return v___x_990_;
}
}
default: 
{
if (lean_obj_tag(v_x_980_) == 2)
{
lean_object* v_pre_991_; lean_object* v_i_992_; lean_object* v_pre_993_; lean_object* v_i_994_; uint8_t v___x_995_; 
v_pre_991_ = lean_ctor_get(v_x_981_, 0);
v_i_992_ = lean_ctor_get(v_x_981_, 1);
v_pre_993_ = lean_ctor_get(v_x_980_, 0);
lean_inc(v_pre_993_);
v_i_994_ = lean_ctor_get(v_x_980_, 1);
lean_inc(v_i_994_);
lean_dec_ref_known(v_x_980_, 2);
v___x_995_ = lean_nat_dec_eq(v_i_994_, v_i_992_);
lean_dec(v_i_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; 
lean_dec(v_pre_993_);
v___x_996_ = lean_box(0);
return v___x_996_;
}
else
{
v_x_980_ = v_pre_993_;
v_x_981_ = v_pre_991_;
goto _start;
}
}
else
{
lean_object* v___x_998_; 
lean_dec(v_x_980_);
v___x_998_ = lean_box(0);
return v___x_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Name_eraseSuffix_x3f(v_x_999_, v_x_1000_);
lean_dec(v_x_1000_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object* v_n_1002_, lean_object* v_f_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = l_Lean_Name_hasMacroScopes(v_n_1002_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_apply_1(v_f_1003_, v_n_1002_);
return v___x_1005_;
}
else
{
lean_object* v_view_1006_; lean_object* v_name_1007_; lean_object* v_imported_1008_; lean_object* v_ctx_1009_; lean_object* v_scopes_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1019_; 
v_view_1006_ = l_Lean_extractMacroScopes(v_n_1002_);
v_name_1007_ = lean_ctor_get(v_view_1006_, 0);
v_imported_1008_ = lean_ctor_get(v_view_1006_, 1);
v_ctx_1009_ = lean_ctor_get(v_view_1006_, 2);
v_scopes_1010_ = lean_ctor_get(v_view_1006_, 3);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_view_1006_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1012_ = v_view_1006_;
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_scopes_1010_);
lean_inc(v_ctx_1009_);
lean_inc(v_imported_1008_);
lean_inc(v_name_1007_);
lean_dec(v_view_1006_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1014_ = lean_apply_1(v_f_1003_, v_name_1007_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1014_);
v___x_1016_ = v___x_1012_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_imported_1008_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v_ctx_1009_);
lean_ctor_set(v_reuseFailAlloc_1018_, 3, v_scopes_1010_);
v___x_1016_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_MacroScopesView_review(v___x_1016_);
return v___x_1017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object* v_suffix_1020_, lean_object* v_x_1021_){
_start:
{
if (lean_obj_tag(v_x_1021_) == 1)
{
lean_object* v_pre_1022_; lean_object* v_str_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_pre_1022_ = lean_ctor_get(v_x_1021_, 0);
lean_inc(v_pre_1022_);
v_str_1023_ = lean_ctor_get(v_x_1021_, 1);
lean_inc_ref(v_str_1023_);
lean_dec_ref_known(v_x_1021_, 2);
v___x_1024_ = lean_string_append(v_str_1023_, v_suffix_1020_);
lean_dec_ref(v_suffix_1020_);
v___x_1025_ = l_Lean_Name_str___override(v_pre_1022_, v___x_1024_);
return v___x_1025_;
}
else
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_Name_str___override(v_x_1021_, v_suffix_1020_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_after(lean_object* v_n_1027_, lean_object* v_suffix_1028_){
_start:
{
uint8_t v___x_1029_; 
v___x_1029_ = l_Lean_Name_hasMacroScopes(v_n_1027_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Name_appendAfter___lam__0(v_suffix_1028_, v_n_1027_);
return v___x_1030_;
}
else
{
lean_object* v_view_1031_; lean_object* v_name_1032_; lean_object* v_imported_1033_; lean_object* v_ctx_1034_; lean_object* v_scopes_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1044_; 
v_view_1031_ = l_Lean_extractMacroScopes(v_n_1027_);
v_name_1032_ = lean_ctor_get(v_view_1031_, 0);
v_imported_1033_ = lean_ctor_get(v_view_1031_, 1);
v_ctx_1034_ = lean_ctor_get(v_view_1031_, 2);
v_scopes_1035_ = lean_ctor_get(v_view_1031_, 3);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_view_1031_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1037_ = v_view_1031_;
v_isShared_1038_ = v_isSharedCheck_1044_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_scopes_1035_);
lean_inc(v_ctx_1034_);
lean_inc(v_imported_1033_);
lean_inc(v_name_1032_);
lean_dec(v_view_1031_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1044_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = l_Lean_Name_appendAfter___lam__0(v_suffix_1028_, v_name_1032_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1039_);
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_imported_1033_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_ctx_1034_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_scopes_1035_);
v___x_1041_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_MacroScopesView_review(v___x_1041_);
return v___x_1042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object* v_idx_1045_, lean_object* v_x_1046_){
_start:
{
if (lean_obj_tag(v_x_1046_) == 1)
{
lean_object* v_pre_1047_; lean_object* v_str_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_pre_1047_ = lean_ctor_get(v_x_1046_, 0);
lean_inc(v_pre_1047_);
v_str_1048_ = lean_ctor_get(v_x_1046_, 1);
lean_inc_ref(v_str_1048_);
lean_dec_ref_known(v_x_1046_, 2);
v___x_1049_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1050_ = lean_string_append(v_str_1048_, v___x_1049_);
v___x_1051_ = l_Nat_reprFast(v_idx_1045_);
v___x_1052_ = lean_string_append(v___x_1050_, v___x_1051_);
lean_dec_ref(v___x_1051_);
v___x_1053_ = l_Lean_Name_str___override(v_pre_1047_, v___x_1052_);
return v___x_1053_;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1054_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1055_ = l_Nat_reprFast(v_idx_1045_);
v___x_1056_ = lean_string_append(v___x_1054_, v___x_1055_);
lean_dec_ref(v___x_1055_);
v___x_1057_ = l_Lean_Name_str___override(v_x_1046_, v___x_1056_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object* v_n_1058_, lean_object* v_idx_1059_){
_start:
{
uint8_t v___x_1060_; 
v___x_1060_ = l_Lean_Name_hasMacroScopes(v_n_1058_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1059_, v_n_1058_);
return v___x_1061_;
}
else
{
lean_object* v_view_1062_; lean_object* v_name_1063_; lean_object* v_imported_1064_; lean_object* v_ctx_1065_; lean_object* v_scopes_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1075_; 
v_view_1062_ = l_Lean_extractMacroScopes(v_n_1058_);
v_name_1063_ = lean_ctor_get(v_view_1062_, 0);
v_imported_1064_ = lean_ctor_get(v_view_1062_, 1);
v_ctx_1065_ = lean_ctor_get(v_view_1062_, 2);
v_scopes_1066_ = lean_ctor_get(v_view_1062_, 3);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_view_1062_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1068_ = v_view_1062_;
v_isShared_1069_ = v_isSharedCheck_1075_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_scopes_1066_);
lean_inc(v_ctx_1065_);
lean_inc(v_imported_1064_);
lean_inc(v_name_1063_);
lean_dec(v_view_1062_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1075_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1070_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1059_, v_name_1063_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1070_);
v___x_1072_ = v___x_1068_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_imported_1064_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_ctx_1065_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v_scopes_1066_);
v___x_1072_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_MacroScopesView_review(v___x_1072_);
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object* v_pre_1076_, lean_object* v_x_1077_){
_start:
{
switch(lean_obj_tag(v_x_1077_))
{
case 0:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Name_str___override(v_x_1077_, v_pre_1076_);
return v___x_1078_;
}
case 1:
{
lean_object* v_pre_1079_; lean_object* v_str_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_pre_1079_ = lean_ctor_get(v_x_1077_, 0);
lean_inc(v_pre_1079_);
v_str_1080_ = lean_ctor_get(v_x_1077_, 1);
lean_inc_ref(v_str_1080_);
lean_dec_ref_known(v_x_1077_, 2);
v___x_1081_ = lean_string_append(v_pre_1076_, v_str_1080_);
lean_dec_ref(v_str_1080_);
v___x_1082_ = l_Lean_Name_str___override(v_pre_1079_, v___x_1081_);
return v___x_1082_;
}
default: 
{
lean_object* v_pre_1083_; lean_object* v_i_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_pre_1083_ = lean_ctor_get(v_x_1077_, 0);
lean_inc(v_pre_1083_);
v_i_1084_ = lean_ctor_get(v_x_1077_, 1);
lean_inc(v_i_1084_);
lean_dec_ref_known(v_x_1077_, 2);
v___x_1085_ = l_Lean_Name_str___override(v_pre_1083_, v_pre_1076_);
v___x_1086_ = l_Lean_Name_num___override(v___x_1085_, v_i_1084_);
return v___x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore(lean_object* v_n_1087_, lean_object* v_pre_1088_){
_start:
{
uint8_t v___x_1089_; 
v___x_1089_ = l_Lean_Name_hasMacroScopes(v_n_1087_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Name_appendBefore___lam__0(v_pre_1088_, v_n_1087_);
return v___x_1090_;
}
else
{
lean_object* v_view_1091_; lean_object* v_name_1092_; lean_object* v_imported_1093_; lean_object* v_ctx_1094_; lean_object* v_scopes_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1104_; 
v_view_1091_ = l_Lean_extractMacroScopes(v_n_1087_);
v_name_1092_ = lean_ctor_get(v_view_1091_, 0);
v_imported_1093_ = lean_ctor_get(v_view_1091_, 1);
v_ctx_1094_ = lean_ctor_get(v_view_1091_, 2);
v_scopes_1095_ = lean_ctor_get(v_view_1091_, 3);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_view_1091_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1097_ = v_view_1091_;
v_isShared_1098_ = v_isSharedCheck_1104_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_scopes_1095_);
lean_inc(v_ctx_1094_);
lean_inc(v_imported_1093_);
lean_inc(v_name_1092_);
lean_dec(v_view_1091_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1104_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1099_ = l_Lean_Name_appendBefore___lam__0(v_pre_1088_, v_name_1092_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1099_);
v___x_1101_ = v___x_1097_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_imported_1093_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v_ctx_1094_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v_scopes_1095_);
v___x_1101_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_MacroScopesView_review(v___x_1101_);
return v___x_1102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_h__1_1107_, lean_object* v_h__2_1108_, lean_object* v_h__3_1109_, lean_object* v_h__4_1110_){
_start:
{
switch(lean_obj_tag(v_x_1105_))
{
case 0:
{
lean_dec(v_h__3_1109_);
lean_dec(v_h__2_1108_);
if (lean_obj_tag(v_x_1106_) == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec(v_h__4_1110_);
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_apply_1(v_h__1_1107_, v___x_1111_);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; 
lean_dec(v_h__1_1107_);
v___x_1113_ = lean_apply_5(v_h__4_1110_, v_x_1105_, v_x_1106_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1113_;
}
}
case 1:
{
lean_dec(v_h__3_1109_);
lean_dec(v_h__1_1107_);
if (lean_obj_tag(v_x_1106_) == 1)
{
lean_object* v_pre_1114_; lean_object* v_str_1115_; lean_object* v_pre_1116_; lean_object* v_str_1117_; lean_object* v___x_1118_; 
lean_dec(v_h__4_1110_);
v_pre_1114_ = lean_ctor_get(v_x_1105_, 0);
lean_inc(v_pre_1114_);
v_str_1115_ = lean_ctor_get(v_x_1105_, 1);
lean_inc_ref(v_str_1115_);
lean_dec_ref_known(v_x_1105_, 2);
v_pre_1116_ = lean_ctor_get(v_x_1106_, 0);
lean_inc(v_pre_1116_);
v_str_1117_ = lean_ctor_get(v_x_1106_, 1);
lean_inc_ref(v_str_1117_);
lean_dec_ref_known(v_x_1106_, 2);
v___x_1118_ = lean_apply_4(v_h__2_1108_, v_pre_1114_, v_str_1115_, v_pre_1116_, v_str_1117_);
return v___x_1118_;
}
else
{
lean_object* v___x_1119_; 
lean_dec(v_h__2_1108_);
v___x_1119_ = lean_apply_5(v_h__4_1110_, v_x_1105_, v_x_1106_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1119_;
}
}
default: 
{
lean_dec(v_h__2_1108_);
lean_dec(v_h__1_1107_);
if (lean_obj_tag(v_x_1106_) == 2)
{
lean_object* v_pre_1120_; lean_object* v_i_1121_; lean_object* v_pre_1122_; lean_object* v_i_1123_; lean_object* v___x_1124_; 
lean_dec(v_h__4_1110_);
v_pre_1120_ = lean_ctor_get(v_x_1105_, 0);
lean_inc(v_pre_1120_);
v_i_1121_ = lean_ctor_get(v_x_1105_, 1);
lean_inc(v_i_1121_);
lean_dec_ref_known(v_x_1105_, 2);
v_pre_1122_ = lean_ctor_get(v_x_1106_, 0);
lean_inc(v_pre_1122_);
v_i_1123_ = lean_ctor_get(v_x_1106_, 1);
lean_inc(v_i_1123_);
lean_dec_ref_known(v_x_1106_, 2);
v___x_1124_ = lean_apply_4(v_h__3_1109_, v_pre_1120_, v_i_1121_, v_pre_1122_, v_i_1123_);
return v___x_1124_;
}
else
{
lean_object* v___x_1125_; 
lean_dec(v_h__3_1109_);
v___x_1125_ = lean_apply_5(v_h__4_1110_, v_x_1105_, v_x_1106_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object* v_motive_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_, lean_object* v_h__1_1129_, lean_object* v_h__2_1130_, lean_object* v_h__3_1131_, lean_object* v_h__4_1132_){
_start:
{
switch(lean_obj_tag(v_x_1127_))
{
case 0:
{
lean_dec(v_h__3_1131_);
lean_dec(v_h__2_1130_);
if (lean_obj_tag(v_x_1128_) == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v_h__4_1132_);
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_apply_1(v_h__1_1129_, v___x_1133_);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; 
lean_dec(v_h__1_1129_);
v___x_1135_ = lean_apply_5(v_h__4_1132_, v_x_1127_, v_x_1128_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1135_;
}
}
case 1:
{
lean_dec(v_h__3_1131_);
lean_dec(v_h__1_1129_);
if (lean_obj_tag(v_x_1128_) == 1)
{
lean_object* v_pre_1136_; lean_object* v_str_1137_; lean_object* v_pre_1138_; lean_object* v_str_1139_; lean_object* v___x_1140_; 
lean_dec(v_h__4_1132_);
v_pre_1136_ = lean_ctor_get(v_x_1127_, 0);
lean_inc(v_pre_1136_);
v_str_1137_ = lean_ctor_get(v_x_1127_, 1);
lean_inc_ref(v_str_1137_);
lean_dec_ref_known(v_x_1127_, 2);
v_pre_1138_ = lean_ctor_get(v_x_1128_, 0);
lean_inc(v_pre_1138_);
v_str_1139_ = lean_ctor_get(v_x_1128_, 1);
lean_inc_ref(v_str_1139_);
lean_dec_ref_known(v_x_1128_, 2);
v___x_1140_ = lean_apply_4(v_h__2_1130_, v_pre_1136_, v_str_1137_, v_pre_1138_, v_str_1139_);
return v___x_1140_;
}
else
{
lean_object* v___x_1141_; 
lean_dec(v_h__2_1130_);
v___x_1141_ = lean_apply_5(v_h__4_1132_, v_x_1127_, v_x_1128_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1141_;
}
}
default: 
{
lean_dec(v_h__2_1130_);
lean_dec(v_h__1_1129_);
if (lean_obj_tag(v_x_1128_) == 2)
{
lean_object* v_pre_1142_; lean_object* v_i_1143_; lean_object* v_pre_1144_; lean_object* v_i_1145_; lean_object* v___x_1146_; 
lean_dec(v_h__4_1132_);
v_pre_1142_ = lean_ctor_get(v_x_1127_, 0);
lean_inc(v_pre_1142_);
v_i_1143_ = lean_ctor_get(v_x_1127_, 1);
lean_inc(v_i_1143_);
lean_dec_ref_known(v_x_1127_, 2);
v_pre_1144_ = lean_ctor_get(v_x_1128_, 0);
lean_inc(v_pre_1144_);
v_i_1145_ = lean_ctor_get(v_x_1128_, 1);
lean_inc(v_i_1145_);
lean_dec_ref_known(v_x_1128_, 2);
v___x_1146_ = lean_apply_4(v_h__3_1131_, v_pre_1142_, v_i_1143_, v_pre_1144_, v_i_1145_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; 
lean_dec(v_h__3_1131_);
v___x_1147_ = lean_apply_5(v_h__4_1132_, v_x_1127_, v_x_1128_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1147_;
}
}
}
}
}
uint8_t l_Lean_Name_instDecidableEq(lean_object* v_a_1148_, lean_object* v_b_1149_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = lean_name_eq(v_a_1148_, v_b_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT void l_Lean_Name_instDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1148_ = stack[0].m_obj;
lean_object* v_b_1149_ = stack[1].m_obj;
uint8_t v_res_1151_;
v_res_1151_ = l_Lean_Name_instDecidableEq(v_a_1148_, v_b_1149_);
stack->m_num = v_res_1151_;
}
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object* v_a_1152_, lean_object* v_b_1153_){
_start:
{
uint8_t v_res_1154_; lean_object* v_r_1155_; 
v_res_1154_ = l_Lean_Name_instDecidableEq(v_a_1152_, v_b_1153_);
lean_dec(v_b_1153_);
lean_dec(v_a_1152_);
v_r_1155_ = lean_box(v_res_1154_);
return v_r_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object* v_g_1156_){
_start:
{
lean_object* v_namePrefix_1157_; lean_object* v_idx_1158_; lean_object* v___x_1159_; 
v_namePrefix_1157_ = lean_ctor_get(v_g_1156_, 0);
lean_inc(v_namePrefix_1157_);
v_idx_1158_ = lean_ctor_get(v_g_1156_, 1);
lean_inc(v_idx_1158_);
lean_dec_ref(v_g_1156_);
v___x_1159_ = l_Lean_Name_num___override(v_namePrefix_1157_, v_idx_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object* v_g_1160_){
_start:
{
lean_object* v_namePrefix_1161_; lean_object* v_idx_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1171_; 
v_namePrefix_1161_ = lean_ctor_get(v_g_1160_, 0);
v_idx_1162_ = lean_ctor_get(v_g_1160_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_g_1160_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1164_ = v_g_1160_;
v_isShared_1165_ = v_isSharedCheck_1171_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_idx_1162_);
lean_inc(v_namePrefix_1161_);
lean_dec(v_g_1160_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1171_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1166_ = lean_unsigned_to_nat(1u);
v___x_1167_ = lean_nat_add(v_idx_1162_, v___x_1166_);
lean_dec(v_idx_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1167_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_namePrefix_1161_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object* v_g_1172_){
_start:
{
lean_object* v_namePrefix_1173_; lean_object* v_idx_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1186_; 
v_namePrefix_1173_ = lean_ctor_get(v_g_1172_, 0);
v_idx_1174_ = lean_ctor_get(v_g_1172_, 1);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_g_1172_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1176_ = v_g_1172_;
v_isShared_1177_ = v_isSharedCheck_1186_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_idx_1174_);
lean_inc(v_namePrefix_1173_);
lean_dec(v_g_1172_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1186_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
lean_inc(v_idx_1174_);
lean_inc(v_namePrefix_1173_);
v___x_1178_ = l_Lean_Name_num___override(v_namePrefix_1173_, v_idx_1174_);
v___x_1179_ = lean_unsigned_to_nat(1u);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v___x_1179_);
lean_ctor_set(v___x_1176_, 0, v___x_1178_);
v___x_1181_ = v___x_1176_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_nat_add(v_idx_1174_, v___x_1179_);
lean_dec(v_idx_1174_);
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v_namePrefix_1173_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1181_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
return v___x_1184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object* v_toPure_1187_, lean_object* v_r_1188_, lean_object* v_____r_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_apply_2(v_toPure_1187_, lean_box(0), v_r_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object* v_toPure_1191_, lean_object* v_setNGen_1192_, lean_object* v_toBind_1193_, lean_object* v_ngen_1194_){
_start:
{
lean_object* v_namePrefix_1195_; lean_object* v_idx_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1209_; 
v_namePrefix_1195_ = lean_ctor_get(v_ngen_1194_, 0);
v_idx_1196_ = lean_ctor_get(v_ngen_1194_, 1);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_ngen_1194_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1198_ = v_ngen_1194_;
v_isShared_1199_ = v_isSharedCheck_1209_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_idx_1196_);
lean_inc(v_namePrefix_1195_);
lean_dec(v_ngen_1194_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1209_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v_r_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
lean_inc(v_idx_1196_);
lean_inc(v_namePrefix_1195_);
v_r_1200_ = l_Lean_Name_num___override(v_namePrefix_1195_, v_idx_1196_);
v___f_1201_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1201_, 0, v_toPure_1191_);
lean_closure_set(v___f_1201_, 1, v_r_1200_);
v___x_1202_ = lean_unsigned_to_nat(1u);
v___x_1203_ = lean_nat_add(v_idx_1196_, v___x_1202_);
lean_dec(v_idx_1196_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 1, v___x_1203_);
v___x_1205_ = v___x_1198_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_namePrefix_1195_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_apply_1(v_setNGen_1192_, v___x_1205_);
v___x_1207_ = lean_apply_4(v_toBind_1193_, lean_box(0), lean_box(0), v___x_1206_, v___f_1201_);
return v___x_1207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object* v_inst_1210_, lean_object* v_inst_1211_){
_start:
{
lean_object* v_toApplicative_1212_; lean_object* v_toBind_1213_; lean_object* v_getNGen_1214_; lean_object* v_setNGen_1215_; lean_object* v_toPure_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; 
v_toApplicative_1212_ = lean_ctor_get(v_inst_1210_, 0);
lean_inc_ref(v_toApplicative_1212_);
v_toBind_1213_ = lean_ctor_get(v_inst_1210_, 1);
lean_inc_n(v_toBind_1213_, 2);
lean_dec_ref(v_inst_1210_);
v_getNGen_1214_ = lean_ctor_get(v_inst_1211_, 0);
lean_inc(v_getNGen_1214_);
v_setNGen_1215_ = lean_ctor_get(v_inst_1211_, 1);
lean_inc(v_setNGen_1215_);
lean_dec_ref(v_inst_1211_);
v_toPure_1216_ = lean_ctor_get(v_toApplicative_1212_, 1);
lean_inc(v_toPure_1216_);
lean_dec_ref(v_toApplicative_1212_);
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1217_, 0, v_toPure_1216_);
lean_closure_set(v___f_1217_, 1, v_setNGen_1215_);
lean_closure_set(v___f_1217_, 2, v_toBind_1213_);
v___x_1218_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v_getNGen_1214_, v___f_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object* v_m_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_mkFreshId___redArg(v_inst_1220_, v_inst_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object* v_setNGen_1223_, lean_object* v_inst_1224_, lean_object* v_ngen_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_apply_1(v_setNGen_1223_, v_ngen_1225_);
v___x_1227_ = lean_apply_2(v_inst_1224_, lean_box(0), v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object* v_inst_1228_, lean_object* v_inst_1229_){
_start:
{
lean_object* v_getNGen_1230_; lean_object* v_setNGen_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1240_; 
v_getNGen_1230_ = lean_ctor_get(v_inst_1229_, 0);
v_setNGen_1231_ = lean_ctor_get(v_inst_1229_, 1);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_inst_1229_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1233_ = v_inst_1229_;
v_isShared_1234_ = v_isSharedCheck_1240_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_setNGen_1231_);
lean_inc(v_getNGen_1230_);
lean_dec(v_inst_1229_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1240_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___f_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
lean_inc(v_inst_1228_);
v___f_1235_ = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1235_, 0, v_setNGen_1231_);
lean_closure_set(v___f_1235_, 1, v_inst_1228_);
v___x_1236_ = lean_apply_2(v_inst_1228_, lean_box(0), v_getNGen_1230_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v___f_1235_);
lean_ctor_set(v___x_1233_, 0, v___x_1236_);
v___x_1238_ = v___x_1233_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___f_1235_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object* v_m_1241_, lean_object* v_n_1242_, lean_object* v_inst_1243_, lean_object* v_inst_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_monadNameGeneratorLift___redArg(v_inst_1243_, v_inst_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
if (lean_obj_tag(v_x_1248_) == 0)
{
lean_dec(v_x_1246_);
return v_x_1247_;
}
else
{
lean_object* v_head_1249_; lean_object* v_tail_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1261_; 
v_head_1249_ = lean_ctor_get(v_x_1248_, 0);
v_tail_1250_ = lean_ctor_get(v_x_1248_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_x_1248_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1252_ = v_x_1248_;
v_isShared_1253_ = v_isSharedCheck_1261_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_tail_1250_);
lean_inc(v_head_1249_);
lean_dec(v_x_1248_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1261_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
lean_inc(v_x_1246_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set_tag(v___x_1252_, 5);
lean_ctor_set(v___x_1252_, 1, v_x_1246_);
lean_ctor_set(v___x_1252_, 0, v_x_1247_);
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_x_1247_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_x_1246_);
v___x_1255_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = l_String_quote(v_head_1249_);
v___x_1257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
v___x_1258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1255_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v_x_1247_ = v___x_1258_;
v_x_1248_ = v_tail_1250_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object* v_x_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_){
_start:
{
if (lean_obj_tag(v_x_1264_) == 0)
{
lean_dec(v_x_1262_);
return v_x_1263_;
}
else
{
lean_object* v_head_1265_; lean_object* v_tail_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1277_; 
v_head_1265_ = lean_ctor_get(v_x_1264_, 0);
v_tail_1266_ = lean_ctor_get(v_x_1264_, 1);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_x_1264_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1268_ = v_x_1264_;
v_isShared_1269_ = v_isSharedCheck_1277_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_tail_1266_);
lean_inc(v_head_1265_);
lean_dec(v_x_1264_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1277_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
lean_inc(v_x_1262_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 5);
lean_ctor_set(v___x_1268_, 1, v_x_1262_);
lean_ctor_set(v___x_1268_, 0, v_x_1263_);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_x_1263_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_x_1262_);
v___x_1271_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1272_ = l_String_quote(v_head_1265_);
v___x_1273_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
v___x_1274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1271_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(v_x_1262_, v___x_1274_, v_tail_1266_);
return v___x_1275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = l_String_quote(v___y_1278_);
v___x_1280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
if (lean_obj_tag(v_x_1281_) == 0)
{
lean_object* v___x_1283_; 
lean_dec(v_x_1282_);
v___x_1283_ = lean_box(0);
return v___x_1283_;
}
else
{
lean_object* v_tail_1284_; 
v_tail_1284_ = lean_ctor_get(v_x_1281_, 1);
if (lean_obj_tag(v_tail_1284_) == 0)
{
lean_object* v_head_1285_; lean_object* v___x_1286_; 
lean_dec(v_x_1282_);
v_head_1285_ = lean_ctor_get(v_x_1281_, 0);
lean_inc(v_head_1285_);
lean_dec_ref_known(v_x_1281_, 2);
v___x_1286_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1285_);
return v___x_1286_;
}
else
{
lean_object* v_head_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_inc(v_tail_1284_);
v_head_1287_ = lean_ctor_get(v_x_1281_, 0);
lean_inc(v_head_1287_);
lean_dec_ref_known(v_x_1281_, 2);
v___x_1288_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1287_);
v___x_1289_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(v_x_1282_, v___x_1288_, v_tail_1284_);
return v___x_1289_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2));
v___x_1302_ = lean_string_length(v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7);
v___x_1304_ = lean_nat_to_int(v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object* v_a_1309_){
_start:
{
if (lean_obj_tag(v_a_1309_) == 0)
{
lean_object* v___x_1310_; 
v___x_1310_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1311_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1312_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(v_a_1309_, v___x_1311_);
v___x_1313_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1314_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v___x_1312_);
v___x_1316_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1313_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___x_1319_ = l_Std_Format_fill(v___x_1318_);
return v___x_1319_;
}
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_unsigned_to_nat(2u);
v___x_1327_ = lean_nat_to_int(v___x_1326_);
return v___x_1327_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_nat_to_int(v___x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object* v_x_1336_, lean_object* v_prec_1337_){
_start:
{
if (lean_obj_tag(v_x_1336_) == 0)
{
lean_object* v_ns_1338_; lean_object* v___y_1340_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v_ns_1338_ = lean_ctor_get(v_x_1336_, 0);
lean_inc(v_ns_1338_);
lean_dec_ref_known(v_x_1336_, 1);
v___x_1349_ = lean_unsigned_to_nat(1024u);
v___x_1350_ = lean_nat_dec_le(v___x_1349_, v_prec_1337_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1340_ = v___x_1351_;
goto v___jp_1339_;
}
else
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1340_ = v___x_1352_;
goto v___jp_1339_;
}
v___jp_1339_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1341_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__2));
v___x_1342_ = lean_unsigned_to_nat(1024u);
v___x_1343_ = l_Lean_Name_reprPrec(v_ns_1338_, v___x_1342_);
v___x_1344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1341_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
lean_inc(v___y_1340_);
v___x_1345_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___y_1340_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = 0;
v___x_1347_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*1, v___x_1346_);
v___x_1348_ = l_Repr_addAppParen(v___x_1347_, v_prec_1337_);
return v___x_1348_;
}
}
else
{
lean_object* v_n_1353_; lean_object* v_fields_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1378_; 
v_n_1353_ = lean_ctor_get(v_x_1336_, 0);
v_fields_1354_ = lean_ctor_get(v_x_1336_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_x_1336_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1356_ = v_x_1336_;
v_isShared_1357_ = v_isSharedCheck_1378_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_fields_1354_);
lean_inc(v_n_1353_);
lean_dec(v_x_1336_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1378_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___y_1359_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = lean_unsigned_to_nat(1024u);
v___x_1375_ = lean_nat_dec_le(v___x_1374_, v_prec_1337_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1359_ = v___x_1376_;
goto v___jp_1358_;
}
else
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1359_ = v___x_1377_;
goto v___jp_1358_;
}
v___jp_1358_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1360_ = lean_box(1);
v___x_1361_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__7));
v___x_1362_ = lean_unsigned_to_nat(1024u);
v___x_1363_ = l_Lean_Name_reprPrec(v_n_1353_, v___x_1362_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 5);
lean_ctor_set(v___x_1356_, 1, v___x_1363_);
lean_ctor_set(v___x_1356_, 0, v___x_1361_);
v___x_1365_ = v___x_1356_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v___x_1360_);
v___x_1367_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_fields_1354_);
v___x_1368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
lean_inc(v___y_1359_);
v___x_1369_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___y_1359_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = 0;
v___x_1371_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set_uint8(v___x_1371_, sizeof(void*)*1, v___x_1370_);
v___x_1372_ = l_Repr_addAppParen(v___x_1371_, v_prec_1337_);
return v___x_1372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object* v_x_1379_, lean_object* v_prec_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Syntax_instReprPreresolved_repr(v_x_1379_, v_prec_1380_);
lean_dec(v_prec_1380_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object* v_a_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_nat_to_int(v_a_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object* v_a_1384_, lean_object* v_n_1385_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_a_1384_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object* v_a_1387_, lean_object* v_n_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(v_a_1387_, v_n_1388_);
lean_dec(v_n_1388_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object* v___y_1392_){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = l_Lean_Syntax_instReprPreresolved_repr(v___y_1392_, v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_1395_, lean_object* v_x_1396_, lean_object* v_x_1397_){
_start:
{
if (lean_obj_tag(v_x_1397_) == 0)
{
lean_dec(v_x_1395_);
return v_x_1396_;
}
else
{
lean_object* v_head_1398_; lean_object* v_tail_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1410_; 
v_head_1398_ = lean_ctor_get(v_x_1397_, 0);
v_tail_1399_ = lean_ctor_get(v_x_1397_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_x_1397_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1401_ = v_x_1397_;
v_isShared_1402_ = v_isSharedCheck_1410_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_tail_1399_);
lean_inc(v_head_1398_);
lean_dec(v_x_1397_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1410_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
lean_inc(v_x_1395_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 5);
lean_ctor_set(v___x_1401_, 1, v_x_1395_);
lean_ctor_set(v___x_1401_, 0, v_x_1396_);
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_x_1396_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_x_1395_);
v___x_1404_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1398_, v___x_1405_);
v___x_1407_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1404_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v_x_1396_ = v___x_1407_;
v_x_1397_ = v_tail_1399_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object* v_x_1411_, lean_object* v_x_1412_, lean_object* v_x_1413_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_dec(v_x_1411_);
return v_x_1412_;
}
else
{
lean_object* v_head_1414_; lean_object* v_tail_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1426_; 
v_head_1414_ = lean_ctor_get(v_x_1413_, 0);
v_tail_1415_ = lean_ctor_get(v_x_1413_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_x_1413_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1417_ = v_x_1413_;
v_isShared_1418_ = v_isSharedCheck_1426_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_tail_1415_);
lean_inc(v_head_1414_);
lean_dec(v_x_1413_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1426_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
lean_inc(v_x_1411_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set_tag(v___x_1417_, 5);
lean_ctor_set(v___x_1417_, 1, v_x_1411_);
lean_ctor_set(v___x_1417_, 0, v_x_1412_);
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_x_1412_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_x_1411_);
v___x_1420_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1421_ = lean_unsigned_to_nat(0u);
v___x_1422_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1414_, v___x_1421_);
v___x_1423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1420_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(v_x_1411_, v___x_1423_, v_tail_1415_);
return v___x_1424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object* v_x_1427_, lean_object* v_x_1428_){
_start:
{
if (lean_obj_tag(v_x_1427_) == 0)
{
lean_object* v___x_1429_; 
lean_dec(v_x_1428_);
v___x_1429_ = lean_box(0);
return v___x_1429_;
}
else
{
lean_object* v_tail_1430_; 
v_tail_1430_ = lean_ctor_get(v_x_1427_, 1);
if (lean_obj_tag(v_tail_1430_) == 0)
{
lean_object* v_head_1431_; lean_object* v___x_1432_; 
lean_dec(v_x_1428_);
v_head_1431_ = lean_ctor_get(v_x_1427_, 0);
lean_inc(v_head_1431_);
lean_dec_ref_known(v_x_1427_, 2);
v___x_1432_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1431_);
return v___x_1432_;
}
else
{
lean_object* v_head_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_inc(v_tail_1430_);
v_head_1433_ = lean_ctor_get(v_x_1427_, 0);
lean_inc(v_head_1433_);
lean_dec_ref_known(v_x_1427_, 2);
v___x_1434_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1433_);
v___x_1435_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(v_x_1428_, v___x_1434_, v_tail_1430_);
return v___x_1435_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object* v_a_1436_){
_start:
{
if (lean_obj_tag(v_a_1436_) == 0)
{
lean_object* v___x_1437_; 
v___x_1437_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1437_;
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; lean_object* v___x_1447_; 
v___x_1438_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1439_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(v_a_1436_, v___x_1438_);
v___x_1440_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1441_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
lean_ctor_set(v___x_1442_, 1, v___x_1439_);
v___x_1443_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1440_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = 0;
v___x_1447_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set_uint8(v___x_1447_, sizeof(void*)*1, v___x_1446_);
return v___x_1447_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1457_, lean_object* v_x_1458_, lean_object* v_x_1459_){
_start:
{
if (lean_obj_tag(v_x_1459_) == 0)
{
lean_dec(v_x_1457_);
return v_x_1458_;
}
else
{
lean_object* v_head_1460_; lean_object* v_tail_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1472_; 
v_head_1460_ = lean_ctor_get(v_x_1459_, 0);
v_tail_1461_ = lean_ctor_get(v_x_1459_, 1);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_x_1459_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1463_ = v_x_1459_;
v_isShared_1464_ = v_isSharedCheck_1472_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_tail_1461_);
lean_inc(v_head_1460_);
lean_dec(v_x_1459_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1472_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
lean_inc(v_x_1457_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set_tag(v___x_1463_, 5);
lean_ctor_set(v___x_1463_, 1, v_x_1457_);
lean_ctor_set(v___x_1463_, 0, v_x_1458_);
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_x_1458_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_x_1457_);
v___x_1466_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = l_Lean_Syntax_instRepr_repr(v_head_1460_, v___x_1467_);
v___x_1469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1466_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v_x_1458_ = v___x_1469_;
v_x_1459_ = v_tail_1461_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object* v_x_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_){
_start:
{
if (lean_obj_tag(v_x_1475_) == 0)
{
lean_dec(v_x_1473_);
return v_x_1474_;
}
else
{
lean_object* v_head_1476_; lean_object* v_tail_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1488_; 
v_head_1476_ = lean_ctor_get(v_x_1475_, 0);
v_tail_1477_ = lean_ctor_get(v_x_1475_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_x_1475_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1479_ = v_x_1475_;
v_isShared_1480_ = v_isSharedCheck_1488_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_tail_1477_);
lean_inc(v_head_1476_);
lean_dec(v_x_1475_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1488_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
lean_inc(v_x_1473_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set_tag(v___x_1479_, 5);
lean_ctor_set(v___x_1479_, 1, v_x_1473_);
lean_ctor_set(v___x_1479_, 0, v_x_1474_);
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_x_1474_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_x_1473_);
v___x_1482_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = l_Lean_Syntax_instRepr_repr(v_head_1476_, v___x_1483_);
v___x_1485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1482_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(v_x_1473_, v___x_1485_, v_tail_1477_);
return v___x_1486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object* v_x_1489_, lean_object* v_x_1490_){
_start:
{
if (lean_obj_tag(v_x_1489_) == 0)
{
lean_object* v___x_1491_; 
lean_dec(v_x_1490_);
v___x_1491_ = lean_box(0);
return v___x_1491_;
}
else
{
lean_object* v_tail_1492_; 
v_tail_1492_ = lean_ctor_get(v_x_1489_, 1);
if (lean_obj_tag(v_tail_1492_) == 0)
{
lean_object* v_head_1493_; lean_object* v___x_1494_; 
lean_dec(v_x_1490_);
v_head_1493_ = lean_ctor_get(v_x_1489_, 0);
lean_inc(v_head_1493_);
lean_dec_ref_known(v_x_1489_, 2);
v___x_1494_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1493_);
return v___x_1494_;
}
else
{
lean_object* v_head_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_inc(v_tail_1492_);
v_head_1495_ = lean_ctor_get(v_x_1489_, 0);
lean_inc(v_head_1495_);
lean_dec_ref_known(v_x_1489_, 2);
v___x_1496_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1495_);
v___x_1497_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(v_x_1490_, v___x_1496_, v_tail_1492_);
return v___x_1497_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0));
v___x_1500_ = lean_string_length(v___x_1499_);
return v___x_1500_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1);
v___x_1502_ = lean_nat_to_int(v___x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object* v_xs_1508_){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1509_ = lean_array_get_size(v_xs_1508_);
v___x_1510_ = lean_unsigned_to_nat(0u);
v___x_1511_ = lean_nat_dec_eq(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1512_ = lean_array_to_list(v_xs_1508_);
v___x_1513_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1514_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(v___x_1512_, v___x_1513_);
v___x_1515_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2);
v___x_1516_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3));
v___x_1517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v___x_1514_);
v___x_1518_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1515_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = l_Std_Format_fill(v___x_1520_);
return v___x_1521_;
}
else
{
lean_object* v___x_1522_; 
lean_dec_ref(v_xs_1508_);
v___x_1522_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5));
return v___x_1522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object* v_x_1536_, lean_object* v_prec_1537_){
_start:
{
lean_object* v___y_1539_; 
switch(lean_obj_tag(v_x_1536_))
{
case 0:
{
lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1545_ = lean_unsigned_to_nat(1024u);
v___x_1546_ = lean_nat_dec_le(v___x_1545_, v_prec_1537_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1539_ = v___x_1547_;
goto v___jp_1538_;
}
else
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1539_ = v___x_1548_;
goto v___jp_1538_;
}
}
case 1:
{
lean_object* v_info_1549_; lean_object* v_kind_1550_; lean_object* v_args_1551_; lean_object* v___y_1553_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v_info_1549_ = lean_ctor_get(v_x_1536_, 0);
lean_inc(v_info_1549_);
v_kind_1550_ = lean_ctor_get(v_x_1536_, 1);
lean_inc(v_kind_1550_);
v_args_1551_ = lean_ctor_get(v_x_1536_, 2);
lean_inc_ref(v_args_1551_);
lean_dec_ref_known(v_x_1536_, 3);
v___x_1569_ = lean_unsigned_to_nat(1024u);
v___x_1570_ = lean_nat_dec_le(v___x_1569_, v_prec_1537_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1553_ = v___x_1571_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1553_ = v___x_1572_;
goto v___jp_1552_;
}
v___jp_1552_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1554_ = lean_box(1);
v___x_1555_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__4));
v___x_1556_ = lean_unsigned_to_nat(1024u);
v___x_1557_ = l_instReprSourceInfo_repr(v_info_1549_, v___x_1556_);
v___x_1558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1555_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v___x_1554_);
v___x_1560_ = l_Lean_Name_reprPrec(v_kind_1550_, v___x_1556_);
v___x_1561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v___x_1554_);
v___x_1563_ = l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(v_args_1551_);
v___x_1564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
lean_inc(v___y_1553_);
v___x_1565_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___y_1553_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = 0;
v___x_1567_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set_uint8(v___x_1567_, sizeof(void*)*1, v___x_1566_);
v___x_1568_ = l_Repr_addAppParen(v___x_1567_, v_prec_1537_);
return v___x_1568_;
}
}
case 2:
{
lean_object* v_info_1573_; lean_object* v_val_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1599_; 
v_info_1573_ = lean_ctor_get(v_x_1536_, 0);
v_val_1574_ = lean_ctor_get(v_x_1536_, 1);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_x_1536_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1576_ = v_x_1536_;
v_isShared_1577_ = v_isSharedCheck_1599_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_val_1574_);
lean_inc(v_info_1573_);
lean_dec(v_x_1536_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1599_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___y_1579_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = lean_unsigned_to_nat(1024u);
v___x_1596_ = lean_nat_dec_le(v___x_1595_, v_prec_1537_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1579_ = v___x_1597_;
goto v___jp_1578_;
}
else
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1579_ = v___x_1598_;
goto v___jp_1578_;
}
v___jp_1578_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1580_ = lean_box(1);
v___x_1581_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__7));
v___x_1582_ = lean_unsigned_to_nat(1024u);
v___x_1583_ = l_instReprSourceInfo_repr(v_info_1573_, v___x_1582_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set_tag(v___x_1576_, 5);
lean_ctor_set(v___x_1576_, 1, v___x_1583_);
lean_ctor_set(v___x_1576_, 0, v___x_1581_);
v___x_1585_ = v___x_1576_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
lean_ctor_set(v___x_1586_, 1, v___x_1580_);
v___x_1587_ = l_String_quote(v_val_1574_);
v___x_1588_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
v___x_1589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1586_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
lean_inc(v___y_1579_);
v___x_1590_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___y_1579_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = 0;
v___x_1592_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set_uint8(v___x_1592_, sizeof(void*)*1, v___x_1591_);
v___x_1593_ = l_Repr_addAppParen(v___x_1592_, v_prec_1537_);
return v___x_1593_;
}
}
}
}
default: 
{
lean_object* v_info_1600_; lean_object* v_rawVal_1601_; lean_object* v_val_1602_; lean_object* v_preresolved_1603_; lean_object* v___y_1605_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v_info_1600_ = lean_ctor_get(v_x_1536_, 0);
lean_inc(v_info_1600_);
v_rawVal_1601_ = lean_ctor_get(v_x_1536_, 1);
lean_inc_ref(v_rawVal_1601_);
v_val_1602_ = lean_ctor_get(v_x_1536_, 2);
lean_inc(v_val_1602_);
v_preresolved_1603_ = lean_ctor_get(v_x_1536_, 3);
lean_inc(v_preresolved_1603_);
lean_dec_ref_known(v_x_1536_, 4);
v___x_1628_ = lean_unsigned_to_nat(1024u);
v___x_1629_ = lean_nat_dec_le(v___x_1628_, v_prec_1537_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1605_ = v___x_1630_;
goto v___jp_1604_;
}
else
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1605_ = v___x_1631_;
goto v___jp_1604_;
}
v___jp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1606_ = lean_box(1);
v___x_1607_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__10));
v___x_1608_ = lean_unsigned_to_nat(1024u);
v___x_1609_ = l_instReprSourceInfo_repr(v_info_1600_, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1607_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_ctor_set(v___x_1611_, 1, v___x_1606_);
v___x_1612_ = lean_substring_tostring(v_rawVal_1601_);
v___x_1613_ = l_String_quote(v___x_1612_);
v___x_1614_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__11));
v___x_1615_ = lean_string_append(v___x_1613_, v___x_1614_);
v___x_1616_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1611_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
lean_ctor_set(v___x_1618_, 1, v___x_1606_);
v___x_1619_ = l_Lean_Name_reprPrec(v_val_1602_, v___x_1608_);
v___x_1620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
lean_ctor_set(v___x_1621_, 1, v___x_1606_);
v___x_1622_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_preresolved_1603_);
v___x_1623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
lean_inc(v___y_1605_);
v___x_1624_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___y_1605_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = 0;
v___x_1626_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1626_, 0, v___x_1624_);
lean_ctor_set_uint8(v___x_1626_, sizeof(void*)*1, v___x_1625_);
v___x_1627_ = l_Repr_addAppParen(v___x_1626_, v_prec_1537_);
return v___x_1627_;
}
}
}
v___jp_1538_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1540_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__1));
lean_inc(v___y_1539_);
v___x_1541_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___y_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = 0;
v___x_1543_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set_uint8(v___x_1543_, sizeof(void*)*1, v___x_1542_);
v___x_1544_ = l_Repr_addAppParen(v___x_1543_, v_prec_1537_);
return v___x_1544_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object* v___y_1632_){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = lean_unsigned_to_nat(0u);
v___x_1634_ = l_Lean_Syntax_instRepr_repr(v___y_1632_, v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object* v_x_1635_, lean_object* v_prec_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_Syntax_instRepr_repr(v_x_1635_, v_prec_1636_);
lean_dec(v_prec_1636_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object* v_a_1638_, lean_object* v_n_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_a_1638_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object* v_a_1641_, lean_object* v_n_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(v_a_1641_, v_n_1642_);
lean_dec(v_n_1642_);
return v_res_1643_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = lean_unsigned_to_nat(7u);
v___x_1660_ = lean_nat_to_int(v___x_1659_);
return v___x_1660_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0));
v___x_1663_ = lean_string_length(v___x_1662_);
return v___x_1663_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9);
v___x_1665_ = lean_nat_to_int(v___x_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object* v_x_1670_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1671_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6));
v___x_1672_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_1673_ = lean_unsigned_to_nat(0u);
v___x_1674_ = l_Lean_Syntax_instRepr_repr(v_x_1670_, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1672_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = 0;
v___x_1677_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set_uint8(v___x_1677_, sizeof(void*)*1, v___x_1676_);
v___x_1678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1671_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_1680_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_1681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v___x_1678_);
v___x_1682_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_1683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1679_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
lean_ctor_set_uint8(v___x_1685_, sizeof(void*)*1, v___x_1676_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object* v_ks_1686_, lean_object* v_x_1687_, lean_object* v_prec_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_x_1687_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object* v_ks_1690_, lean_object* v_x_1691_, lean_object* v_prec_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_Syntax_instReprTSyntax_repr(v_ks_1690_, v_x_1691_, v_prec_1692_);
lean_dec(v_prec_1692_);
lean_dec(v_ks_1690_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object* v_ks_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_alloc_closure((void*)(l_Lean_Syntax_instReprTSyntax_repr___boxed), 3, 1);
lean_closure_set(v___x_1695_, 0, v_ks_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_stx_1696_){
_start:
{
lean_inc(v_stx_1696_);
return v_stx_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0___boxed(lean_object* v_stx_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(v_stx_1697_);
lean_dec(v_stx_1697_);
return v_res_1698_;
}
}
lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg(){
_start:
{
lean_object* v___f_1701_; 
v___f_1701_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1701_;
}
}
LEAN_EXPORT void l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1702_;
v_res_1702_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg();
stack->m_obj
 = v_res_1702_;
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___boxed(lean_object* v___dummy_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg();
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object* v_k_1705_, lean_object* v_ks_1706_){
_start:
{
lean_object* v___f_1707_; 
v___f_1707_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object* v_k_1708_, lean_object* v_ks_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(v_k_1708_, v_ks_1709_);
lean_dec(v_ks_1709_);
lean_dec(v_k_1708_);
return v_res_1710_;
}
}
lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg(){
_start:
{
lean_object* v___f_1712_; 
v___f_1712_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1712_;
}
}
LEAN_EXPORT void l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1713_;
v_res_1713_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg();
stack->m_obj
 = v_res_1713_;
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg___boxed(lean_object* v___dummy_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg();
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object* v_ks_1716_, lean_object* v_k_x27_1717_){
_start:
{
lean_object* v___f_1718_; 
v___f_1718_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object* v_ks_1719_, lean_object* v_k_x27_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind(v_ks_1719_, v_k_x27_1720_);
lean_dec(v_k_x27_1720_);
lean_dec(v_ks_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object* v_s_1722_){
_start:
{
lean_inc(v_s_1722_);
return v_s_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object* v_s_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_TSyntax_instCoeIdentTerm___lam__0(v_s_1723_);
lean_dec(v_s_1723_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object* v_info_1727_, lean_object* v_ss_1728_, lean_object* v_n_1729_, lean_object* v_res_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1731_, 0, v_info_1727_);
lean_ctor_set(v___x_1731_, 1, v_ss_1728_);
lean_ctor_set(v___x_1731_, 2, v_n_1729_);
lean_ctor_set(v___x_1731_, 3, v_res_1730_);
return v___x_1731_;
}
}
lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg(){
_start:
{
lean_object* v___f_1741_; 
v___f_1741_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1741_;
}
}
LEAN_EXPORT void l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1742_;
v_res_1742_ = l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg();
stack->m_obj
 = v_res_1742_;
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg___boxed(lean_object* v___dummy_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg();
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object* v_k_1745_){
_start:
{
lean_object* v___f_1746_; 
v___f_1746_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object* v_k_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_TSyntax_Compat_instCoeTailSyntax(v_k_1747_);
lean_dec(v_k_1747_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object* v_k_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_alloc_closure((void*)(l_Lean_TSyntaxArray_mkImpl___boxed), 2, 1);
lean_closure_set(v___x_1750_, 0, v_k_1749_);
return v___x_1750_;
}
}
uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
if (lean_obj_tag(v_x_1751_) == 0)
{
if (lean_obj_tag(v_x_1752_) == 0)
{
uint8_t v___x_1753_; 
v___x_1753_ = 1;
return v___x_1753_;
}
else
{
uint8_t v___x_1754_; 
v___x_1754_ = 0;
return v___x_1754_;
}
}
else
{
if (lean_obj_tag(v_x_1752_) == 0)
{
uint8_t v___x_1755_; 
v___x_1755_ = 0;
return v___x_1755_;
}
else
{
lean_object* v_head_1756_; lean_object* v_tail_1757_; lean_object* v_head_1758_; lean_object* v_tail_1759_; uint8_t v___x_1760_; 
v_head_1756_ = lean_ctor_get(v_x_1751_, 0);
v_tail_1757_ = lean_ctor_get(v_x_1751_, 1);
v_head_1758_ = lean_ctor_get(v_x_1752_, 0);
v_tail_1759_ = lean_ctor_get(v_x_1752_, 1);
v___x_1760_ = lean_string_dec_eq(v_head_1756_, v_head_1758_);
if (v___x_1760_ == 0)
{
return v___x_1760_;
}
else
{
v_x_1751_ = v_tail_1757_;
v_x_1752_ = v_tail_1759_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1751_ = stack[0].m_obj;
lean_object* v_x_1752_ = stack[1].m_obj;
uint8_t v_res_1762_;
v_res_1762_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_x_1751_, v_x_1752_);
stack->m_num = v_res_1762_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
uint8_t v_res_1765_; lean_object* v_r_1766_; 
v_res_1765_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_x_1763_, v_x_1764_);
lean_dec(v_x_1764_);
lean_dec(v_x_1763_);
v_r_1766_ = lean_box(v_res_1765_);
return v_r_1766_;
}
}
uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object* v_x_1767_, lean_object* v_x_1768_){
_start:
{
if (lean_obj_tag(v_x_1767_) == 0)
{
if (lean_obj_tag(v_x_1768_) == 0)
{
lean_object* v_ns_1769_; lean_object* v_ns_1770_; uint8_t v___x_1771_; 
v_ns_1769_ = lean_ctor_get(v_x_1767_, 0);
v_ns_1770_ = lean_ctor_get(v_x_1768_, 0);
v___x_1771_ = lean_name_eq(v_ns_1769_, v_ns_1770_);
return v___x_1771_;
}
else
{
uint8_t v___x_1772_; 
v___x_1772_ = 0;
return v___x_1772_;
}
}
else
{
if (lean_obj_tag(v_x_1768_) == 1)
{
lean_object* v_n_1773_; lean_object* v_fields_1774_; lean_object* v_n_1775_; lean_object* v_fields_1776_; uint8_t v___x_1777_; 
v_n_1773_ = lean_ctor_get(v_x_1767_, 0);
v_fields_1774_ = lean_ctor_get(v_x_1767_, 1);
v_n_1775_ = lean_ctor_get(v_x_1768_, 0);
v_fields_1776_ = lean_ctor_get(v_x_1768_, 1);
v___x_1777_ = lean_name_eq(v_n_1773_, v_n_1775_);
if (v___x_1777_ == 0)
{
return v___x_1777_;
}
else
{
uint8_t v___x_1778_; 
v___x_1778_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_fields_1774_, v_fields_1776_);
return v___x_1778_;
}
}
else
{
uint8_t v___x_1779_; 
v___x_1779_ = 0;
return v___x_1779_;
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_instBEqPreresolved_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1767_ = stack[0].m_obj;
lean_object* v_x_1768_ = stack[1].m_obj;
uint8_t v_res_1780_;
v_res_1780_ = l_Lean_Syntax_instBEqPreresolved_beq(v_x_1767_, v_x_1768_);
stack->m_num = v_res_1780_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object* v_x_1781_, lean_object* v_x_1782_){
_start:
{
uint8_t v_res_1783_; lean_object* v_r_1784_; 
v_res_1783_ = l_Lean_Syntax_instBEqPreresolved_beq(v_x_1781_, v_x_1782_);
lean_dec_ref(v_x_1782_);
lean_dec_ref(v_x_1781_);
v_r_1784_ = lean_box(v_res_1783_);
return v_r_1784_;
}
}
uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object* v_x_1787_, lean_object* v_x_1788_){
_start:
{
if (lean_obj_tag(v_x_1787_) == 0)
{
if (lean_obj_tag(v_x_1788_) == 0)
{
uint8_t v___x_1789_; 
v___x_1789_ = 1;
return v___x_1789_;
}
else
{
uint8_t v___x_1790_; 
v___x_1790_ = 0;
return v___x_1790_;
}
}
else
{
if (lean_obj_tag(v_x_1788_) == 0)
{
uint8_t v___x_1791_; 
v___x_1791_ = 0;
return v___x_1791_;
}
else
{
lean_object* v_head_1792_; lean_object* v_tail_1793_; lean_object* v_head_1794_; lean_object* v_tail_1795_; uint8_t v___x_1796_; 
v_head_1792_ = lean_ctor_get(v_x_1787_, 0);
v_tail_1793_ = lean_ctor_get(v_x_1787_, 1);
v_head_1794_ = lean_ctor_get(v_x_1788_, 0);
v_tail_1795_ = lean_ctor_get(v_x_1788_, 1);
v___x_1796_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_1792_, v_head_1794_);
if (v___x_1796_ == 0)
{
return v___x_1796_;
}
else
{
v_x_1787_ = v_tail_1793_;
v_x_1788_ = v_tail_1795_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_Syntax_structEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1787_ = stack[0].m_obj;
lean_object* v_x_1788_ = stack[1].m_obj;
uint8_t v_res_1798_;
v_res_1798_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_x_1787_, v_x_1788_);
stack->m_num = v_res_1798_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object* v_x_1799_, lean_object* v_x_1800_){
_start:
{
uint8_t v_res_1801_; lean_object* v_r_1802_; 
v_res_1801_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_x_1799_, v_x_1800_);
lean_dec(v_x_1800_);
lean_dec(v_x_1799_);
v_r_1802_ = lean_box(v_res_1801_);
return v_r_1802_;
}
}
uint8_t l_Lean_Syntax_structEq(lean_object* v_x_1803_, lean_object* v_x_1804_){
_start:
{
switch(lean_obj_tag(v_x_1803_))
{
case 0:
{
if (lean_obj_tag(v_x_1804_) == 0)
{
uint8_t v___x_1805_; 
v___x_1805_ = 1;
return v___x_1805_;
}
else
{
uint8_t v___x_1806_; 
v___x_1806_ = 0;
return v___x_1806_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1804_) == 1)
{
lean_object* v_kind_1807_; lean_object* v_args_1808_; lean_object* v_kind_1809_; lean_object* v_args_1810_; uint8_t v___x_1811_; 
v_kind_1807_ = lean_ctor_get(v_x_1803_, 1);
v_args_1808_ = lean_ctor_get(v_x_1803_, 2);
v_kind_1809_ = lean_ctor_get(v_x_1804_, 1);
v_args_1810_ = lean_ctor_get(v_x_1804_, 2);
v___x_1811_ = lean_name_eq(v_kind_1807_, v_kind_1809_);
if (v___x_1811_ == 0)
{
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1812_ = lean_array_get_size(v_args_1808_);
v___x_1813_ = lean_array_get_size(v_args_1810_);
v___x_1814_ = lean_nat_dec_eq(v___x_1812_, v___x_1813_);
if (v___x_1814_ == 0)
{
return v___x_1814_;
}
else
{
uint8_t v___x_1815_; 
v___x_1815_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_args_1808_, v_args_1810_, v___x_1812_);
return v___x_1815_;
}
}
}
else
{
uint8_t v___x_1816_; 
v___x_1816_ = 0;
return v___x_1816_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1804_) == 2)
{
lean_object* v_val_1817_; lean_object* v_val_1818_; uint8_t v___x_1819_; 
v_val_1817_ = lean_ctor_get(v_x_1803_, 1);
v_val_1818_ = lean_ctor_get(v_x_1804_, 1);
v___x_1819_ = lean_string_dec_eq(v_val_1817_, v_val_1818_);
return v___x_1819_;
}
else
{
uint8_t v___x_1820_; 
v___x_1820_ = 0;
return v___x_1820_;
}
}
default: 
{
if (lean_obj_tag(v_x_1804_) == 3)
{
lean_object* v_rawVal_1821_; lean_object* v_val_1822_; lean_object* v_preresolved_1823_; lean_object* v_rawVal_1824_; lean_object* v_val_1825_; lean_object* v_preresolved_1826_; uint8_t v___y_1828_; uint8_t v___x_1830_; 
v_rawVal_1821_ = lean_ctor_get(v_x_1803_, 1);
v_val_1822_ = lean_ctor_get(v_x_1803_, 2);
v_preresolved_1823_ = lean_ctor_get(v_x_1803_, 3);
v_rawVal_1824_ = lean_ctor_get(v_x_1804_, 1);
v_val_1825_ = lean_ctor_get(v_x_1804_, 2);
v_preresolved_1826_ = lean_ctor_get(v_x_1804_, 3);
lean_inc_ref(v_rawVal_1824_);
lean_inc_ref(v_rawVal_1821_);
v___x_1830_ = lean_substring_beq(v_rawVal_1821_, v_rawVal_1824_);
if (v___x_1830_ == 0)
{
v___y_1828_ = v___x_1830_;
goto v___jp_1827_;
}
else
{
uint8_t v___x_1831_; 
v___x_1831_ = lean_name_eq(v_val_1822_, v_val_1825_);
v___y_1828_ = v___x_1831_;
goto v___jp_1827_;
}
v___jp_1827_:
{
if (v___y_1828_ == 0)
{
return v___y_1828_;
}
else
{
uint8_t v___x_1829_; 
v___x_1829_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_preresolved_1823_, v_preresolved_1826_);
return v___x_1829_;
}
}
}
else
{
uint8_t v___x_1832_; 
v___x_1832_ = 0;
return v___x_1832_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_structEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1803_ = stack[0].m_obj;
lean_object* v_x_1804_ = stack[1].m_obj;
uint8_t v_res_1833_;
v_res_1833_ = l_Lean_Syntax_structEq(v_x_1803_, v_x_1804_);
stack->m_num = v_res_1833_;
}
uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object* v_xs_1834_, lean_object* v_ys_1835_, lean_object* v_x_1836_){
_start:
{
lean_object* v_zero_1837_; uint8_t v_isZero_1838_; 
v_zero_1837_ = lean_unsigned_to_nat(0u);
v_isZero_1838_ = lean_nat_dec_eq(v_x_1836_, v_zero_1837_);
if (v_isZero_1838_ == 1)
{
lean_dec(v_x_1836_);
return v_isZero_1838_;
}
else
{
lean_object* v_one_1839_; lean_object* v_n_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v_one_1839_ = lean_unsigned_to_nat(1u);
v_n_1840_ = lean_nat_sub(v_x_1836_, v_one_1839_);
lean_dec(v_x_1836_);
v___x_1841_ = lean_array_fget_borrowed(v_xs_1834_, v_n_1840_);
v___x_1842_ = lean_array_fget_borrowed(v_ys_1835_, v_n_1840_);
v___x_1843_ = l_Lean_Syntax_structEq(v___x_1841_, v___x_1842_);
if (v___x_1843_ == 0)
{
lean_dec(v_n_1840_);
return v___x_1843_;
}
else
{
v_x_1836_ = v_n_1840_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1834_ = stack[0].m_obj;
lean_object* v_ys_1835_ = stack[1].m_obj;
lean_object* v_x_1836_ = stack[2].m_obj;
uint8_t v_res_1845_;
v_res_1845_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1834_, v_ys_1835_, v_x_1836_);
stack->m_num = v_res_1845_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object* v_xs_1846_, lean_object* v_ys_1847_, lean_object* v_x_1848_){
_start:
{
uint8_t v_res_1849_; lean_object* v_r_1850_; 
v_res_1849_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1846_, v_ys_1847_, v_x_1848_);
lean_dec_ref(v_ys_1847_);
lean_dec_ref(v_xs_1846_);
v_r_1850_ = lean_box(v_res_1849_);
return v_r_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object* v_x_1851_, lean_object* v_x_1852_){
_start:
{
uint8_t v_res_1853_; lean_object* v_r_1854_; 
v_res_1853_ = l_Lean_Syntax_structEq(v_x_1851_, v_x_1852_);
lean_dec(v_x_1852_);
lean_dec(v_x_1851_);
v_r_1854_ = lean_box(v_res_1853_);
return v_r_1854_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object* v_xs_1855_, lean_object* v_ys_1856_, lean_object* v_hsz_1857_, lean_object* v_x_1858_, lean_object* v_x_1859_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1855_, v_ys_1856_, v_x_1858_);
return v___x_1860_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1855_ = stack[0].m_obj;
lean_object* v_ys_1856_ = stack[1].m_obj;
lean_object* v_x_1858_ = stack[3].m_obj;
uint8_t v_res_1861_;
v_res_1861_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(v_xs_1855_, v_ys_1856_, lean_box(0), v_x_1858_, lean_box(0));
stack->m_num = v_res_1861_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object* v_xs_1862_, lean_object* v_ys_1863_, lean_object* v_hsz_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_){
_start:
{
uint8_t v_res_1867_; lean_object* v_r_1868_; 
v_res_1867_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(v_xs_1862_, v_ys_1863_, v_hsz_1864_, v_x_1865_, v_x_1866_);
lean_dec_ref(v_ys_1863_);
lean_dec_ref(v_xs_1862_);
v_r_1868_ = lean_box(v_res_1867_);
return v_r_1868_;
}
}
lean_object* l_Lean_Syntax_instBEqTSyntax___redArg(){
_start:
{
lean_object* v___f_1873_; 
v___f_1873_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___redArg___closed__0));
return v___f_1873_;
}
}
LEAN_EXPORT void l_Lean_Syntax_instBEqTSyntax___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1874_;
v_res_1874_ = l_Lean_Syntax_instBEqTSyntax___redArg();
stack->m_obj
 = v_res_1874_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg___boxed(lean_object* v___dummy_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Syntax_instBEqTSyntax___redArg();
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object* v_k_1877_){
_start:
{
lean_object* v___f_1878_; 
v___f_1878_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___redArg___closed__0));
return v___f_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object* v_k_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_Syntax_instBEqTSyntax(v_k_1879_);
lean_dec(v_k_1879_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object* v_as_1881_, lean_object* v_i_1882_){
_start:
{
lean_object* v_zero_1883_; uint8_t v_isZero_1884_; 
v_zero_1883_ = lean_unsigned_to_nat(0u);
v_isZero_1884_ = lean_nat_dec_eq(v_i_1882_, v_zero_1883_);
if (v_isZero_1884_ == 1)
{
lean_object* v___x_1885_; 
lean_dec(v_i_1882_);
v___x_1885_ = lean_box(0);
return v___x_1885_;
}
else
{
lean_object* v_one_1886_; lean_object* v_n_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v_one_1886_ = lean_unsigned_to_nat(1u);
v_n_1887_ = lean_nat_sub(v_i_1882_, v_one_1886_);
lean_dec(v_i_1882_);
v___x_1888_ = lean_array_fget_borrowed(v_as_1881_, v_n_1887_);
v___x_1889_ = l_Lean_Syntax_getTailInfo_x3f(v___x_1888_);
if (lean_obj_tag(v___x_1889_) == 0)
{
v_i_1882_ = v_n_1887_;
goto _start;
}
else
{
lean_dec(v_n_1887_);
return v___x_1889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object* v_x_1891_){
_start:
{
switch(lean_obj_tag(v_x_1891_))
{
case 2:
{
lean_object* v_info_1892_; lean_object* v___x_1893_; 
v_info_1892_ = lean_ctor_get(v_x_1891_, 0);
lean_inc(v_info_1892_);
v___x_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1893_, 0, v_info_1892_);
return v___x_1893_;
}
case 3:
{
lean_object* v_info_1894_; lean_object* v___x_1895_; 
v_info_1894_ = lean_ctor_get(v_x_1891_, 0);
lean_inc(v_info_1894_);
v___x_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1895_, 0, v_info_1894_);
return v___x_1895_;
}
case 1:
{
lean_object* v_info_1896_; 
v_info_1896_ = lean_ctor_get(v_x_1891_, 0);
if (lean_obj_tag(v_info_1896_) == 2)
{
lean_object* v_args_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v_args_1897_ = lean_ctor_get(v_x_1891_, 2);
v___x_1898_ = lean_array_get_size(v_args_1897_);
v___x_1899_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_args_1897_, v___x_1898_);
return v___x_1899_;
}
else
{
lean_object* v___x_1900_; 
lean_inc(v_info_1896_);
v___x_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1900_, 0, v_info_1896_);
return v___x_1900_;
}
}
default: 
{
lean_object* v___x_1901_; 
v___x_1901_ = lean_box(0);
return v___x_1901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object* v_x_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_Syntax_getTailInfo_x3f(v_x_1902_);
lean_dec(v_x_1902_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object* v_as_1904_, lean_object* v_i_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1904_, v_i_1905_);
lean_dec_ref(v_as_1904_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object* v_as_1907_, lean_object* v_i_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1907_, v_i_1908_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object* v_as_1911_, lean_object* v_i_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(v_as_1911_, v_i_1912_, v_a_1913_);
lean_dec_ref(v_as_1911_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object* v_stx_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1915_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_box(2);
return v___x_1917_;
}
else
{
lean_object* v_val_1918_; 
v_val_1918_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_val_1918_);
lean_dec_ref_known(v___x_1916_, 1);
return v_val_1918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object* v_stx_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_Syntax_getTailInfo(v_stx_1919_);
lean_dec(v_stx_1919_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object* v_stx_1921_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1921_);
if (lean_obj_tag(v___x_1922_) == 1)
{
lean_object* v_val_1923_; 
v_val_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_val_1923_);
lean_dec_ref_known(v___x_1922_, 1);
if (lean_obj_tag(v_val_1923_) == 0)
{
lean_object* v_trailing_1924_; lean_object* v_startPos_1925_; lean_object* v_stopPos_1926_; lean_object* v___x_1927_; 
v_trailing_1924_ = lean_ctor_get(v_val_1923_, 2);
lean_inc_ref(v_trailing_1924_);
lean_dec_ref_known(v_val_1923_, 4);
v_startPos_1925_ = lean_ctor_get(v_trailing_1924_, 1);
lean_inc(v_startPos_1925_);
v_stopPos_1926_ = lean_ctor_get(v_trailing_1924_, 2);
lean_inc(v_stopPos_1926_);
lean_dec_ref(v_trailing_1924_);
v___x_1927_ = lean_nat_sub(v_stopPos_1926_, v_startPos_1925_);
lean_dec(v_startPos_1925_);
lean_dec(v_stopPos_1926_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; 
lean_dec(v_val_1923_);
v___x_1928_ = lean_unsigned_to_nat(0u);
return v___x_1928_;
}
}
else
{
lean_object* v___x_1929_; 
lean_dec(v___x_1922_);
v___x_1929_ = lean_unsigned_to_nat(0u);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object* v_stx_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_Syntax_getTrailingSize(v_stx_1930_);
lean_dec(v_stx_1930_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object* v_stx_1932_){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = l_Lean_Syntax_getTailInfo(v_stx_1932_);
v___x_1934_ = l_Lean_SourceInfo_getTrailing_x3f(v___x_1933_);
lean_dec(v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object* v_stx_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_Syntax_getTrailing_x3f(v_stx_1935_);
lean_dec(v_stx_1935_);
return v_res_1936_;
}
}
lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object* v_stx_1937_, uint8_t v_canonicalOnly_1938_){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = l_Lean_Syntax_getTailInfo(v_stx_1937_);
v___x_1940_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v___x_1939_, v_canonicalOnly_1938_);
lean_dec(v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT void l_Lean_Syntax_getTrailingTailPos_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1937_ = stack[0].m_obj;
uint8_t v_canonicalOnly_1938_ = stack[1].m_num;
lean_object* v_res_1941_;
v_res_1941_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1937_, v_canonicalOnly_1938_);
stack->m_obj
 = v_res_1941_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object* v_stx_1942_, lean_object* v_canonicalOnly_1943_){
_start:
{
uint8_t v_canonicalOnly_boxed_1944_; lean_object* v_res_1945_; 
v_canonicalOnly_boxed_1944_ = lean_unbox(v_canonicalOnly_1943_);
v_res_1945_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1942_, v_canonicalOnly_boxed_1944_);
lean_dec(v_stx_1942_);
return v_res_1945_;
}
}
lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object* v_stx_1946_, uint8_t v_withLeading_1947_, uint8_t v_withTrailing_1948_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_Syntax_getHeadInfo(v_stx_1946_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_leading_1950_; lean_object* v_pos_1951_; lean_object* v___x_1952_; 
v_leading_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc_ref(v_leading_1950_);
v_pos_1951_ = lean_ctor_get(v___x_1949_, 1);
lean_inc(v_pos_1951_);
lean_dec_ref_known(v___x_1949_, 4);
v___x_1952_ = l_Lean_Syntax_getTailInfo(v_stx_1946_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_trailing_1953_; lean_object* v_endPos_1954_; lean_object* v_str_1955_; lean_object* v_startPos_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1970_; 
v_trailing_1953_ = lean_ctor_get(v___x_1952_, 2);
lean_inc_ref(v_trailing_1953_);
v_endPos_1954_ = lean_ctor_get(v___x_1952_, 3);
lean_inc(v_endPos_1954_);
lean_dec_ref_known(v___x_1952_, 4);
v_str_1955_ = lean_ctor_get(v_leading_1950_, 0);
v_startPos_1956_ = lean_ctor_get(v_leading_1950_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_leading_1950_);
if (v_isSharedCheck_1970_ == 0)
{
lean_object* v_unused_1971_; 
v_unused_1971_ = lean_ctor_get(v_leading_1950_, 2);
lean_dec(v_unused_1971_);
v___x_1958_ = v_leading_1950_;
v_isShared_1959_ = v_isSharedCheck_1970_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_startPos_1956_);
lean_inc(v_str_1955_);
lean_dec(v_leading_1950_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1970_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1968_; 
if (v_withLeading_1947_ == 0)
{
lean_dec(v_startPos_1956_);
v___y_1968_ = v_pos_1951_;
goto v___jp_1967_;
}
else
{
lean_dec(v_pos_1951_);
v___y_1968_ = v_startPos_1956_;
goto v___jp_1967_;
}
v___jp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 2, v___y_1962_);
lean_ctor_set(v___x_1958_, 1, v___y_1961_);
v___x_1964_ = v___x_1958_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_str_1955_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v___y_1961_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v___y_1962_);
v___x_1964_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1965_; 
v___x_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
return v___x_1965_;
}
}
v___jp_1967_:
{
if (v_withTrailing_1948_ == 0)
{
lean_dec_ref(v_trailing_1953_);
v___y_1961_ = v___y_1968_;
v___y_1962_ = v_endPos_1954_;
goto v___jp_1960_;
}
else
{
lean_object* v_stopPos_1969_; 
lean_dec(v_endPos_1954_);
v_stopPos_1969_ = lean_ctor_get(v_trailing_1953_, 2);
lean_inc(v_stopPos_1969_);
lean_dec_ref(v_trailing_1953_);
v___y_1961_ = v___y_1968_;
v___y_1962_ = v_stopPos_1969_;
goto v___jp_1960_;
}
}
}
}
else
{
lean_object* v___x_1972_; 
lean_dec(v___x_1952_);
lean_dec(v_pos_1951_);
lean_dec_ref(v_leading_1950_);
v___x_1972_ = lean_box(0);
return v___x_1972_;
}
}
else
{
lean_object* v___x_1973_; 
lean_dec(v___x_1949_);
v___x_1973_ = lean_box(0);
return v___x_1973_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_getSubstring_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1946_ = stack[0].m_obj;
uint8_t v_withLeading_1947_ = stack[1].m_num;
uint8_t v_withTrailing_1948_ = stack[2].m_num;
lean_object* v_res_1974_;
v_res_1974_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1946_, v_withLeading_1947_, v_withTrailing_1948_);
stack->m_obj
 = v_res_1974_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object* v_stx_1975_, lean_object* v_withLeading_1976_, lean_object* v_withTrailing_1977_){
_start:
{
uint8_t v_withLeading_boxed_1978_; uint8_t v_withTrailing_boxed_1979_; lean_object* v_res_1980_; 
v_withLeading_boxed_1978_ = lean_unbox(v_withLeading_1976_);
v_withTrailing_boxed_1979_ = lean_unbox(v_withTrailing_1977_);
v_res_1980_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1975_, v_withLeading_boxed_1978_, v_withTrailing_boxed_1979_);
lean_dec(v_stx_1975_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object* v_a_1981_, lean_object* v_f_1982_, lean_object* v_i_1983_){
_start:
{
lean_object* v_zero_1984_; uint8_t v_isZero_1985_; 
v_zero_1984_ = lean_unsigned_to_nat(0u);
v_isZero_1985_ = lean_nat_dec_eq(v_i_1983_, v_zero_1984_);
if (v_isZero_1985_ == 1)
{
lean_object* v___x_1986_; 
lean_dec(v_i_1983_);
lean_dec_ref(v_f_1982_);
lean_dec_ref(v_a_1981_);
v___x_1986_ = lean_box(0);
return v___x_1986_;
}
else
{
lean_object* v_one_1987_; lean_object* v_n_1988_; lean_object* v_v_1989_; lean_object* v___x_1990_; 
v_one_1987_ = lean_unsigned_to_nat(1u);
v_n_1988_ = lean_nat_sub(v_i_1983_, v_one_1987_);
lean_dec(v_i_1983_);
v_v_1989_ = lean_array_fget_borrowed(v_a_1981_, v_n_1988_);
lean_inc_ref(v_f_1982_);
lean_inc(v_v_1989_);
v___x_1990_ = lean_apply_1(v_f_1982_, v_v_1989_);
if (lean_obj_tag(v___x_1990_) == 0)
{
v_i_1983_ = v_n_1988_;
goto _start;
}
else
{
lean_object* v_val_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v_f_1982_);
v_val_1992_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1994_ = v___x_1990_;
v_isShared_1995_ = v_isSharedCheck_2000_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_val_1992_);
lean_dec(v___x_1990_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2000_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1996_ = lean_array_fset(v_a_1981_, v_n_1988_, v_val_1992_);
lean_dec(v_n_1988_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_1996_);
v___x_1998_ = v___x_1994_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object* v_00_u03b1_2001_, lean_object* v_a_2002_, lean_object* v_f_2003_, lean_object* v_i_2004_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(v_a_2002_, v_f_2003_, v_i_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* v_info_2006_, lean_object* v_x_2007_){
_start:
{
switch(lean_obj_tag(v_x_2007_))
{
case 2:
{
lean_object* v_val_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2016_; 
v_val_2008_ = lean_ctor_get(v_x_2007_, 1);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_x_2007_);
if (v_isSharedCheck_2016_ == 0)
{
lean_object* v_unused_2017_; 
v_unused_2017_ = lean_ctor_get(v_x_2007_, 0);
lean_dec(v_unused_2017_);
v___x_2010_ = v_x_2007_;
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_val_2008_);
lean_dec(v_x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v_info_2006_);
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_info_2006_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_val_2008_);
v___x_2013_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
return v___x_2014_;
}
}
}
case 3:
{
lean_object* v_rawVal_2018_; lean_object* v_val_2019_; lean_object* v_preresolved_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2028_; 
v_rawVal_2018_ = lean_ctor_get(v_x_2007_, 1);
v_val_2019_ = lean_ctor_get(v_x_2007_, 2);
v_preresolved_2020_ = lean_ctor_get(v_x_2007_, 3);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_x_2007_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; 
v_unused_2029_ = lean_ctor_get(v_x_2007_, 0);
lean_dec(v_unused_2029_);
v___x_2022_ = v_x_2007_;
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_preresolved_2020_);
lean_inc(v_val_2019_);
lean_inc(v_rawVal_2018_);
lean_dec(v_x_2007_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v_info_2006_);
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_info_2006_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_rawVal_2018_);
lean_ctor_set(v_reuseFailAlloc_2027_, 2, v_val_2019_);
lean_ctor_set(v_reuseFailAlloc_2027_, 3, v_preresolved_2020_);
v___x_2025_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
return v___x_2026_;
}
}
}
case 1:
{
lean_object* v_info_2030_; lean_object* v_kind_2031_; lean_object* v_args_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2050_; 
v_info_2030_ = lean_ctor_get(v_x_2007_, 0);
v_kind_2031_ = lean_ctor_get(v_x_2007_, 1);
v_args_2032_ = lean_ctor_get(v_x_2007_, 2);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_x_2007_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2034_ = v_x_2007_;
v_isShared_2035_ = v_isSharedCheck_2050_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_args_2032_);
lean_inc(v_kind_2031_);
lean_inc(v_info_2030_);
lean_dec(v_x_2007_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2050_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = lean_array_get_size(v_args_2032_);
v___x_2037_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(v_info_2006_, v_args_2032_, v___x_2036_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v___x_2038_; 
lean_del_object(v___x_2034_);
lean_dec(v_kind_2031_);
lean_dec(v_info_2030_);
v___x_2038_ = lean_box(0);
return v___x_2038_;
}
else
{
lean_object* v_val_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2049_; 
v_val_2039_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2041_ = v___x_2037_;
v_isShared_2042_ = v_isSharedCheck_2049_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_val_2039_);
lean_dec(v___x_2037_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2049_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 2, v_val_2039_);
v___x_2044_ = v___x_2034_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_info_2030_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_kind_2031_);
lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_val_2039_);
v___x_2044_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2046_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2044_);
v___x_2046_ = v___x_2041_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2051_; 
lean_dec(v_x_2007_);
lean_dec(v_info_2006_);
v___x_2051_ = lean_box(0);
return v___x_2051_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object* v_info_2052_, lean_object* v_a_2053_, lean_object* v_i_2054_){
_start:
{
lean_object* v_zero_2055_; uint8_t v_isZero_2056_; 
v_zero_2055_ = lean_unsigned_to_nat(0u);
v_isZero_2056_ = lean_nat_dec_eq(v_i_2054_, v_zero_2055_);
if (v_isZero_2056_ == 1)
{
lean_object* v___x_2057_; 
lean_dec(v_i_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_info_2052_);
v___x_2057_ = lean_box(0);
return v___x_2057_;
}
else
{
lean_object* v_one_2058_; lean_object* v_n_2059_; lean_object* v_v_2060_; lean_object* v___x_2061_; 
v_one_2058_ = lean_unsigned_to_nat(1u);
v_n_2059_ = lean_nat_sub(v_i_2054_, v_one_2058_);
lean_dec(v_i_2054_);
v_v_2060_ = lean_array_fget_borrowed(v_a_2053_, v_n_2059_);
lean_inc(v_v_2060_);
lean_inc(v_info_2052_);
v___x_2061_ = l_Lean_Syntax_setTailInfoAux(v_info_2052_, v_v_2060_);
if (lean_obj_tag(v___x_2061_) == 0)
{
v_i_2054_ = v_n_2059_;
goto _start;
}
else
{
lean_object* v_val_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2071_; 
lean_dec(v_info_2052_);
v_val_2063_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2065_ = v___x_2061_;
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_val_2063_);
lean_dec(v___x_2061_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_array_fset(v_a_2053_, v_n_2059_, v_val_2063_);
lean_dec(v_n_2059_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2067_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object* v_stx_2072_, lean_object* v_info_2073_){
_start:
{
lean_object* v___x_2074_; 
lean_inc(v_stx_2072_);
v___x_2074_ = l_Lean_Syntax_setTailInfoAux(v_info_2073_, v_stx_2072_);
if (lean_obj_tag(v___x_2074_) == 0)
{
return v_stx_2072_;
}
else
{
lean_object* v_val_2075_; 
lean_dec(v_stx_2072_);
v_val_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_val_2075_);
lean_dec_ref_known(v___x_2074_, 1);
return v_val_2075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object* v_stx_2076_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Syntax_getTailInfo(v_stx_2076_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_trailing_2078_; lean_object* v_leading_2079_; lean_object* v_pos_2080_; lean_object* v_endPos_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2099_; 
v_trailing_2078_ = lean_ctor_get(v___x_2077_, 2);
v_leading_2079_ = lean_ctor_get(v___x_2077_, 0);
v_pos_2080_ = lean_ctor_get(v___x_2077_, 1);
v_endPos_2081_ = lean_ctor_get(v___x_2077_, 3);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2083_ = v___x_2077_;
v_isShared_2084_ = v_isSharedCheck_2099_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_endPos_2081_);
lean_inc(v_trailing_2078_);
lean_inc(v_pos_2080_);
lean_inc(v_leading_2079_);
lean_dec(v___x_2077_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2099_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_str_2085_; lean_object* v_startPos_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2097_; 
v_str_2085_ = lean_ctor_get(v_trailing_2078_, 0);
v_startPos_2086_ = lean_ctor_get(v_trailing_2078_, 1);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_trailing_2078_);
if (v_isSharedCheck_2097_ == 0)
{
lean_object* v_unused_2098_; 
v_unused_2098_ = lean_ctor_get(v_trailing_2078_, 2);
lean_dec(v_unused_2098_);
v___x_2088_ = v_trailing_2078_;
v_isShared_2089_ = v_isSharedCheck_2097_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_startPos_2086_);
lean_inc(v_str_2085_);
lean_dec(v_trailing_2078_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2097_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
lean_inc(v_startPos_2086_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 2, v_startPos_2086_);
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_str_2085_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_startPos_2086_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_startPos_2086_);
v___x_2091_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2093_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 2, v___x_2091_);
v___x_2093_ = v___x_2083_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_leading_2079_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_pos_2080_);
lean_ctor_set(v_reuseFailAlloc_2095_, 2, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2095_, 3, v_endPos_2081_);
v___x_2093_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_Syntax_setTailInfo(v_stx_2076_, v___x_2093_);
return v___x_2094_;
}
}
}
}
}
else
{
lean_dec(v___x_2077_);
return v_stx_2076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object* v_a_2100_, lean_object* v_f_2101_, lean_object* v_i_2102_){
_start:
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = lean_array_get_size(v_a_2100_);
v___x_2104_ = lean_nat_dec_lt(v_i_2102_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; 
lean_dec(v_i_2102_);
lean_dec_ref(v_f_2101_);
lean_dec_ref(v_a_2100_);
v___x_2105_ = lean_box(0);
return v___x_2105_;
}
else
{
lean_object* v_v_2106_; lean_object* v___x_2107_; 
v_v_2106_ = lean_array_fget_borrowed(v_a_2100_, v_i_2102_);
lean_inc_ref(v_f_2101_);
lean_inc(v_v_2106_);
v___x_2107_ = lean_apply_1(v_f_2101_, v_v_2106_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = lean_unsigned_to_nat(1u);
v___x_2109_ = lean_nat_add(v_i_2102_, v___x_2108_);
lean_dec(v_i_2102_);
v_i_2102_ = v___x_2109_;
goto _start;
}
else
{
lean_object* v_val_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref(v_f_2101_);
v_val_2111_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2113_ = v___x_2107_;
v_isShared_2114_ = v_isSharedCheck_2119_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_val_2111_);
lean_dec(v___x_2107_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2119_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2115_ = lean_array_fset(v_a_2100_, v_i_2102_, v_val_2111_);
lean_dec(v_i_2102_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2115_);
v___x_2117_ = v___x_2113_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object* v_00_u03b1_2120_, lean_object* v_inst_2121_, lean_object* v_a_2122_, lean_object* v_f_2123_, lean_object* v_i_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(v_a_2122_, v_f_2123_, v_i_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object* v_00_u03b1_2126_, lean_object* v_inst_2127_, lean_object* v_a_2128_, lean_object* v_f_2129_, lean_object* v_i_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(v_00_u03b1_2126_, v_inst_2127_, v_a_2128_, v_f_2129_, v_i_2130_);
lean_dec(v_inst_2127_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object* v_info_2132_, lean_object* v_x_2133_){
_start:
{
switch(lean_obj_tag(v_x_2133_))
{
case 2:
{
lean_object* v_val_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2142_; 
v_val_2134_ = lean_ctor_get(v_x_2133_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_x_2133_);
if (v_isSharedCheck_2142_ == 0)
{
lean_object* v_unused_2143_; 
v_unused_2143_ = lean_ctor_get(v_x_2133_, 0);
lean_dec(v_unused_2143_);
v___x_2136_ = v_x_2133_;
v_isShared_2137_ = v_isSharedCheck_2142_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_val_2134_);
lean_dec(v_x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2142_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v_info_2132_);
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_info_2132_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_val_2134_);
v___x_2139_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2140_; 
v___x_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
return v___x_2140_;
}
}
}
case 3:
{
lean_object* v_rawVal_2144_; lean_object* v_val_2145_; lean_object* v_preresolved_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2154_; 
v_rawVal_2144_ = lean_ctor_get(v_x_2133_, 1);
v_val_2145_ = lean_ctor_get(v_x_2133_, 2);
v_preresolved_2146_ = lean_ctor_get(v_x_2133_, 3);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_x_2133_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v_x_2133_, 0);
lean_dec(v_unused_2155_);
v___x_2148_ = v_x_2133_;
v_isShared_2149_ = v_isSharedCheck_2154_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_preresolved_2146_);
lean_inc(v_val_2145_);
lean_inc(v_rawVal_2144_);
lean_dec(v_x_2133_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2154_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v_info_2132_);
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_info_2132_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_rawVal_2144_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_val_2145_);
lean_ctor_set(v_reuseFailAlloc_2153_, 3, v_preresolved_2146_);
v___x_2151_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
return v___x_2152_;
}
}
}
case 1:
{
lean_object* v_info_2156_; lean_object* v_kind_2157_; lean_object* v_args_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2176_; 
v_info_2156_ = lean_ctor_get(v_x_2133_, 0);
v_kind_2157_ = lean_ctor_get(v_x_2133_, 1);
v_args_2158_ = lean_ctor_get(v_x_2133_, 2);
v_isSharedCheck_2176_ = !lean_is_exclusive(v_x_2133_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2160_ = v_x_2133_;
v_isShared_2161_ = v_isSharedCheck_2176_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_args_2158_);
lean_inc(v_kind_2157_);
lean_inc(v_info_2156_);
lean_dec(v_x_2133_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2176_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_unsigned_to_nat(0u);
v___x_2163_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(v_info_2132_, v_args_2158_, v___x_2162_);
if (lean_obj_tag(v___x_2163_) == 1)
{
lean_object* v_val_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2174_; 
v_val_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2174_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_val_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2174_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 2, v_val_2164_);
v___x_2169_ = v___x_2160_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_info_2156_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_kind_2157_);
lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_val_2164_);
v___x_2169_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2171_; 
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2169_);
v___x_2171_ = v___x_2166_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_object* v___x_2175_; 
lean_dec(v___x_2163_);
lean_del_object(v___x_2160_);
lean_dec(v_kind_2157_);
lean_dec(v_info_2156_);
v___x_2175_ = lean_box(0);
return v___x_2175_;
}
}
}
default: 
{
lean_object* v___x_2177_; 
lean_dec(v_x_2133_);
lean_dec(v_info_2132_);
v___x_2177_ = lean_box(0);
return v___x_2177_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object* v_info_2178_, lean_object* v_a_2179_, lean_object* v_i_2180_){
_start:
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = lean_array_get_size(v_a_2179_);
v___x_2182_ = lean_nat_dec_lt(v_i_2180_, v___x_2181_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; 
lean_dec(v_i_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_info_2178_);
v___x_2183_ = lean_box(0);
return v___x_2183_;
}
else
{
lean_object* v_v_2184_; lean_object* v___x_2185_; 
v_v_2184_ = lean_array_fget_borrowed(v_a_2179_, v_i_2180_);
lean_inc(v_v_2184_);
lean_inc(v_info_2178_);
v___x_2185_ = l_Lean_Syntax_setHeadInfoAux(v_info_2178_, v_v_2184_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_unsigned_to_nat(1u);
v___x_2187_ = lean_nat_add(v_i_2180_, v___x_2186_);
lean_dec(v_i_2180_);
v_i_2180_ = v___x_2187_;
goto _start;
}
else
{
lean_object* v_val_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_info_2178_);
v_val_2189_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2191_ = v___x_2185_;
v_isShared_2192_ = v_isSharedCheck_2197_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_val_2189_);
lean_dec(v___x_2185_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2197_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2193_ = lean_array_fset(v_a_2179_, v_i_2180_, v_val_2189_);
lean_dec(v_i_2180_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2193_);
v___x_2195_ = v___x_2191_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object* v_stx_2198_, lean_object* v_info_2199_){
_start:
{
lean_object* v___x_2200_; 
lean_inc(v_stx_2198_);
v___x_2200_ = l_Lean_Syntax_setHeadInfoAux(v_info_2199_, v_stx_2198_);
if (lean_obj_tag(v___x_2200_) == 0)
{
return v_stx_2198_;
}
else
{
lean_object* v_val_2201_; 
lean_dec(v_stx_2198_);
v_val_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_val_2201_);
lean_dec_ref_known(v___x_2200_, 1);
return v_val_2201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object* v_info_2202_, lean_object* v_x_2203_){
_start:
{
switch(lean_obj_tag(v_x_2203_))
{
case 0:
{
lean_dec(v_info_2202_);
return v_x_2203_;
}
case 1:
{
lean_object* v_kind_2204_; lean_object* v_args_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
v_kind_2204_ = lean_ctor_get(v_x_2203_, 1);
v_args_2205_ = lean_ctor_get(v_x_2203_, 2);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_x_2203_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v_x_2203_, 0);
lean_dec(v_unused_2213_);
v___x_2207_ = v_x_2203_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_args_2205_);
lean_inc(v_kind_2204_);
lean_dec(v_x_2203_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v_info_2202_);
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_info_2202_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_kind_2204_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_args_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
case 2:
{
lean_object* v_val_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
v_val_2214_ = lean_ctor_get(v_x_2203_, 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_x_2203_);
if (v_isSharedCheck_2221_ == 0)
{
lean_object* v_unused_2222_; 
v_unused_2222_ = lean_ctor_get(v_x_2203_, 0);
lean_dec(v_unused_2222_);
v___x_2216_ = v_x_2203_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_val_2214_);
lean_dec(v_x_2203_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v_info_2202_);
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_info_2202_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_val_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
default: 
{
lean_object* v_rawVal_2223_; lean_object* v_val_2224_; lean_object* v_preresolved_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
v_rawVal_2223_ = lean_ctor_get(v_x_2203_, 1);
v_val_2224_ = lean_ctor_get(v_x_2203_, 2);
v_preresolved_2225_ = lean_ctor_get(v_x_2203_, 3);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_x_2203_);
if (v_isSharedCheck_2232_ == 0)
{
lean_object* v_unused_2233_; 
v_unused_2233_ = lean_ctor_get(v_x_2203_, 0);
lean_dec(v_unused_2233_);
v___x_2227_ = v_x_2203_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_preresolved_2225_);
lean_inc(v_val_2224_);
lean_inc(v_rawVal_2223_);
lean_dec(v_x_2203_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v_info_2202_);
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_info_2202_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_rawVal_2223_);
lean_ctor_set(v_reuseFailAlloc_2231_, 2, v_val_2224_);
lean_ctor_set(v_reuseFailAlloc_2231_, 3, v_preresolved_2225_);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object* v_x_2237_){
_start:
{
switch(lean_obj_tag(v_x_2237_))
{
case 2:
{
lean_object* v_info_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; 
v_info_2238_ = lean_ctor_get(v_x_2237_, 0);
v___x_2239_ = 0;
v___x_2240_ = l_Lean_SourceInfo_getPos_x3f(v_info_2238_, v___x_2239_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v___x_2241_; 
lean_dec_ref_known(v_x_2237_, 2);
v___x_2241_ = lean_box(0);
return v___x_2241_;
}
else
{
lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2248_ == 0)
{
lean_object* v_unused_2249_; 
v_unused_2249_ = lean_ctor_get(v___x_2240_, 0);
lean_dec(v_unused_2249_);
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v_x_2237_);
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_x_2237_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
case 3:
{
lean_object* v_info_2250_; uint8_t v___x_2251_; lean_object* v___x_2252_; 
v_info_2250_ = lean_ctor_get(v_x_2237_, 0);
v___x_2251_ = 0;
v___x_2252_ = l_Lean_SourceInfo_getPos_x3f(v_info_2250_, v___x_2251_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v___x_2253_; 
lean_dec_ref_known(v_x_2237_, 4);
v___x_2253_ = lean_box(0);
return v___x_2253_;
}
else
{
lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2260_ == 0)
{
lean_object* v_unused_2261_; 
v_unused_2261_ = lean_ctor_get(v___x_2252_, 0);
lean_dec(v_unused_2261_);
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v_x_2237_);
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_x_2237_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
case 1:
{
lean_object* v_info_2262_; 
v_info_2262_ = lean_ctor_get(v_x_2237_, 0);
if (lean_obj_tag(v_info_2262_) == 2)
{
lean_object* v_args_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; size_t v_sz_2266_; size_t v___x_2267_; lean_object* v___x_2268_; lean_object* v_fst_2269_; 
v_args_2263_ = lean_ctor_get(v_x_2237_, 2);
lean_inc_ref(v_args_2263_);
lean_dec_ref_known(v_x_2237_, 3);
v___x_2264_ = lean_box(0);
v___x_2265_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_2266_ = lean_array_size(v_args_2263_);
v___x_2267_ = ((size_t)0ULL);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_args_2263_, v_sz_2266_, v___x_2267_, v___x_2265_);
lean_dec_ref(v_args_2263_);
v_fst_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_fst_2269_);
lean_dec_ref(v___x_2268_);
if (lean_obj_tag(v_fst_2269_) == 0)
{
return v___x_2264_;
}
else
{
lean_object* v_val_2270_; 
v_val_2270_ = lean_ctor_get(v_fst_2269_, 0);
lean_inc(v_val_2270_);
lean_dec_ref_known(v_fst_2269_, 1);
return v_val_2270_;
}
}
else
{
lean_object* v___x_2271_; 
v___x_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2271_, 0, v_x_2237_);
return v___x_2271_;
}
}
default: 
{
lean_object* v___x_2272_; 
lean_dec(v_x_2237_);
v___x_2272_ = lean_box(0);
return v___x_2272_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object* v_as_2273_, size_t v_sz_2274_, size_t v_i_2275_, lean_object* v_b_2276_){
_start:
{
uint8_t v___x_2277_; 
v___x_2277_ = lean_usize_dec_lt(v_i_2275_, v_sz_2274_);
if (v___x_2277_ == 0)
{
lean_inc_ref(v_b_2276_);
return v_b_2276_;
}
else
{
lean_object* v___x_2278_; lean_object* v_a_2279_; lean_object* v___x_2280_; 
v___x_2278_ = lean_box(0);
v_a_2279_ = lean_array_uget_borrowed(v_as_2273_, v_i_2275_);
lean_inc(v_a_2279_);
v___x_2280_ = l_Lean_Syntax_getHead_x3f(v_a_2279_);
if (lean_obj_tag(v___x_2280_) == 1)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
v___x_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v___x_2278_);
return v___x_2282_;
}
else
{
lean_object* v___x_2283_; size_t v___x_2284_; size_t v___x_2285_; 
lean_dec(v___x_2280_);
v___x_2283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_2284_ = ((size_t)1ULL);
v___x_2285_ = lean_usize_add(v_i_2275_, v___x_2284_);
v_i_2275_ = v___x_2285_;
v_b_2276_ = v___x_2283_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2273_ = stack[0].m_obj;
size_t v_sz_2274_ = stack[1].m_num;
size_t v_i_2275_ = stack[2].m_num;
lean_object* v_b_2276_ = stack[3].m_obj;
lean_object* v_res_2287_;
v_res_2287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_as_2273_, v_sz_2274_, v_i_2275_, v_b_2276_);
stack->m_obj
 = v_res_2287_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object* v_as_2288_, lean_object* v_sz_2289_, lean_object* v_i_2290_, lean_object* v_b_2291_){
_start:
{
size_t v_sz_boxed_2292_; size_t v_i_boxed_2293_; lean_object* v_res_2294_; 
v_sz_boxed_2292_ = lean_unbox_usize(v_sz_2289_);
lean_dec(v_sz_2289_);
v_i_boxed_2293_ = lean_unbox_usize(v_i_2290_);
lean_dec(v_i_2290_);
v_res_2294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_as_2288_, v_sz_boxed_2292_, v_i_boxed_2293_, v_b_2291_);
lean_dec_ref(v_b_2291_);
lean_dec_ref(v_as_2288_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object* v_target_2295_, lean_object* v_source_2296_){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2297_ = l_Lean_Syntax_getHeadInfo(v_source_2296_);
v___x_2298_ = l_Lean_Syntax_setHeadInfo(v_target_2295_, v___x_2297_);
v___x_2299_ = l_Lean_Syntax_getTailInfo(v_source_2296_);
v___x_2300_ = l_Lean_Syntax_setTailInfo(v___x_2298_, v___x_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object* v_target_2301_, lean_object* v_source_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_target_2301_, v_source_2302_);
lean_dec(v_source_2302_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object* v_stx_2304_){
_start:
{
uint8_t v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = 0;
v___x_2306_ = l_Lean_SourceInfo_fromRef(v_stx_2304_, v___x_2305_);
v___x_2307_ = l_Lean_Syntax_setHeadInfo(v_stx_2304_, v___x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object* v_val_2308_, lean_object* v_withRef_2309_, lean_object* v_x_2310_, lean_object* v_oldRef_2311_){
_start:
{
lean_object* v_ref_2312_; lean_object* v___x_2313_; 
v_ref_2312_ = l_Lean_replaceRef(v_val_2308_, v_oldRef_2311_);
v___x_2313_ = lean_apply_3(v_withRef_2309_, lean_box(0), v_ref_2312_, v_x_2310_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object* v_val_2314_, lean_object* v_withRef_2315_, lean_object* v_x_2316_, lean_object* v_oldRef_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_withHeadRefOnly___redArg___lam__0(v_val_2314_, v_withRef_2315_, v_x_2316_, v_oldRef_2317_);
lean_dec(v_oldRef_2317_);
lean_dec(v_val_2314_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object* v_x_2319_, lean_object* v_withRef_2320_, lean_object* v_toBind_2321_, lean_object* v_getRef_2322_, lean_object* v_____do__lift_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_Syntax_getHead_x3f(v_____do__lift_2323_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_dec(v_getRef_2322_);
lean_dec(v_toBind_2321_);
lean_dec(v_withRef_2320_);
return v_x_2319_;
}
else
{
lean_object* v_val_2325_; lean_object* v___f_2326_; lean_object* v___x_2327_; 
v_val_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_val_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v___f_2326_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2326_, 0, v_val_2325_);
lean_closure_set(v___f_2326_, 1, v_withRef_2320_);
lean_closure_set(v___f_2326_, 2, v_x_2319_);
v___x_2327_ = lean_apply_4(v_toBind_2321_, lean_box(0), lean_box(0), v_getRef_2322_, v___f_2326_);
return v___x_2327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object* v_inst_2328_, lean_object* v_inst_2329_, lean_object* v_x_2330_){
_start:
{
lean_object* v_toBind_2331_; lean_object* v_getRef_2332_; lean_object* v_withRef_2333_; lean_object* v___f_2334_; lean_object* v___x_2335_; 
v_toBind_2331_ = lean_ctor_get(v_inst_2328_, 1);
lean_inc_n(v_toBind_2331_, 2);
lean_dec_ref(v_inst_2328_);
v_getRef_2332_ = lean_ctor_get(v_inst_2329_, 0);
lean_inc_n(v_getRef_2332_, 2);
v_withRef_2333_ = lean_ctor_get(v_inst_2329_, 1);
lean_inc(v_withRef_2333_);
lean_dec_ref(v_inst_2329_);
v___f_2334_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2334_, 0, v_x_2330_);
lean_closure_set(v___f_2334_, 1, v_withRef_2333_);
lean_closure_set(v___f_2334_, 2, v_toBind_2331_);
lean_closure_set(v___f_2334_, 3, v_getRef_2332_);
v___x_2335_ = lean_apply_4(v_toBind_2331_, lean_box(0), lean_box(0), v_getRef_2332_, v___f_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object* v_m_2336_, lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_00_u03b1_2339_, lean_object* v_x_2340_){
_start:
{
lean_object* v_toBind_2341_; lean_object* v_getRef_2342_; lean_object* v_withRef_2343_; lean_object* v___f_2344_; lean_object* v___x_2345_; 
v_toBind_2341_ = lean_ctor_get(v_inst_2337_, 1);
lean_inc_n(v_toBind_2341_, 2);
lean_dec_ref(v_inst_2337_);
v_getRef_2342_ = lean_ctor_get(v_inst_2338_, 0);
lean_inc_n(v_getRef_2342_, 2);
v_withRef_2343_ = lean_ctor_get(v_inst_2338_, 1);
lean_inc(v_withRef_2343_);
lean_dec_ref(v_inst_2338_);
v___f_2344_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2344_, 0, v_x_2340_);
lean_closure_set(v___f_2344_, 1, v_withRef_2343_);
lean_closure_set(v___f_2344_, 2, v_toBind_2341_);
lean_closure_set(v___f_2344_, 3, v_getRef_2342_);
v___x_2345_ = lean_apply_4(v_toBind_2341_, lean_box(0), lean_box(0), v_getRef_2342_, v___f_2344_);
return v___x_2345_;
}
}
uint8_t l_Lean_expandMacros___lam__0(uint8_t v___x_2355_, lean_object* v_k_2356_){
_start:
{
lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2357_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_2358_ = lean_name_eq(v_k_2356_, v___x_2357_);
if (v___x_2358_ == 0)
{
return v___x_2355_;
}
else
{
uint8_t v___x_2359_; 
v___x_2359_ = 0;
return v___x_2359_;
}
}
}
LEAN_EXPORT void l_Lean_expandMacros___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2355_ = stack[0].m_num;
lean_object* v_k_2356_ = stack[1].m_obj;
uint8_t v_res_2360_;
v_res_2360_ = l_Lean_expandMacros___lam__0(v___x_2355_, v_k_2356_);
stack->m_num = v_res_2360_;
}
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object* v___x_2361_, lean_object* v_k_2362_){
_start:
{
uint8_t v___x_1783__boxed_2363_; uint8_t v_res_2364_; lean_object* v_r_2365_; 
v___x_1783__boxed_2363_ = lean_unbox(v___x_2361_);
v_res_2364_ = l_Lean_expandMacros___lam__0(v___x_1783__boxed_2363_, v_k_2362_);
lean_dec(v_k_2362_);
v_r_2365_ = lean_box(v_res_2364_);
return v_r_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object* v_stx_2367_, lean_object* v_p_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
if (lean_obj_tag(v_stx_2367_) == 1)
{
lean_object* v_info_2371_; lean_object* v_kind_2372_; lean_object* v_args_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v_info_2371_ = lean_ctor_get(v_stx_2367_, 0);
v_kind_2372_ = lean_ctor_get(v_stx_2367_, 1);
v_args_2373_ = lean_ctor_get(v_stx_2367_, 2);
lean_inc(v_kind_2372_);
v___x_2374_ = lean_apply_1(v_p_2368_, v_kind_2372_);
v___x_2375_ = lean_unbox(v___x_2374_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; 
lean_dec_ref(v_a_2369_);
v___x_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2376_, 0, v_stx_2367_);
lean_ctor_set(v___x_2376_, 1, v_a_2370_);
return v___x_2376_;
}
else
{
lean_object* v_methods_2377_; lean_object* v_quotContext_2378_; lean_object* v_currMacroScope_2379_; lean_object* v_currRecDepth_2380_; lean_object* v_maxRecDepth_2381_; lean_object* v_ref_2382_; lean_object* v_ref_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_methods_2377_ = lean_ctor_get(v_a_2369_, 0);
lean_inc_n(v_methods_2377_, 2);
v_quotContext_2378_ = lean_ctor_get(v_a_2369_, 1);
lean_inc_n(v_quotContext_2378_, 2);
v_currMacroScope_2379_ = lean_ctor_get(v_a_2369_, 2);
lean_inc_n(v_currMacroScope_2379_, 2);
v_currRecDepth_2380_ = lean_ctor_get(v_a_2369_, 3);
lean_inc_n(v_currRecDepth_2380_, 2);
v_maxRecDepth_2381_ = lean_ctor_get(v_a_2369_, 4);
lean_inc_n(v_maxRecDepth_2381_, 2);
v_ref_2382_ = lean_ctor_get(v_a_2369_, 5);
lean_inc(v_ref_2382_);
lean_dec_ref(v_a_2369_);
v_ref_2383_ = l_Lean_replaceRef(v_stx_2367_, v_ref_2382_);
lean_dec(v_ref_2382_);
lean_inc(v_ref_2383_);
v___x_2384_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2384_, 0, v_methods_2377_);
lean_ctor_set(v___x_2384_, 1, v_quotContext_2378_);
lean_ctor_set(v___x_2384_, 2, v_currMacroScope_2379_);
lean_ctor_set(v___x_2384_, 3, v_currRecDepth_2380_);
lean_ctor_set(v___x_2384_, 4, v_maxRecDepth_2381_);
lean_ctor_set(v___x_2384_, 5, v_ref_2383_);
lean_inc_ref(v_stx_2367_);
v___x_2385_ = l_Lean_Macro_expandMacro_x3f(v_stx_2367_, v___x_2384_, v_a_2370_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
if (lean_obj_tag(v_a_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2432_; 
lean_dec_ref_known(v___x_2384_, 6);
v_a_2387_ = lean_ctor_get(v___x_2385_, 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; 
v_unused_2433_ = lean_ctor_get(v___x_2385_, 0);
lean_dec(v_unused_2433_);
v___x_2389_ = v___x_2385_;
v_isShared_2390_ = v_isSharedCheck_2432_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2385_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2432_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_nat_dec_eq(v_currRecDepth_2380_, v_maxRecDepth_2381_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2423_; 
lean_inc_ref(v_args_2373_);
lean_inc(v_kind_2372_);
lean_inc(v_info_2371_);
lean_del_object(v___x_2389_);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_stx_2367_);
if (v_isSharedCheck_2423_ == 0)
{
lean_object* v_unused_2424_; lean_object* v_unused_2425_; lean_object* v_unused_2426_; 
v_unused_2424_ = lean_ctor_get(v_stx_2367_, 2);
lean_dec(v_unused_2424_);
v_unused_2425_ = lean_ctor_get(v_stx_2367_, 1);
lean_dec(v_unused_2425_);
v_unused_2426_ = lean_ctor_get(v_stx_2367_, 0);
lean_dec(v_unused_2426_);
v___x_2393_ = v_stx_2367_;
v_isShared_2394_ = v_isSharedCheck_2423_;
goto v_resetjp_2392_;
}
else
{
lean_dec(v_stx_2367_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2423_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; size_t v_sz_2398_; size_t v___x_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; 
v___x_2395_ = lean_unsigned_to_nat(1u);
v___x_2396_ = lean_nat_add(v_currRecDepth_2380_, v___x_2395_);
lean_dec(v_currRecDepth_2380_);
v___x_2397_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2397_, 0, v_methods_2377_);
lean_ctor_set(v___x_2397_, 1, v_quotContext_2378_);
lean_ctor_set(v___x_2397_, 2, v_currMacroScope_2379_);
lean_ctor_set(v___x_2397_, 3, v___x_2396_);
lean_ctor_set(v___x_2397_, 4, v_maxRecDepth_2381_);
lean_ctor_set(v___x_2397_, 5, v_ref_2383_);
v_sz_2398_ = lean_array_size(v_args_2373_);
v___x_2399_ = ((size_t)0ULL);
v___x_2400_ = lean_unbox(v___x_2374_);
v___x_2401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2400_, v_sz_2398_, v___x_2399_, v_args_2373_, v___x_2397_, v_a_2387_);
lean_dec_ref_known(v___x_2397_, 6);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2413_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_a_2403_ = lean_ctor_get(v___x_2401_, 1);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2405_ = v___x_2401_;
v_isShared_2406_ = v_isSharedCheck_2413_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2413_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 2, v_a_2402_);
v___x_2408_ = v___x_2393_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_info_2371_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_kind_2372_);
lean_ctor_set(v_reuseFailAlloc_2412_, 2, v_a_2402_);
v___x_2408_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2410_; 
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2408_);
v___x_2410_ = v___x_2405_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_a_2403_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_del_object(v___x_2393_);
lean_dec(v_kind_2372_);
lean_dec(v_info_2371_);
v_a_2414_ = lean_ctor_get(v___x_2401_, 0);
v_a_2415_ = lean_ctor_get(v___x_2401_, 1);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2401_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_inc(v_a_2414_);
lean_dec(v___x_2401_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2414_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2430_; 
lean_dec(v_ref_2383_);
lean_dec(v_maxRecDepth_2381_);
lean_dec(v_currRecDepth_2380_);
lean_dec(v_currMacroScope_2379_);
lean_dec(v_quotContext_2378_);
lean_dec(v_methods_2377_);
v___x_2427_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v_stx_2367_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set_tag(v___x_2389_, 1);
lean_ctor_set(v___x_2389_, 0, v___x_2428_);
v___x_2430_ = v___x_2389_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_a_2387_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v_val_2435_; lean_object* v___f_2436_; 
lean_inc_ref(v_a_2386_);
lean_dec(v_ref_2383_);
lean_dec(v_maxRecDepth_2381_);
lean_dec(v_currRecDepth_2380_);
lean_dec(v_currMacroScope_2379_);
lean_dec(v_quotContext_2378_);
lean_dec(v_methods_2377_);
lean_dec_ref_known(v_stx_2367_, 3);
v_a_2434_ = lean_ctor_get(v___x_2385_, 1);
lean_inc(v_a_2434_);
lean_dec_ref_known(v___x_2385_, 2);
v_val_2435_ = lean_ctor_get(v_a_2386_, 0);
lean_inc(v_val_2435_);
lean_dec_ref_known(v_a_2386_, 1);
v___f_2436_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2436_, 0, v___x_2374_);
v_stx_2367_ = v_val_2435_;
v_p_2368_ = v___f_2436_;
v_a_2369_ = v___x_2384_;
v_a_2370_ = v_a_2434_;
goto _start;
}
}
else
{
lean_object* v_a_2438_; lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_dec_ref_known(v___x_2384_, 6);
lean_dec(v_ref_2383_);
lean_dec(v_maxRecDepth_2381_);
lean_dec(v_currRecDepth_2380_);
lean_dec(v_currMacroScope_2379_);
lean_dec(v_quotContext_2378_);
lean_dec(v_methods_2377_);
lean_dec_ref_known(v_stx_2367_, 3);
v_a_2438_ = lean_ctor_get(v___x_2385_, 0);
v_a_2439_ = lean_ctor_get(v___x_2385_, 1);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2385_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_inc(v_a_2438_);
lean_dec(v___x_2385_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2438_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
else
{
lean_object* v___x_2447_; 
lean_dec_ref(v_a_2369_);
lean_dec_ref(v_p_2368_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v_stx_2367_);
lean_ctor_set(v___x_2447_, 1, v_a_2370_);
return v___x_2447_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t v___x_2448_, size_t v_sz_2449_, size_t v_i_2450_, lean_object* v_bs_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
uint8_t v___x_2454_; 
v___x_2454_ = lean_usize_dec_lt(v_i_2450_, v_sz_2449_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; 
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v_bs_2451_);
lean_ctor_set(v___x_2455_, 1, v___y_2453_);
return v___x_2455_;
}
else
{
lean_object* v___x_2456_; lean_object* v___f_2457_; lean_object* v_v_2458_; lean_object* v___x_2459_; 
v___x_2456_ = lean_box(v___x_2448_);
v___f_2457_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2457_, 0, v___x_2456_);
v_v_2458_ = lean_array_uget_borrowed(v_bs_2451_, v_i_2450_);
lean_inc_ref(v___y_2452_);
lean_inc(v_v_2458_);
v___x_2459_ = l_Lean_expandMacros(v_v_2458_, v___f_2457_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v_a_2461_; lean_object* v___x_2462_; lean_object* v_bs_x27_2463_; size_t v___x_2464_; size_t v___x_2465_; lean_object* v___x_2466_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
v_a_2461_ = lean_ctor_get(v___x_2459_, 1);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___x_2459_, 2);
v___x_2462_ = lean_unsigned_to_nat(0u);
v_bs_x27_2463_ = lean_array_uset(v_bs_2451_, v_i_2450_, v___x_2462_);
v___x_2464_ = ((size_t)1ULL);
v___x_2465_ = lean_usize_add(v_i_2450_, v___x_2464_);
v___x_2466_ = lean_array_uset(v_bs_x27_2463_, v_i_2450_, v_a_2460_);
v_i_2450_ = v___x_2465_;
v_bs_2451_ = v___x_2466_;
v___y_2453_ = v_a_2461_;
goto _start;
}
else
{
lean_object* v_a_2468_; lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v_bs_2451_);
v_a_2468_ = lean_ctor_get(v___x_2459_, 0);
v_a_2469_ = lean_ctor_get(v___x_2459_, 1);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2459_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_inc(v_a_2468_);
lean_dec(v___x_2459_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2468_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2448_ = stack[0].m_num;
size_t v_sz_2449_ = stack[1].m_num;
size_t v_i_2450_ = stack[2].m_num;
lean_object* v_bs_2451_ = stack[3].m_obj;
lean_object* v___y_2452_ = stack[4].m_obj;
lean_object* v___y_2453_ = stack[5].m_obj;
lean_object* v_res_2477_;
v_res_2477_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2448_, v_sz_2449_, v_i_2450_, v_bs_2451_, v___y_2452_, v___y_2453_);
stack->m_obj
 = v_res_2477_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object* v___x_2478_, lean_object* v_sz_2479_, lean_object* v_i_2480_, lean_object* v_bs_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
uint8_t v___x_1816__boxed_2484_; size_t v_sz_boxed_2485_; size_t v_i_boxed_2486_; lean_object* v_res_2487_; 
v___x_1816__boxed_2484_ = lean_unbox(v___x_2478_);
v_sz_boxed_2485_ = lean_unbox_usize(v_sz_2479_);
lean_dec(v_sz_2479_);
v_i_boxed_2486_ = lean_unbox_usize(v_i_2480_);
lean_dec(v_i_2480_);
v_res_2487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_1816__boxed_2484_, v_sz_boxed_2485_, v_i_boxed_2486_, v_bs_2481_, v___y_2482_, v___y_2483_);
lean_dec_ref(v___y_2482_);
return v_res_2487_;
}
}
lean_object* l_Lean_mkIdentFrom(lean_object* v_src_2488_, lean_object* v_val_2489_, uint8_t v_canonical_2490_){
_start:
{
lean_object* v___x_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2491_ = l_Lean_SourceInfo_fromRef(v_src_2488_, v_canonical_2490_);
v___x_2492_ = 1;
lean_inc(v_val_2489_);
v___x_2493_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2489_, v___x_2492_);
v___x_2494_ = lean_unsigned_to_nat(0u);
v___x_2495_ = lean_string_utf8_byte_size(v___x_2493_);
v___x_2496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2493_);
lean_ctor_set(v___x_2496_, 1, v___x_2494_);
lean_ctor_set(v___x_2496_, 2, v___x_2495_);
v___x_2497_ = lean_box(0);
v___x_2498_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2491_);
lean_ctor_set(v___x_2498_, 1, v___x_2496_);
lean_ctor_set(v___x_2498_, 2, v_val_2489_);
lean_ctor_set(v___x_2498_, 3, v___x_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT void l_Lean_mkIdentFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_2488_ = stack[0].m_obj;
lean_object* v_val_2489_ = stack[1].m_obj;
uint8_t v_canonical_2490_ = stack[2].m_num;
lean_object* v_res_2499_;
v_res_2499_ = l_Lean_mkIdentFrom(v_src_2488_, v_val_2489_, v_canonical_2490_);
stack->m_obj
 = v_res_2499_;
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object* v_src_2500_, lean_object* v_val_2501_, lean_object* v_canonical_2502_){
_start:
{
uint8_t v_canonical_boxed_2503_; lean_object* v_res_2504_; 
v_canonical_boxed_2503_ = lean_unbox(v_canonical_2502_);
v_res_2504_ = l_Lean_mkIdentFrom(v_src_2500_, v_val_2501_, v_canonical_boxed_2503_);
lean_dec(v_src_2500_);
return v_res_2504_;
}
}
lean_object* l_Lean_mkMarkdownDocCommentFrom(lean_object* v_src_2520_, lean_object* v_text_2521_, uint8_t v_canonical_2522_){
_start:
{
lean_object* v_info_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v_body_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v_info_2523_ = l_Lean_SourceInfo_fromRef(v_src_2520_, v_canonical_2522_);
v___x_2524_ = lean_box(2);
v___x_2525_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__2));
lean_inc_n(v_info_2523_, 2);
v___x_2526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2526_, 0, v_info_2523_);
lean_ctor_set(v___x_2526_, 1, v_text_2521_);
v___x_2527_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__3));
v___x_2528_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2528_, 0, v_info_2523_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
v___x_2529_ = lean_unsigned_to_nat(2u);
v___x_2530_ = lean_mk_empty_array_with_capacity(v___x_2529_);
lean_inc_ref(v___x_2530_);
v___x_2531_ = lean_array_push(v___x_2530_, v___x_2526_);
v___x_2532_ = lean_array_push(v___x_2531_, v___x_2528_);
v_body_2533_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_body_2533_, 0, v___x_2524_);
lean_ctor_set(v_body_2533_, 1, v___x_2525_);
lean_ctor_set(v_body_2533_, 2, v___x_2532_);
v___x_2534_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__5));
v___x_2535_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__6));
v___x_2536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2536_, 0, v_info_2523_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = lean_array_push(v___x_2530_, v___x_2536_);
v___x_2538_ = lean_array_push(v___x_2537_, v_body_2533_);
v___x_2539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2524_);
lean_ctor_set(v___x_2539_, 1, v___x_2534_);
lean_ctor_set(v___x_2539_, 2, v___x_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT void l_Lean_mkMarkdownDocCommentFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_2520_ = stack[0].m_obj;
lean_object* v_text_2521_ = stack[1].m_obj;
uint8_t v_canonical_2522_ = stack[2].m_num;
lean_object* v_res_2540_;
v_res_2540_ = l_Lean_mkMarkdownDocCommentFrom(v_src_2520_, v_text_2521_, v_canonical_2522_);
stack->m_obj
 = v_res_2540_;
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom___boxed(lean_object* v_src_2541_, lean_object* v_text_2542_, lean_object* v_canonical_2543_){
_start:
{
uint8_t v_canonical_boxed_2544_; lean_object* v_res_2545_; 
v_canonical_boxed_2544_ = lean_unbox(v_canonical_2543_);
v_res_2545_ = l_Lean_mkMarkdownDocCommentFrom(v_src_2541_, v_text_2542_, v_canonical_boxed_2544_);
lean_dec(v_src_2541_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocComment(lean_object* v_text_2546_){
_start:
{
lean_object* v___x_2547_; uint8_t v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = lean_box(0);
v___x_2548_ = 0;
v___x_2549_ = l_Lean_mkMarkdownDocCommentFrom(v___x_2547_, v_text_2546_, v___x_2548_);
return v___x_2549_;
}
}
lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object* v_val_2550_, uint8_t v_canonical_2551_, lean_object* v_toPure_2552_, lean_object* v_____do__lift_2553_){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = l_Lean_mkIdentFrom(v_____do__lift_2553_, v_val_2550_, v_canonical_2551_);
v___x_2555_ = lean_apply_2(v_toPure_2552_, lean_box(0), v___x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT void l_Lean_mkIdentFromRef___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2550_ = stack[0].m_obj;
uint8_t v_canonical_2551_ = stack[1].m_num;
lean_object* v_toPure_2552_ = stack[2].m_obj;
lean_object* v_____do__lift_2553_ = stack[3].m_obj;
lean_object* v_res_2556_;
v_res_2556_ = l_Lean_mkIdentFromRef___redArg___lam__0(v_val_2550_, v_canonical_2551_, v_toPure_2552_, v_____do__lift_2553_);
stack->m_obj
 = v_res_2556_;
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object* v_val_2557_, lean_object* v_canonical_2558_, lean_object* v_toPure_2559_, lean_object* v_____do__lift_2560_){
_start:
{
uint8_t v_canonical_boxed_2561_; lean_object* v_res_2562_; 
v_canonical_boxed_2561_ = lean_unbox(v_canonical_2558_);
v_res_2562_ = l_Lean_mkIdentFromRef___redArg___lam__0(v_val_2557_, v_canonical_boxed_2561_, v_toPure_2559_, v_____do__lift_2560_);
lean_dec(v_____do__lift_2560_);
return v_res_2562_;
}
}
lean_object* l_Lean_mkIdentFromRef___redArg(lean_object* v_inst_2563_, lean_object* v_inst_2564_, lean_object* v_val_2565_, uint8_t v_canonical_2566_){
_start:
{
lean_object* v_toApplicative_2567_; lean_object* v_toBind_2568_; lean_object* v_getRef_2569_; lean_object* v_toPure_2570_; lean_object* v___x_2571_; lean_object* v___f_2572_; lean_object* v___x_2573_; 
v_toApplicative_2567_ = lean_ctor_get(v_inst_2563_, 0);
lean_inc_ref(v_toApplicative_2567_);
v_toBind_2568_ = lean_ctor_get(v_inst_2563_, 1);
lean_inc(v_toBind_2568_);
lean_dec_ref(v_inst_2563_);
v_getRef_2569_ = lean_ctor_get(v_inst_2564_, 0);
lean_inc(v_getRef_2569_);
lean_dec_ref(v_inst_2564_);
v_toPure_2570_ = lean_ctor_get(v_toApplicative_2567_, 1);
lean_inc(v_toPure_2570_);
lean_dec_ref(v_toApplicative_2567_);
v___x_2571_ = lean_box(v_canonical_2566_);
v___f_2572_ = lean_alloc_closure((void*)(l_Lean_mkIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2572_, 0, v_val_2565_);
lean_closure_set(v___f_2572_, 1, v___x_2571_);
lean_closure_set(v___f_2572_, 2, v_toPure_2570_);
v___x_2573_ = lean_apply_4(v_toBind_2568_, lean_box(0), lean_box(0), v_getRef_2569_, v___f_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT void l_Lean_mkIdentFromRef___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2563_ = stack[0].m_obj;
lean_object* v_inst_2564_ = stack[1].m_obj;
lean_object* v_val_2565_ = stack[2].m_obj;
uint8_t v_canonical_2566_ = stack[3].m_num;
lean_object* v_res_2574_;
v_res_2574_ = l_Lean_mkIdentFromRef___redArg(v_inst_2563_, v_inst_2564_, v_val_2565_, v_canonical_2566_);
stack->m_obj
 = v_res_2574_;
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object* v_inst_2575_, lean_object* v_inst_2576_, lean_object* v_val_2577_, lean_object* v_canonical_2578_){
_start:
{
uint8_t v_canonical_boxed_2579_; lean_object* v_res_2580_; 
v_canonical_boxed_2579_ = lean_unbox(v_canonical_2578_);
v_res_2580_ = l_Lean_mkIdentFromRef___redArg(v_inst_2575_, v_inst_2576_, v_val_2577_, v_canonical_boxed_2579_);
return v_res_2580_;
}
}
lean_object* l_Lean_mkIdentFromRef(lean_object* v_m_2581_, lean_object* v_inst_2582_, lean_object* v_inst_2583_, lean_object* v_val_2584_, uint8_t v_canonical_2585_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_mkIdentFromRef___redArg(v_inst_2582_, v_inst_2583_, v_val_2584_, v_canonical_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT void l_Lean_mkIdentFromRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2582_ = stack[1].m_obj;
lean_object* v_inst_2583_ = stack[2].m_obj;
lean_object* v_val_2584_ = stack[3].m_obj;
uint8_t v_canonical_2585_ = stack[4].m_num;
lean_object* v_res_2587_;
v_res_2587_ = l_Lean_mkIdentFromRef(lean_box(0), v_inst_2582_, v_inst_2583_, v_val_2584_, v_canonical_2585_);
stack->m_obj
 = v_res_2587_;
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object* v_m_2588_, lean_object* v_inst_2589_, lean_object* v_inst_2590_, lean_object* v_val_2591_, lean_object* v_canonical_2592_){
_start:
{
uint8_t v_canonical_boxed_2593_; lean_object* v_res_2594_; 
v_canonical_boxed_2593_ = lean_unbox(v_canonical_2592_);
v_res_2594_ = l_Lean_mkIdentFromRef(v_m_2588_, v_inst_2589_, v_inst_2590_, v_val_2591_, v_canonical_boxed_2593_);
return v_res_2594_;
}
}
lean_object* l_Lean_mkCIdentFrom(lean_object* v_src_2598_, lean_object* v_c_2599_, uint8_t v_canonical_2600_){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v_id_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2601_ = ((lean_object*)(l_Lean_mkCIdentFrom___closed__1));
v___x_2602_ = lean_unsigned_to_nat(0u);
lean_inc(v_c_2599_);
v_id_2603_ = l_Lean_addMacroScope(v___x_2601_, v_c_2599_, v___x_2602_);
v___x_2604_ = l_Lean_SourceInfo_fromRef(v_src_2598_, v_canonical_2600_);
v___x_2605_ = 1;
lean_inc(v_id_2603_);
v___x_2606_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_id_2603_, v___x_2605_);
v___x_2607_ = lean_string_utf8_byte_size(v___x_2606_);
v___x_2608_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2606_);
lean_ctor_set(v___x_2608_, 1, v___x_2602_);
lean_ctor_set(v___x_2608_, 2, v___x_2607_);
v___x_2609_ = lean_box(0);
v___x_2610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2610_, 0, v_c_2599_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
lean_ctor_set(v___x_2611_, 1, v___x_2609_);
v___x_2612_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2604_);
lean_ctor_set(v___x_2612_, 1, v___x_2608_);
lean_ctor_set(v___x_2612_, 2, v_id_2603_);
lean_ctor_set(v___x_2612_, 3, v___x_2611_);
return v___x_2612_;
}
}
LEAN_EXPORT void l_Lean_mkCIdentFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_2598_ = stack[0].m_obj;
lean_object* v_c_2599_ = stack[1].m_obj;
uint8_t v_canonical_2600_ = stack[2].m_num;
lean_object* v_res_2613_;
v_res_2613_ = l_Lean_mkCIdentFrom(v_src_2598_, v_c_2599_, v_canonical_2600_);
stack->m_obj
 = v_res_2613_;
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* v_src_2614_, lean_object* v_c_2615_, lean_object* v_canonical_2616_){
_start:
{
uint8_t v_canonical_boxed_2617_; lean_object* v_res_2618_; 
v_canonical_boxed_2617_ = lean_unbox(v_canonical_2616_);
v_res_2618_ = l_Lean_mkCIdentFrom(v_src_2614_, v_c_2615_, v_canonical_boxed_2617_);
lean_dec(v_src_2614_);
return v_res_2618_;
}
}
lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object* v_c_2619_, uint8_t v_canonical_2620_, lean_object* v_toPure_2621_, lean_object* v_____do__lift_2622_){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = l_Lean_mkCIdentFrom(v_____do__lift_2622_, v_c_2619_, v_canonical_2620_);
v___x_2624_ = lean_apply_2(v_toPure_2621_, lean_box(0), v___x_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT void l_Lean_mkCIdentFromRef___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2619_ = stack[0].m_obj;
uint8_t v_canonical_2620_ = stack[1].m_num;
lean_object* v_toPure_2621_ = stack[2].m_obj;
lean_object* v_____do__lift_2622_ = stack[3].m_obj;
lean_object* v_res_2625_;
v_res_2625_ = l_Lean_mkCIdentFromRef___redArg___lam__0(v_c_2619_, v_canonical_2620_, v_toPure_2621_, v_____do__lift_2622_);
stack->m_obj
 = v_res_2625_;
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object* v_c_2626_, lean_object* v_canonical_2627_, lean_object* v_toPure_2628_, lean_object* v_____do__lift_2629_){
_start:
{
uint8_t v_canonical_boxed_2630_; lean_object* v_res_2631_; 
v_canonical_boxed_2630_ = lean_unbox(v_canonical_2627_);
v_res_2631_ = l_Lean_mkCIdentFromRef___redArg___lam__0(v_c_2626_, v_canonical_boxed_2630_, v_toPure_2628_, v_____do__lift_2629_);
lean_dec(v_____do__lift_2629_);
return v_res_2631_;
}
}
lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object* v_inst_2632_, lean_object* v_inst_2633_, lean_object* v_c_2634_, uint8_t v_canonical_2635_){
_start:
{
lean_object* v_toApplicative_2636_; lean_object* v_toBind_2637_; lean_object* v_getRef_2638_; lean_object* v_toPure_2639_; lean_object* v___x_2640_; lean_object* v___f_2641_; lean_object* v___x_2642_; 
v_toApplicative_2636_ = lean_ctor_get(v_inst_2632_, 0);
lean_inc_ref(v_toApplicative_2636_);
v_toBind_2637_ = lean_ctor_get(v_inst_2632_, 1);
lean_inc(v_toBind_2637_);
lean_dec_ref(v_inst_2632_);
v_getRef_2638_ = lean_ctor_get(v_inst_2633_, 0);
lean_inc(v_getRef_2638_);
lean_dec_ref(v_inst_2633_);
v_toPure_2639_ = lean_ctor_get(v_toApplicative_2636_, 1);
lean_inc(v_toPure_2639_);
lean_dec_ref(v_toApplicative_2636_);
v___x_2640_ = lean_box(v_canonical_2635_);
v___f_2641_ = lean_alloc_closure((void*)(l_Lean_mkCIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2641_, 0, v_c_2634_);
lean_closure_set(v___f_2641_, 1, v___x_2640_);
lean_closure_set(v___f_2641_, 2, v_toPure_2639_);
v___x_2642_ = lean_apply_4(v_toBind_2637_, lean_box(0), lean_box(0), v_getRef_2638_, v___f_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT void l_Lean_mkCIdentFromRef___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2632_ = stack[0].m_obj;
lean_object* v_inst_2633_ = stack[1].m_obj;
lean_object* v_c_2634_ = stack[2].m_obj;
uint8_t v_canonical_2635_ = stack[3].m_num;
lean_object* v_res_2643_;
v_res_2643_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2632_, v_inst_2633_, v_c_2634_, v_canonical_2635_);
stack->m_obj
 = v_res_2643_;
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object* v_inst_2644_, lean_object* v_inst_2645_, lean_object* v_c_2646_, lean_object* v_canonical_2647_){
_start:
{
uint8_t v_canonical_boxed_2648_; lean_object* v_res_2649_; 
v_canonical_boxed_2648_ = lean_unbox(v_canonical_2647_);
v_res_2649_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2644_, v_inst_2645_, v_c_2646_, v_canonical_boxed_2648_);
return v_res_2649_;
}
}
lean_object* l_Lean_mkCIdentFromRef(lean_object* v_m_2650_, lean_object* v_inst_2651_, lean_object* v_inst_2652_, lean_object* v_c_2653_, uint8_t v_canonical_2654_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2651_, v_inst_2652_, v_c_2653_, v_canonical_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT void l_Lean_mkCIdentFromRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2651_ = stack[1].m_obj;
lean_object* v_inst_2652_ = stack[2].m_obj;
lean_object* v_c_2653_ = stack[3].m_obj;
uint8_t v_canonical_2654_ = stack[4].m_num;
lean_object* v_res_2656_;
v_res_2656_ = l_Lean_mkCIdentFromRef(lean_box(0), v_inst_2651_, v_inst_2652_, v_c_2653_, v_canonical_2654_);
stack->m_obj
 = v_res_2656_;
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object* v_m_2657_, lean_object* v_inst_2658_, lean_object* v_inst_2659_, lean_object* v_c_2660_, lean_object* v_canonical_2661_){
_start:
{
uint8_t v_canonical_boxed_2662_; lean_object* v_res_2663_; 
v_canonical_boxed_2662_ = lean_unbox(v_canonical_2661_);
v_res_2663_ = l_Lean_mkCIdentFromRef(v_m_2657_, v_inst_2658_, v_inst_2659_, v_c_2660_, v_canonical_boxed_2662_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object* v_c_2664_){
_start:
{
lean_object* v___x_2665_; uint8_t v___x_2666_; lean_object* v___x_2667_; 
v___x_2665_ = lean_box(0);
v___x_2666_ = 0;
v___x_2667_ = l_Lean_mkCIdentFrom(v___x_2665_, v_c_2664_, v___x_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdent(lean_object* v_val_2668_){
_start:
{
lean_object* v___x_2669_; uint8_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2669_ = lean_box(2);
v___x_2670_ = 1;
lean_inc(v_val_2668_);
v___x_2671_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2668_, v___x_2670_);
v___x_2672_ = lean_unsigned_to_nat(0u);
v___x_2673_ = lean_string_utf8_byte_size(v___x_2671_);
v___x_2674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2671_);
lean_ctor_set(v___x_2674_, 1, v___x_2672_);
lean_ctor_set(v___x_2674_, 2, v___x_2673_);
v___x_2675_ = lean_box(0);
v___x_2676_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2669_);
lean_ctor_set(v___x_2676_, 1, v___x_2674_);
lean_ctor_set(v___x_2676_, 2, v_val_2668_);
lean_ctor_set(v___x_2676_, 3, v___x_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object* v_args_2680_){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = ((lean_object*)(l_Lean_mkGroupNode___closed__1));
v___x_2682_ = lean_box(2);
v___x_2683_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
lean_ctor_set(v___x_2683_, 1, v___x_2681_);
lean_ctor_set(v___x_2683_, 2, v_args_2680_);
return v___x_2683_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object* v_sep_2684_, lean_object* v_as_2685_, size_t v_sz_2686_, size_t v_i_2687_, lean_object* v_b_2688_){
_start:
{
uint8_t v___x_2689_; 
v___x_2689_ = lean_usize_dec_lt(v_i_2687_, v_sz_2686_);
if (v___x_2689_ == 0)
{
lean_dec(v_sep_2684_);
return v_b_2688_;
}
else
{
lean_object* v_fst_2690_; lean_object* v_snd_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2711_; 
v_fst_2690_ = lean_ctor_get(v_b_2688_, 0);
v_snd_2691_ = lean_ctor_get(v_b_2688_, 1);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_b_2688_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2693_ = v_b_2688_;
v_isShared_2694_ = v_isSharedCheck_2711_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_snd_2691_);
lean_inc(v_fst_2690_);
lean_dec(v_b_2688_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2711_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v_r_2696_; lean_object* v_i_2705_; lean_object* v_a_2706_; uint8_t v___x_2707_; 
v_i_2705_ = lean_unsigned_to_nat(0u);
v_a_2706_ = lean_array_uget_borrowed(v_as_2685_, v_i_2687_);
v___x_2707_ = lean_nat_dec_lt(v_i_2705_, v_fst_2690_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; 
lean_inc(v_a_2706_);
v___x_2708_ = lean_array_push(v_snd_2691_, v_a_2706_);
v_r_2696_ = v___x_2708_;
goto v___jp_2695_;
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_inc(v_sep_2684_);
v___x_2709_ = lean_array_push(v_snd_2691_, v_sep_2684_);
lean_inc(v_a_2706_);
v___x_2710_ = lean_array_push(v___x_2709_, v_a_2706_);
v_r_2696_ = v___x_2710_;
goto v___jp_2695_;
}
v___jp_2695_:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
v___x_2697_ = lean_unsigned_to_nat(1u);
v___x_2698_ = lean_nat_add(v_fst_2690_, v___x_2697_);
lean_dec(v_fst_2690_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 1, v_r_2696_);
lean_ctor_set(v___x_2693_, 0, v___x_2698_);
v___x_2700_ = v___x_2693_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2698_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_r_2696_);
v___x_2700_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
size_t v___x_2701_; size_t v___x_2702_; 
v___x_2701_ = ((size_t)1ULL);
v___x_2702_ = lean_usize_add(v_i_2687_, v___x_2701_);
v_i_2687_ = v___x_2702_;
v_b_2688_ = v___x_2700_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_sep_2684_ = stack[0].m_obj;
lean_object* v_as_2685_ = stack[1].m_obj;
size_t v_sz_2686_ = stack[2].m_num;
size_t v_i_2687_ = stack[3].m_num;
lean_object* v_b_2688_ = stack[4].m_obj;
lean_object* v_res_2712_;
v_res_2712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2684_, v_as_2685_, v_sz_2686_, v_i_2687_, v_b_2688_);
stack->m_obj
 = v_res_2712_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object* v_sep_2713_, lean_object* v_as_2714_, lean_object* v_sz_2715_, lean_object* v_i_2716_, lean_object* v_b_2717_){
_start:
{
size_t v_sz_boxed_2718_; size_t v_i_boxed_2719_; lean_object* v_res_2720_; 
v_sz_boxed_2718_ = lean_unbox_usize(v_sz_2715_);
lean_dec(v_sz_2715_);
v_i_boxed_2719_ = lean_unbox_usize(v_i_2716_);
lean_dec(v_i_2716_);
v_res_2720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2713_, v_as_2714_, v_sz_boxed_2718_, v_i_boxed_2719_, v_b_2717_);
lean_dec_ref(v_as_2714_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object* v_as_2726_, lean_object* v_sep_2727_){
_start:
{
lean_object* v___x_2728_; size_t v_sz_2729_; size_t v___x_2730_; lean_object* v___x_2731_; lean_object* v_snd_2732_; 
v___x_2728_ = ((lean_object*)(l_Lean_mkSepArray___closed__1));
v_sz_2729_ = lean_array_size(v_as_2726_);
v___x_2730_ = ((size_t)0ULL);
v___x_2731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2727_, v_as_2726_, v_sz_2729_, v___x_2730_, v___x_2728_);
v_snd_2732_ = lean_ctor_get(v___x_2731_, 1);
lean_inc(v_snd_2732_);
lean_dec_ref(v___x_2731_);
return v_snd_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object* v_as_2733_, lean_object* v_sep_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_mkSepArray(v_as_2733_, v_sep_2734_);
lean_dec_ref(v_as_2733_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object* v_arg_2743_){
_start:
{
if (lean_obj_tag(v_arg_2743_) == 0)
{
lean_object* v___x_2744_; 
v___x_2744_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
return v___x_2744_;
}
else
{
lean_object* v_val_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_val_2745_ = lean_ctor_get(v_arg_2743_, 0);
lean_inc(v_val_2745_);
lean_dec_ref_known(v_arg_2743_, 1);
v___x_2746_ = lean_unsigned_to_nat(1u);
v___x_2747_ = lean_mk_empty_array_with_capacity(v___x_2746_);
v___x_2748_ = lean_array_push(v___x_2747_, v_val_2745_);
v___x_2749_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2750_ = lean_box(2);
v___x_2751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
lean_ctor_set(v___x_2751_, 1, v___x_2749_);
lean_ctor_set(v___x_2751_, 2, v___x_2748_);
return v___x_2751_;
}
}
}
lean_object* l_Lean_mkHole(lean_object* v_ref_2758_, uint8_t v_canonical_2759_){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2760_ = ((lean_object*)(l_Lean_mkHole___closed__1));
v___x_2761_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_2762_ = l_Lean_mkAtomFrom(v_ref_2758_, v___x_2761_, v_canonical_2759_);
v___x_2763_ = lean_unsigned_to_nat(1u);
v___x_2764_ = lean_mk_empty_array_with_capacity(v___x_2763_);
v___x_2765_ = lean_array_push(v___x_2764_, v___x_2762_);
v___x_2766_ = lean_box(2);
v___x_2767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v___x_2760_);
lean_ctor_set(v___x_2767_, 2, v___x_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT void l_Lean_mkHole_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2758_ = stack[0].m_obj;
uint8_t v_canonical_2759_ = stack[1].m_num;
lean_object* v_res_2768_;
v_res_2768_ = l_Lean_mkHole(v_ref_2758_, v_canonical_2759_);
stack->m_obj
 = v_res_2768_;
}
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object* v_ref_2769_, lean_object* v_canonical_2770_){
_start:
{
uint8_t v_canonical_boxed_2771_; lean_object* v_res_2772_; 
v_canonical_boxed_2771_ = lean_unbox(v_canonical_2770_);
v_res_2772_ = l_Lean_mkHole(v_ref_2769_, v_canonical_boxed_2771_);
lean_dec(v_ref_2769_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object* v_a_2773_, lean_object* v_sep_2774_){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2775_ = l_Lean_mkSepArray(v_a_2773_, v_sep_2774_);
v___x_2776_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2777_ = lean_box(2);
v___x_2778_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
lean_ctor_set(v___x_2778_, 1, v___x_2776_);
lean_ctor_set(v___x_2778_, 2, v___x_2775_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object* v_a_2779_, lean_object* v_sep_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Lean_Syntax_mkSep(v_a_2779_, v_sep_2780_);
lean_dec_ref(v_a_2779_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object* v_sep_2788_, lean_object* v_elems_2789_){
_start:
{
uint8_t v___x_2790_; 
lean_inc_ref(v_sep_2788_);
v___x_2790_ = lean_string_isempty(v_sep_2788_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = l_Lean_mkAtom(v_sep_2788_);
v___x_2792_ = l_Lean_mkSepArray(v_elems_2789_, v___x_2791_);
return v___x_2792_;
}
else
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_dec_ref(v_sep_2788_);
v___x_2793_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___x_2794_ = l_Lean_mkSepArray(v_elems_2789_, v___x_2793_);
return v___x_2794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object* v_sep_2795_, lean_object* v_elems_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2795_, v_elems_2796_);
lean_dec_ref(v_elems_2796_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object* v_elems_2798_, lean_object* v_toPure_2799_, lean_object* v_sep_2800_, lean_object* v_ref_2801_){
_start:
{
lean_object* v___y_2803_; uint8_t v___x_2806_; 
lean_inc_ref(v_sep_2800_);
v___x_2806_ = lean_string_isempty(v_sep_2800_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_mkAtomFrom(v_ref_2801_, v_sep_2800_, v___x_2806_);
v___y_2803_ = v___x_2807_;
goto v___jp_2802_;
}
else
{
lean_object* v___x_2808_; 
lean_dec_ref(v_sep_2800_);
v___x_2808_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___y_2803_ = v___x_2808_;
goto v___jp_2802_;
}
v___jp_2802_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = l_Lean_mkSepArray(v_elems_2798_, v___y_2803_);
v___x_2805_ = lean_apply_2(v_toPure_2799_, lean_box(0), v___x_2804_);
return v___x_2805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object* v_elems_2809_, lean_object* v_toPure_2810_, lean_object* v_sep_2811_, lean_object* v_ref_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(v_elems_2809_, v_toPure_2810_, v_sep_2811_, v_ref_2812_);
lean_dec(v_ref_2812_);
lean_dec_ref(v_elems_2809_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object* v_inst_2814_, lean_object* v_inst_2815_, lean_object* v_sep_2816_, lean_object* v_elems_2817_){
_start:
{
lean_object* v_toApplicative_2818_; lean_object* v_toBind_2819_; lean_object* v_getRef_2820_; lean_object* v_toPure_2821_; lean_object* v___f_2822_; lean_object* v___x_2823_; 
v_toApplicative_2818_ = lean_ctor_get(v_inst_2814_, 0);
lean_inc_ref(v_toApplicative_2818_);
v_toBind_2819_ = lean_ctor_get(v_inst_2814_, 1);
lean_inc(v_toBind_2819_);
lean_dec_ref(v_inst_2814_);
v_getRef_2820_ = lean_ctor_get(v_inst_2815_, 0);
lean_inc(v_getRef_2820_);
lean_dec_ref(v_inst_2815_);
v_toPure_2821_ = lean_ctor_get(v_toApplicative_2818_, 1);
lean_inc(v_toPure_2821_);
lean_dec_ref(v_toApplicative_2818_);
v___f_2822_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2822_, 0, v_elems_2817_);
lean_closure_set(v___f_2822_, 1, v_toPure_2821_);
lean_closure_set(v___f_2822_, 2, v_sep_2816_);
v___x_2823_ = lean_apply_4(v_toBind_2819_, lean_box(0), lean_box(0), v_getRef_2820_, v___f_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object* v_m_2824_, lean_object* v_inst_2825_, lean_object* v_inst_2826_, lean_object* v_sep_2827_, lean_object* v_elems_2828_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(v_inst_2825_, v_inst_2826_, v_sep_2827_, v_elems_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* v_sep_2830_, lean_object* v_elems_2831_){
_start:
{
lean_object* v___x_2832_; 
v___x_2832_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2830_, v_elems_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* v_sep_2833_, lean_object* v_elems_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_Syntax_TSepArray_ofElems___redArg(v_sep_2833_, v_elems_2834_);
lean_dec_ref(v_elems_2834_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* v_k_2836_, lean_object* v_sep_2837_, lean_object* v_elems_2838_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2837_, v_elems_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* v_k_2840_, lean_object* v_sep_2841_, lean_object* v_elems_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_Syntax_TSepArray_ofElems(v_k_2840_, v_sep_2841_, v_elems_2842_);
lean_dec_ref(v_elems_2842_);
lean_dec(v_k_2840_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* v_k_2844_, lean_object* v_sep_2845_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(v___x_2846_, 0, v_k_2844_);
lean_closure_set(v___x_2846_, 1, v_sep_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* v_fn_2853_, lean_object* v_x_2854_){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; 
v___x_2855_ = lean_array_get_size(v_x_2854_);
v___x_2856_ = lean_unsigned_to_nat(0u);
v___x_2857_ = lean_nat_dec_eq(v___x_2855_, v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2858_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_2859_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2860_ = lean_box(2);
v___x_2861_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
lean_ctor_set(v___x_2861_, 1, v___x_2859_);
lean_ctor_set(v___x_2861_, 2, v_x_2854_);
v___x_2862_ = lean_unsigned_to_nat(2u);
v___x_2863_ = lean_mk_empty_array_with_capacity(v___x_2862_);
v___x_2864_ = lean_array_push(v___x_2863_, v_fn_2853_);
v___x_2865_ = lean_array_push(v___x_2864_, v___x_2861_);
v___x_2866_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2860_);
lean_ctor_set(v___x_2866_, 1, v___x_2858_);
lean_ctor_set(v___x_2866_, 2, v___x_2865_);
return v___x_2866_;
}
else
{
lean_dec_ref(v_x_2854_);
return v_fn_2853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* v_fn_2867_, lean_object* v_args_2868_){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = l_Lean_mkCIdent(v_fn_2867_);
v___x_2870_ = l_Lean_Syntax_mkApp(v___x_2869_, v_args_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* v_kind_2871_, lean_object* v_val_2872_, lean_object* v_info_2873_){
_start:
{
lean_object* v_atom_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_atom_2874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2874_, 0, v_info_2873_);
lean_ctor_set(v_atom_2874_, 1, v_val_2872_);
v___x_2875_ = lean_unsigned_to_nat(1u);
v___x_2876_ = lean_mk_empty_array_with_capacity(v___x_2875_);
v___x_2877_ = lean_array_push(v___x_2876_, v_atom_2874_);
v___x_2878_ = lean_box(2);
v___x_2879_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
lean_ctor_set(v___x_2879_, 1, v_kind_2871_);
lean_ctor_set(v___x_2879_, 2, v___x_2877_);
return v___x_2879_;
}
}
lean_object* l_Lean_Syntax_mkCharLit(uint32_t v_val_2883_, lean_object* v_info_2884_){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2885_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_2886_ = l_Char_quote(v_val_2883_);
v___x_2887_ = l_Lean_Syntax_mkLit(v___x_2885_, v___x_2886_, v_info_2884_);
return v___x_2887_;
}
}
LEAN_EXPORT void l_Lean_Syntax_mkCharLit_0interp(lean_interpreter_value* stack)
{
uint32_t v_val_2883_ = stack[0].m_num;
lean_object* v_info_2884_ = stack[1].m_obj;
lean_object* v_res_2888_;
v_res_2888_ = l_Lean_Syntax_mkCharLit(v_val_2883_, v_info_2884_);
stack->m_obj
 = v_res_2888_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* v_val_2889_, lean_object* v_info_2890_){
_start:
{
uint32_t v_val_boxed_2891_; lean_object* v_res_2892_; 
v_val_boxed_2891_ = lean_unbox_uint32(v_val_2889_);
lean_dec(v_val_2889_);
v_res_2892_ = l_Lean_Syntax_mkCharLit(v_val_boxed_2891_, v_info_2890_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* v_val_2896_, lean_object* v_info_2897_){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2898_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_2899_ = l_String_quote(v_val_2896_);
v___x_2900_ = l_Lean_Syntax_mkLit(v___x_2898_, v___x_2899_, v_info_2897_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* v_val_2904_, lean_object* v_info_2905_){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2907_ = l_Lean_Syntax_mkLit(v___x_2906_, v_val_2904_, v_info_2905_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* v_val_2908_, lean_object* v_info_2909_){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2910_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2911_ = l_Nat_reprFast(v_val_2908_);
v___x_2912_ = l_Lean_Syntax_mkLit(v___x_2910_, v___x_2911_, v_info_2909_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* v_val_2916_, lean_object* v_info_2917_){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_2919_ = l_Lean_Syntax_mkLit(v___x_2918_, v_val_2916_, v_info_2917_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* v_val_2923_, lean_object* v_info_2924_){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_2926_ = l_Lean_Syntax_mkLit(v___x_2925_, v_val_2923_, v_info_2924_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* v_s_2927_, lean_object* v_i_2928_, lean_object* v_val_2929_){
_start:
{
uint8_t v___x_2930_; 
v___x_2930_ = lean_string_utf8_at_end(v_s_2927_, v_i_2928_);
if (v___x_2930_ == 0)
{
uint32_t v_c_2931_; uint32_t v___x_2932_; uint8_t v___x_2933_; 
v_c_2931_ = lean_string_utf8_get(v_s_2927_, v_i_2928_);
v___x_2932_ = 48;
v___x_2933_ = lean_uint32_dec_eq(v_c_2931_, v___x_2932_);
if (v___x_2933_ == 0)
{
uint32_t v___x_2934_; uint8_t v___x_2935_; 
v___x_2934_ = 49;
v___x_2935_ = lean_uint32_dec_eq(v_c_2931_, v___x_2934_);
if (v___x_2935_ == 0)
{
uint32_t v___x_2936_; uint8_t v___x_2937_; 
v___x_2936_ = 95;
v___x_2937_ = lean_uint32_dec_eq(v_c_2931_, v___x_2936_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; 
lean_dec(v_val_2929_);
lean_dec(v_i_2928_);
v___x_2938_ = lean_box(0);
return v___x_2938_;
}
else
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_string_utf8_next(v_s_2927_, v_i_2928_);
lean_dec(v_i_2928_);
v_i_2928_ = v___x_2939_;
goto _start;
}
}
else
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2941_ = lean_string_utf8_next(v_s_2927_, v_i_2928_);
lean_dec(v_i_2928_);
v___x_2942_ = lean_unsigned_to_nat(2u);
v___x_2943_ = lean_nat_mul(v___x_2942_, v_val_2929_);
lean_dec(v_val_2929_);
v___x_2944_ = lean_unsigned_to_nat(1u);
v___x_2945_ = lean_nat_add(v___x_2943_, v___x_2944_);
lean_dec(v___x_2943_);
v_i_2928_ = v___x_2941_;
v_val_2929_ = v___x_2945_;
goto _start;
}
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = lean_string_utf8_next(v_s_2927_, v_i_2928_);
lean_dec(v_i_2928_);
v___x_2948_ = lean_unsigned_to_nat(2u);
v___x_2949_ = lean_nat_mul(v___x_2948_, v_val_2929_);
lean_dec(v_val_2929_);
v_i_2928_ = v___x_2947_;
v_val_2929_ = v___x_2949_;
goto _start;
}
}
else
{
lean_object* v___x_2951_; 
lean_dec(v_i_2928_);
v___x_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2951_, 0, v_val_2929_);
return v___x_2951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* v_s_2952_, lean_object* v_i_2953_, lean_object* v_val_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2952_, v_i_2953_, v_val_2954_);
lean_dec_ref(v_s_2952_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* v_s_2956_, lean_object* v_i_2957_, lean_object* v_val_2958_){
_start:
{
uint8_t v___x_2959_; 
v___x_2959_ = lean_string_utf8_at_end(v_s_2956_, v_i_2957_);
if (v___x_2959_ == 0)
{
uint32_t v_c_2960_; uint8_t v___y_2962_; uint32_t v___x_2976_; uint8_t v___x_2977_; 
v_c_2960_ = lean_string_utf8_get(v_s_2956_, v_i_2957_);
v___x_2976_ = 48;
v___x_2977_ = lean_uint32_dec_le(v___x_2976_, v_c_2960_);
if (v___x_2977_ == 0)
{
v___y_2962_ = v___x_2959_;
goto v___jp_2961_;
}
else
{
uint32_t v___x_2978_; uint8_t v___x_2979_; 
v___x_2978_ = 55;
v___x_2979_ = lean_uint32_dec_le(v_c_2960_, v___x_2978_);
v___y_2962_ = v___x_2979_;
goto v___jp_2961_;
}
v___jp_2961_:
{
if (v___y_2962_ == 0)
{
uint32_t v___x_2963_; uint8_t v___x_2964_; 
v___x_2963_ = 95;
v___x_2964_ = lean_uint32_dec_eq(v_c_2960_, v___x_2963_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; 
lean_dec(v_val_2958_);
lean_dec(v_i_2957_);
v___x_2965_ = lean_box(0);
return v___x_2965_;
}
else
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_string_utf8_next(v_s_2956_, v_i_2957_);
lean_dec(v_i_2957_);
v_i_2957_ = v___x_2966_;
goto _start;
}
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2968_ = lean_string_utf8_next(v_s_2956_, v_i_2957_);
lean_dec(v_i_2957_);
v___x_2969_ = lean_unsigned_to_nat(8u);
v___x_2970_ = lean_nat_mul(v___x_2969_, v_val_2958_);
lean_dec(v_val_2958_);
v___x_2971_ = lean_uint32_to_nat(v_c_2960_);
v___x_2972_ = lean_nat_add(v___x_2970_, v___x_2971_);
lean_dec(v___x_2971_);
lean_dec(v___x_2970_);
v___x_2973_ = lean_unsigned_to_nat(48u);
v___x_2974_ = lean_nat_sub(v___x_2972_, v___x_2973_);
lean_dec(v___x_2972_);
v_i_2957_ = v___x_2968_;
v_val_2958_ = v___x_2974_;
goto _start;
}
}
}
else
{
lean_object* v___x_2980_; 
lean_dec(v_i_2957_);
v___x_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_val_2958_);
return v___x_2980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* v_s_2981_, lean_object* v_i_2982_, lean_object* v_val_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2981_, v_i_2982_, v_val_2983_);
lean_dec_ref(v_s_2981_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object* v_s_2985_, lean_object* v_i_2986_){
_start:
{
uint32_t v_c_2987_; lean_object* v_i_2988_; uint32_t v___x_3015_; uint8_t v___x_3016_; 
v_c_2987_ = lean_string_utf8_get(v_s_2985_, v_i_2986_);
v_i_2988_ = lean_string_utf8_next(v_s_2985_, v_i_2986_);
v___x_3015_ = 48;
v___x_3016_ = lean_uint32_dec_le(v___x_3015_, v_c_2987_);
if (v___x_3016_ == 0)
{
goto v___jp_3003_;
}
else
{
uint32_t v___x_3017_; uint8_t v___x_3018_; 
v___x_3017_ = 57;
v___x_3018_ = lean_uint32_dec_le(v_c_2987_, v___x_3017_);
if (v___x_3018_ == 0)
{
goto v___jp_3003_;
}
else
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3019_ = lean_uint32_to_nat(v_c_2987_);
v___x_3020_ = lean_unsigned_to_nat(48u);
v___x_3021_ = lean_nat_sub(v___x_3019_, v___x_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
lean_ctor_set(v___x_3022_, 1, v_i_2988_);
v___x_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
return v___x_3023_;
}
}
v___jp_2989_:
{
uint32_t v___x_2990_; uint8_t v___x_2991_; 
v___x_2990_ = 65;
v___x_2991_ = lean_uint32_dec_le(v___x_2990_, v_c_2987_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; 
lean_dec(v_i_2988_);
v___x_2992_ = lean_box(0);
return v___x_2992_;
}
else
{
uint32_t v___x_2993_; uint8_t v___x_2994_; 
v___x_2993_ = 70;
v___x_2994_ = lean_uint32_dec_le(v_c_2987_, v___x_2993_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; 
lean_dec(v_i_2988_);
v___x_2995_ = lean_box(0);
return v___x_2995_;
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2996_ = lean_unsigned_to_nat(10u);
v___x_2997_ = lean_uint32_to_nat(v_c_2987_);
v___x_2998_ = lean_nat_add(v___x_2996_, v___x_2997_);
lean_dec(v___x_2997_);
v___x_2999_ = lean_unsigned_to_nat(65u);
v___x_3000_ = lean_nat_sub(v___x_2998_, v___x_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
lean_ctor_set(v___x_3001_, 1, v_i_2988_);
v___x_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
return v___x_3002_;
}
}
}
v___jp_3003_:
{
uint32_t v___x_3004_; uint8_t v___x_3005_; 
v___x_3004_ = 97;
v___x_3005_ = lean_uint32_dec_le(v___x_3004_, v_c_2987_);
if (v___x_3005_ == 0)
{
goto v___jp_2989_;
}
else
{
uint32_t v___x_3006_; uint8_t v___x_3007_; 
v___x_3006_ = 102;
v___x_3007_ = lean_uint32_dec_le(v_c_2987_, v___x_3006_);
if (v___x_3007_ == 0)
{
goto v___jp_2989_;
}
else
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3008_ = lean_unsigned_to_nat(10u);
v___x_3009_ = lean_uint32_to_nat(v_c_2987_);
v___x_3010_ = lean_nat_add(v___x_3008_, v___x_3009_);
lean_dec(v___x_3009_);
v___x_3011_ = lean_unsigned_to_nat(97u);
v___x_3012_ = lean_nat_sub(v___x_3010_, v___x_3011_);
lean_dec(v___x_3010_);
v___x_3013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
lean_ctor_set(v___x_3013_, 1, v_i_2988_);
v___x_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
return v___x_3014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* v_s_3024_, lean_object* v_i_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3024_, v_i_3025_);
lean_dec(v_i_3025_);
lean_dec_ref(v_s_3024_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object* v_s_3027_, lean_object* v_i_3028_, lean_object* v_val_3029_){
_start:
{
uint8_t v___x_3030_; 
v___x_3030_ = lean_string_utf8_at_end(v_s_3027_, v_i_3028_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; 
v___x_3031_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3027_, v_i_3028_);
if (lean_obj_tag(v___x_3031_) == 0)
{
uint32_t v___x_3032_; uint32_t v___x_3033_; uint8_t v___x_3034_; 
v___x_3032_ = lean_string_utf8_get(v_s_3027_, v_i_3028_);
v___x_3033_ = 95;
v___x_3034_ = lean_uint32_dec_eq(v___x_3032_, v___x_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; 
lean_dec(v_val_3029_);
lean_dec(v_i_3028_);
v___x_3035_ = lean_box(0);
return v___x_3035_;
}
else
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_string_utf8_next(v_s_3027_, v_i_3028_);
lean_dec(v_i_3028_);
v_i_3028_ = v___x_3036_;
goto _start;
}
}
else
{
lean_object* v_val_3038_; lean_object* v_fst_3039_; lean_object* v_snd_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
lean_dec(v_i_3028_);
v_val_3038_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_val_3038_);
lean_dec_ref_known(v___x_3031_, 1);
v_fst_3039_ = lean_ctor_get(v_val_3038_, 0);
lean_inc(v_fst_3039_);
v_snd_3040_ = lean_ctor_get(v_val_3038_, 1);
lean_inc(v_snd_3040_);
lean_dec(v_val_3038_);
v___x_3041_ = lean_unsigned_to_nat(16u);
v___x_3042_ = lean_nat_mul(v___x_3041_, v_val_3029_);
lean_dec(v_val_3029_);
v___x_3043_ = lean_nat_add(v___x_3042_, v_fst_3039_);
lean_dec(v_fst_3039_);
lean_dec(v___x_3042_);
v_i_3028_ = v_snd_3040_;
v_val_3029_ = v___x_3043_;
goto _start;
}
}
else
{
lean_object* v___x_3045_; 
lean_dec(v_i_3028_);
v___x_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3045_, 0, v_val_3029_);
return v___x_3045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* v_s_3046_, lean_object* v_i_3047_, lean_object* v_val_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3046_, v_i_3047_, v_val_3048_);
lean_dec_ref(v_s_3046_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object* v_s_3050_, lean_object* v_i_3051_, lean_object* v_val_3052_){
_start:
{
uint8_t v___x_3053_; 
v___x_3053_ = lean_string_utf8_at_end(v_s_3050_, v_i_3051_);
if (v___x_3053_ == 0)
{
uint32_t v_c_3054_; uint8_t v___y_3056_; uint32_t v___x_3070_; uint8_t v___x_3071_; 
v_c_3054_ = lean_string_utf8_get(v_s_3050_, v_i_3051_);
v___x_3070_ = 48;
v___x_3071_ = lean_uint32_dec_le(v___x_3070_, v_c_3054_);
if (v___x_3071_ == 0)
{
v___y_3056_ = v___x_3053_;
goto v___jp_3055_;
}
else
{
uint32_t v___x_3072_; uint8_t v___x_3073_; 
v___x_3072_ = 57;
v___x_3073_ = lean_uint32_dec_le(v_c_3054_, v___x_3072_);
v___y_3056_ = v___x_3073_;
goto v___jp_3055_;
}
v___jp_3055_:
{
if (v___y_3056_ == 0)
{
uint32_t v___x_3057_; uint8_t v___x_3058_; 
v___x_3057_ = 95;
v___x_3058_ = lean_uint32_dec_eq(v_c_3054_, v___x_3057_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; 
lean_dec(v_val_3052_);
lean_dec(v_i_3051_);
v___x_3059_ = lean_box(0);
return v___x_3059_;
}
else
{
lean_object* v___x_3060_; 
v___x_3060_ = lean_string_utf8_next(v_s_3050_, v_i_3051_);
lean_dec(v_i_3051_);
v_i_3051_ = v___x_3060_;
goto _start;
}
}
else
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3062_ = lean_string_utf8_next(v_s_3050_, v_i_3051_);
lean_dec(v_i_3051_);
v___x_3063_ = lean_unsigned_to_nat(10u);
v___x_3064_ = lean_nat_mul(v___x_3063_, v_val_3052_);
lean_dec(v_val_3052_);
v___x_3065_ = lean_uint32_to_nat(v_c_3054_);
v___x_3066_ = lean_nat_add(v___x_3064_, v___x_3065_);
lean_dec(v___x_3065_);
lean_dec(v___x_3064_);
v___x_3067_ = lean_unsigned_to_nat(48u);
v___x_3068_ = lean_nat_sub(v___x_3066_, v___x_3067_);
lean_dec(v___x_3066_);
v_i_3051_ = v___x_3062_;
v_val_3052_ = v___x_3068_;
goto _start;
}
}
}
else
{
lean_object* v___x_3074_; 
lean_dec(v_i_3051_);
v___x_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3074_, 0, v_val_3052_);
return v___x_3074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* v_s_3075_, lean_object* v_i_3076_, lean_object* v_val_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3075_, v_i_3076_, v_val_3077_);
lean_dec_ref(v_s_3075_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* v_s_3081_){
_start:
{
lean_object* v_len_3082_; lean_object* v___x_3083_; uint8_t v___x_3093_; 
v_len_3082_ = lean_string_length(v_s_3081_);
v___x_3083_ = lean_unsigned_to_nat(0u);
v___x_3093_ = lean_nat_dec_eq(v_len_3082_, v___x_3083_);
if (v___x_3093_ == 0)
{
uint32_t v_c_3094_; uint32_t v___x_3095_; uint8_t v___x_3096_; 
v_c_3094_ = lean_string_utf8_get(v_s_3081_, v___x_3083_);
v___x_3095_ = 48;
v___x_3096_ = lean_uint32_dec_eq(v_c_3094_, v___x_3095_);
if (v___x_3096_ == 0)
{
uint8_t v___x_3097_; 
lean_dec(v_len_3082_);
v___x_3097_ = lean_uint32_dec_le(v___x_3095_, v_c_3094_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; 
v___x_3098_ = lean_box(0);
return v___x_3098_;
}
else
{
uint32_t v___x_3099_; uint8_t v___x_3100_; 
v___x_3099_ = 57;
v___x_3100_ = lean_uint32_dec_le(v_c_3094_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; 
v___x_3101_ = lean_box(0);
return v___x_3101_;
}
else
{
lean_object* v___x_3102_; 
v___x_3102_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3081_, v___x_3083_, v___x_3083_);
return v___x_3102_;
}
}
}
else
{
lean_object* v___x_3103_; uint8_t v___x_3104_; 
v___x_3103_ = lean_unsigned_to_nat(1u);
v___x_3104_ = lean_nat_dec_eq(v_len_3082_, v___x_3103_);
lean_dec(v_len_3082_);
if (v___x_3104_ == 0)
{
uint32_t v_c_3105_; uint32_t v___x_3106_; uint8_t v___x_3107_; 
v_c_3105_ = lean_string_utf8_get(v_s_3081_, v___x_3103_);
v___x_3106_ = 120;
v___x_3107_ = lean_uint32_dec_eq(v_c_3105_, v___x_3106_);
if (v___x_3107_ == 0)
{
uint32_t v___x_3108_; uint8_t v___x_3109_; 
v___x_3108_ = 88;
v___x_3109_ = lean_uint32_dec_eq(v_c_3105_, v___x_3108_);
if (v___x_3109_ == 0)
{
uint32_t v___x_3110_; uint8_t v___x_3111_; 
v___x_3110_ = 98;
v___x_3111_ = lean_uint32_dec_eq(v_c_3105_, v___x_3110_);
if (v___x_3111_ == 0)
{
uint32_t v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = 66;
v___x_3113_ = lean_uint32_dec_eq(v_c_3105_, v___x_3112_);
if (v___x_3113_ == 0)
{
uint32_t v___x_3114_; uint8_t v___x_3115_; 
v___x_3114_ = 111;
v___x_3115_ = lean_uint32_dec_eq(v_c_3105_, v___x_3114_);
if (v___x_3115_ == 0)
{
uint32_t v___x_3116_; uint8_t v___x_3117_; 
v___x_3116_ = 79;
v___x_3117_ = lean_uint32_dec_eq(v_c_3105_, v___x_3116_);
if (v___x_3117_ == 0)
{
uint8_t v___x_3118_; 
v___x_3118_ = lean_uint32_dec_le(v___x_3095_, v_c_3105_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_box(0);
return v___x_3119_;
}
else
{
uint32_t v___x_3120_; uint8_t v___x_3121_; 
v___x_3120_ = 57;
v___x_3121_ = lean_uint32_dec_le(v_c_3105_, v___x_3120_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; 
v___x_3122_ = lean_box(0);
return v___x_3122_;
}
else
{
lean_object* v___x_3123_; 
v___x_3123_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3081_, v___x_3083_, v___x_3083_);
return v___x_3123_;
}
}
}
else
{
goto v___jp_3084_;
}
}
else
{
goto v___jp_3084_;
}
}
else
{
goto v___jp_3087_;
}
}
else
{
goto v___jp_3087_;
}
}
else
{
goto v___jp_3090_;
}
}
else
{
goto v___jp_3090_;
}
}
else
{
lean_object* v___x_3124_; 
v___x_3124_ = ((lean_object*)(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0));
return v___x_3124_;
}
}
}
else
{
lean_object* v___x_3125_; 
lean_dec(v_len_3082_);
v___x_3125_ = lean_box(0);
return v___x_3125_;
}
v___jp_3084_:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = lean_unsigned_to_nat(2u);
v___x_3086_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_3081_, v___x_3085_, v___x_3083_);
return v___x_3086_;
}
v___jp_3087_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = lean_unsigned_to_nat(2u);
v___x_3089_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_3081_, v___x_3088_, v___x_3083_);
return v___x_3089_;
}
v___jp_3090_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = lean_unsigned_to_nat(2u);
v___x_3092_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3081_, v___x_3091_, v___x_3083_);
return v___x_3092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* v_s_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_s_3126_);
lean_dec_ref(v_s_3126_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* v_litKind_3128_, lean_object* v_stx_3129_){
_start:
{
if (lean_obj_tag(v_stx_3129_) == 1)
{
lean_object* v_kind_3130_; lean_object* v_args_3131_; uint8_t v___y_3133_; uint8_t v___x_3140_; 
v_kind_3130_ = lean_ctor_get(v_stx_3129_, 1);
v_args_3131_ = lean_ctor_get(v_stx_3129_, 2);
v___x_3140_ = lean_name_eq(v_kind_3130_, v_litKind_3128_);
if (v___x_3140_ == 0)
{
v___y_3133_ = v___x_3140_;
goto v___jp_3132_;
}
else
{
lean_object* v___x_3141_; lean_object* v___x_3142_; uint8_t v___x_3143_; 
v___x_3141_ = lean_array_get_size(v_args_3131_);
v___x_3142_ = lean_unsigned_to_nat(1u);
v___x_3143_ = lean_nat_dec_eq(v___x_3141_, v___x_3142_);
v___y_3133_ = v___x_3143_;
goto v___jp_3132_;
}
v___jp_3132_:
{
if (v___y_3133_ == 0)
{
lean_object* v___x_3134_; 
v___x_3134_ = lean_box(0);
return v___x_3134_;
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = lean_unsigned_to_nat(0u);
v___x_3136_ = lean_array_fget_borrowed(v_args_3131_, v___x_3135_);
if (lean_obj_tag(v___x_3136_) == 2)
{
lean_object* v_val_3137_; lean_object* v___x_3138_; 
v_val_3137_ = lean_ctor_get(v___x_3136_, 1);
lean_inc_ref(v_val_3137_);
v___x_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3138_, 0, v_val_3137_);
return v___x_3138_;
}
else
{
lean_object* v___x_3139_; 
v___x_3139_ = lean_box(0);
return v___x_3139_;
}
}
}
}
else
{
lean_object* v___x_3144_; 
v___x_3144_ = lean_box(0);
return v___x_3144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* v_litKind_3145_, lean_object* v_stx_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l_Lean_Syntax_isLit_x3f(v_litKind_3145_, v_stx_3146_);
lean_dec(v_stx_3146_);
lean_dec(v_litKind_3145_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object* v_litKind_3148_, lean_object* v_stx_3149_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Lean_Syntax_isLit_x3f(v_litKind_3148_, v_stx_3149_);
if (lean_obj_tag(v___x_3150_) == 1)
{
lean_object* v_val_3151_; lean_object* v___x_3152_; 
v_val_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_val_3151_);
lean_dec_ref_known(v___x_3150_, 1);
v___x_3152_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_val_3151_);
lean_dec(v_val_3151_);
return v___x_3152_;
}
else
{
lean_object* v___x_3153_; 
lean_dec(v___x_3150_);
v___x_3153_ = lean_box(0);
return v___x_3153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object* v_litKind_3154_, lean_object* v_stx_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v_litKind_3154_, v_stx_3155_);
lean_dec(v_stx_3155_);
lean_dec(v_litKind_3154_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* v_s_3157_){
_start:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_3159_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3158_, v_s_3157_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* v_s_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_Syntax_isNatLit_x3f(v_s_3160_);
lean_dec(v_s_3160_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* v_s_3165_){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = ((lean_object*)(l_Lean_Syntax_isFieldIdx_x3f___closed__1));
v___x_3167_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3166_, v_s_3165_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* v_s_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Lean_Syntax_isFieldIdx_x3f(v_s_3168_);
lean_dec(v_s_3168_);
return v_res_3169_;
}
}
lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* v_s_3170_, lean_object* v_i_3171_, lean_object* v_val_3172_, lean_object* v_e_3173_, uint8_t v_sign_3174_, lean_object* v_exp_3175_){
_start:
{
uint8_t v___x_3176_; 
v___x_3176_ = lean_string_utf8_at_end(v_s_3170_, v_i_3171_);
if (v___x_3176_ == 0)
{
uint32_t v_c_3177_; uint8_t v___y_3179_; uint32_t v___x_3193_; uint8_t v___x_3194_; 
v_c_3177_ = lean_string_utf8_get(v_s_3170_, v_i_3171_);
v___x_3193_ = 48;
v___x_3194_ = lean_uint32_dec_le(v___x_3193_, v_c_3177_);
if (v___x_3194_ == 0)
{
v___y_3179_ = v___x_3176_;
goto v___jp_3178_;
}
else
{
uint32_t v___x_3195_; uint8_t v___x_3196_; 
v___x_3195_ = 57;
v___x_3196_ = lean_uint32_dec_le(v_c_3177_, v___x_3195_);
v___y_3179_ = v___x_3196_;
goto v___jp_3178_;
}
v___jp_3178_:
{
if (v___y_3179_ == 0)
{
uint32_t v___x_3180_; uint8_t v___x_3181_; 
v___x_3180_ = 95;
v___x_3181_ = lean_uint32_dec_eq(v_c_3177_, v___x_3180_);
if (v___x_3181_ == 0)
{
lean_object* v___x_3182_; 
lean_dec(v_exp_3175_);
lean_dec(v_val_3172_);
lean_dec(v_i_3171_);
v___x_3182_ = lean_box(0);
return v___x_3182_;
}
else
{
lean_object* v___x_3183_; 
v___x_3183_ = lean_string_utf8_next(v_s_3170_, v_i_3171_);
lean_dec(v_i_3171_);
v_i_3171_ = v___x_3183_;
goto _start;
}
}
else
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3185_ = lean_string_utf8_next(v_s_3170_, v_i_3171_);
lean_dec(v_i_3171_);
v___x_3186_ = lean_unsigned_to_nat(10u);
v___x_3187_ = lean_nat_mul(v___x_3186_, v_exp_3175_);
lean_dec(v_exp_3175_);
v___x_3188_ = lean_uint32_to_nat(v_c_3177_);
v___x_3189_ = lean_nat_add(v___x_3187_, v___x_3188_);
lean_dec(v___x_3188_);
lean_dec(v___x_3187_);
v___x_3190_ = lean_unsigned_to_nat(48u);
v___x_3191_ = lean_nat_sub(v___x_3189_, v___x_3190_);
lean_dec(v___x_3189_);
v_i_3171_ = v___x_3185_;
v_exp_3175_ = v___x_3191_;
goto _start;
}
}
}
else
{
lean_dec(v_i_3171_);
if (v_sign_3174_ == 0)
{
uint8_t v___x_3197_; 
v___x_3197_ = lean_nat_dec_le(v_e_3173_, v_exp_3175_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3198_ = lean_nat_sub(v_e_3173_, v_exp_3175_);
lean_dec(v_exp_3175_);
v___x_3199_ = lean_box(v___x_3176_);
v___x_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
lean_ctor_set(v___x_3200_, 1, v___x_3198_);
v___x_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3201_, 0, v_val_3172_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
v___x_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
return v___x_3202_;
}
else
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3203_ = lean_nat_sub(v_exp_3175_, v_e_3173_);
lean_dec(v_exp_3175_);
v___x_3204_ = lean_box(v_sign_3174_);
v___x_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
lean_ctor_set(v___x_3205_, 1, v___x_3203_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_val_3172_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
return v___x_3207_;
}
}
else
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3208_ = lean_nat_add(v_exp_3175_, v_e_3173_);
lean_dec(v_exp_3175_);
v___x_3209_ = lean_box(v_sign_3174_);
v___x_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
lean_ctor_set(v___x_3210_, 1, v___x_3208_);
v___x_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3211_, 0, v_val_3172_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
return v___x_3212_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3170_ = stack[0].m_obj;
lean_object* v_i_3171_ = stack[1].m_obj;
lean_object* v_val_3172_ = stack[2].m_obj;
lean_object* v_e_3173_ = stack[3].m_obj;
uint8_t v_sign_3174_ = stack[4].m_num;
lean_object* v_exp_3175_ = stack[5].m_obj;
lean_object* v_res_3213_;
v_res_3213_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3170_, v_i_3171_, v_val_3172_, v_e_3173_, v_sign_3174_, v_exp_3175_);
stack->m_obj
 = v_res_3213_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* v_s_3214_, lean_object* v_i_3215_, lean_object* v_val_3216_, lean_object* v_e_3217_, lean_object* v_sign_3218_, lean_object* v_exp_3219_){
_start:
{
uint8_t v_sign_boxed_3220_; lean_object* v_res_3221_; 
v_sign_boxed_3220_ = lean_unbox(v_sign_3218_);
v_res_3221_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3214_, v_i_3215_, v_val_3216_, v_e_3217_, v_sign_boxed_3220_, v_exp_3219_);
lean_dec(v_e_3217_);
lean_dec_ref(v_s_3214_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* v_s_3222_, lean_object* v_i_3223_, lean_object* v_val_3224_, lean_object* v_e_3225_){
_start:
{
uint8_t v___x_3226_; 
v___x_3226_ = lean_string_utf8_at_end(v_s_3222_, v_i_3223_);
if (v___x_3226_ == 0)
{
uint32_t v_c_3227_; uint32_t v___x_3228_; uint8_t v___x_3229_; 
v_c_3227_ = lean_string_utf8_get(v_s_3222_, v_i_3223_);
v___x_3228_ = 45;
v___x_3229_ = lean_uint32_dec_eq(v_c_3227_, v___x_3228_);
if (v___x_3229_ == 0)
{
uint32_t v___x_3230_; uint8_t v___x_3231_; 
v___x_3230_ = 43;
v___x_3231_ = lean_uint32_dec_eq(v_c_3227_, v___x_3230_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3232_ = lean_unsigned_to_nat(0u);
v___x_3233_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3222_, v_i_3223_, v_val_3224_, v_e_3225_, v___x_3231_, v___x_3232_);
return v___x_3233_;
}
else
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3234_ = lean_string_utf8_next(v_s_3222_, v_i_3223_);
lean_dec(v_i_3223_);
v___x_3235_ = lean_unsigned_to_nat(0u);
v___x_3236_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3222_, v___x_3234_, v_val_3224_, v_e_3225_, v___x_3229_, v___x_3235_);
return v___x_3236_;
}
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = lean_string_utf8_next(v_s_3222_, v_i_3223_);
lean_dec(v_i_3223_);
v___x_3238_ = lean_unsigned_to_nat(0u);
v___x_3239_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3222_, v___x_3237_, v_val_3224_, v_e_3225_, v___x_3229_, v___x_3238_);
return v___x_3239_;
}
}
else
{
lean_object* v___x_3240_; 
lean_dec(v_val_3224_);
lean_dec(v_i_3223_);
v___x_3240_ = lean_box(0);
return v___x_3240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* v_s_3241_, lean_object* v_i_3242_, lean_object* v_val_3243_, lean_object* v_e_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3241_, v_i_3242_, v_val_3243_, v_e_3244_);
lean_dec(v_e_3244_);
lean_dec_ref(v_s_3241_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* v_s_3246_, lean_object* v_i_3247_, lean_object* v_val_3248_, lean_object* v_e_3249_){
_start:
{
uint8_t v___x_3253_; 
v___x_3253_ = lean_string_utf8_at_end(v_s_3246_, v_i_3247_);
if (v___x_3253_ == 0)
{
uint32_t v_c_3254_; uint8_t v___y_3256_; uint32_t v___x_3276_; uint8_t v___x_3277_; 
v_c_3254_ = lean_string_utf8_get(v_s_3246_, v_i_3247_);
v___x_3276_ = 48;
v___x_3277_ = lean_uint32_dec_le(v___x_3276_, v_c_3254_);
if (v___x_3277_ == 0)
{
v___y_3256_ = v___x_3253_;
goto v___jp_3255_;
}
else
{
uint32_t v___x_3278_; uint8_t v___x_3279_; 
v___x_3278_ = 57;
v___x_3279_ = lean_uint32_dec_le(v_c_3254_, v___x_3278_);
v___y_3256_ = v___x_3279_;
goto v___jp_3255_;
}
v___jp_3255_:
{
if (v___y_3256_ == 0)
{
uint32_t v___x_3257_; uint8_t v___x_3258_; 
v___x_3257_ = 95;
v___x_3258_ = lean_uint32_dec_eq(v_c_3254_, v___x_3257_);
if (v___x_3258_ == 0)
{
uint32_t v___x_3259_; uint8_t v___x_3260_; 
v___x_3259_ = 101;
v___x_3260_ = lean_uint32_dec_eq(v_c_3254_, v___x_3259_);
if (v___x_3260_ == 0)
{
uint32_t v___x_3261_; uint8_t v___x_3262_; 
v___x_3261_ = 69;
v___x_3262_ = lean_uint32_dec_eq(v_c_3254_, v___x_3261_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3263_; 
lean_dec(v_e_3249_);
lean_dec(v_val_3248_);
lean_dec(v_i_3247_);
v___x_3263_ = lean_box(0);
return v___x_3263_;
}
else
{
goto v___jp_3250_;
}
}
else
{
goto v___jp_3250_;
}
}
else
{
lean_object* v___x_3264_; 
v___x_3264_ = lean_string_utf8_next(v_s_3246_, v_i_3247_);
lean_dec(v_i_3247_);
v_i_3247_ = v___x_3264_;
goto _start;
}
}
else
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3266_ = lean_string_utf8_next(v_s_3246_, v_i_3247_);
lean_dec(v_i_3247_);
v___x_3267_ = lean_unsigned_to_nat(10u);
v___x_3268_ = lean_nat_mul(v___x_3267_, v_val_3248_);
lean_dec(v_val_3248_);
v___x_3269_ = lean_uint32_to_nat(v_c_3254_);
v___x_3270_ = lean_nat_add(v___x_3268_, v___x_3269_);
lean_dec(v___x_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_unsigned_to_nat(48u);
v___x_3272_ = lean_nat_sub(v___x_3270_, v___x_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_unsigned_to_nat(1u);
v___x_3274_ = lean_nat_add(v_e_3249_, v___x_3273_);
lean_dec(v_e_3249_);
v_i_3247_ = v___x_3266_;
v_val_3248_ = v___x_3272_;
v_e_3249_ = v___x_3274_;
goto _start;
}
}
}
else
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
lean_dec(v_i_3247_);
v___x_3280_ = lean_box(v___x_3253_);
v___x_3281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
lean_ctor_set(v___x_3281_, 1, v_e_3249_);
v___x_3282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3282_, 0, v_val_3248_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
v___x_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
return v___x_3283_;
}
v___jp_3250_:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = lean_string_utf8_next(v_s_3246_, v_i_3247_);
lean_dec(v_i_3247_);
v___x_3252_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3246_, v___x_3251_, v_val_3248_, v_e_3249_);
lean_dec(v_e_3249_);
return v___x_3252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* v_s_3284_, lean_object* v_i_3285_, lean_object* v_val_3286_, lean_object* v_e_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3284_, v_i_3285_, v_val_3286_, v_e_3287_);
lean_dec_ref(v_s_3284_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* v_s_3289_, lean_object* v_i_3290_, lean_object* v_val_3291_){
_start:
{
uint8_t v___x_3296_; 
v___x_3296_ = lean_string_utf8_at_end(v_s_3289_, v_i_3290_);
if (v___x_3296_ == 0)
{
uint32_t v_c_3297_; uint8_t v___y_3299_; uint32_t v___x_3322_; uint8_t v___x_3323_; 
v_c_3297_ = lean_string_utf8_get(v_s_3289_, v_i_3290_);
v___x_3322_ = 48;
v___x_3323_ = lean_uint32_dec_le(v___x_3322_, v_c_3297_);
if (v___x_3323_ == 0)
{
v___y_3299_ = v___x_3296_;
goto v___jp_3298_;
}
else
{
uint32_t v___x_3324_; uint8_t v___x_3325_; 
v___x_3324_ = 57;
v___x_3325_ = lean_uint32_dec_le(v_c_3297_, v___x_3324_);
v___y_3299_ = v___x_3325_;
goto v___jp_3298_;
}
v___jp_3298_:
{
if (v___y_3299_ == 0)
{
uint32_t v___x_3300_; uint8_t v___x_3301_; 
v___x_3300_ = 95;
v___x_3301_ = lean_uint32_dec_eq(v_c_3297_, v___x_3300_);
if (v___x_3301_ == 0)
{
uint32_t v___x_3302_; uint8_t v___x_3303_; 
v___x_3302_ = 46;
v___x_3303_ = lean_uint32_dec_eq(v_c_3297_, v___x_3302_);
if (v___x_3303_ == 0)
{
uint32_t v___x_3304_; uint8_t v___x_3305_; 
v___x_3304_ = 101;
v___x_3305_ = lean_uint32_dec_eq(v_c_3297_, v___x_3304_);
if (v___x_3305_ == 0)
{
uint32_t v___x_3306_; uint8_t v___x_3307_; 
v___x_3306_ = 69;
v___x_3307_ = lean_uint32_dec_eq(v_c_3297_, v___x_3306_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; 
lean_dec(v_val_3291_);
lean_dec(v_i_3290_);
v___x_3308_ = lean_box(0);
return v___x_3308_;
}
else
{
goto v___jp_3292_;
}
}
else
{
goto v___jp_3292_;
}
}
else
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3309_ = lean_string_utf8_next(v_s_3289_, v_i_3290_);
lean_dec(v_i_3290_);
v___x_3310_ = lean_unsigned_to_nat(0u);
v___x_3311_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3289_, v___x_3309_, v_val_3291_, v___x_3310_);
return v___x_3311_;
}
}
else
{
lean_object* v___x_3312_; 
v___x_3312_ = lean_string_utf8_next(v_s_3289_, v_i_3290_);
lean_dec(v_i_3290_);
v_i_3290_ = v___x_3312_;
goto _start;
}
}
else
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3314_ = lean_string_utf8_next(v_s_3289_, v_i_3290_);
lean_dec(v_i_3290_);
v___x_3315_ = lean_unsigned_to_nat(10u);
v___x_3316_ = lean_nat_mul(v___x_3315_, v_val_3291_);
lean_dec(v_val_3291_);
v___x_3317_ = lean_uint32_to_nat(v_c_3297_);
v___x_3318_ = lean_nat_add(v___x_3316_, v___x_3317_);
lean_dec(v___x_3317_);
lean_dec(v___x_3316_);
v___x_3319_ = lean_unsigned_to_nat(48u);
v___x_3320_ = lean_nat_sub(v___x_3318_, v___x_3319_);
lean_dec(v___x_3318_);
v_i_3290_ = v___x_3314_;
v_val_3291_ = v___x_3320_;
goto _start;
}
}
}
else
{
lean_object* v___x_3326_; 
lean_dec(v_val_3291_);
lean_dec(v_i_3290_);
v___x_3326_ = lean_box(0);
return v___x_3326_;
}
v___jp_3292_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3293_ = lean_string_utf8_next(v_s_3289_, v_i_3290_);
lean_dec(v_i_3290_);
v___x_3294_ = lean_unsigned_to_nat(0u);
v___x_3295_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3289_, v___x_3293_, v_val_3291_, v___x_3294_);
return v___x_3295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* v_s_3327_, lean_object* v_i_3328_, lean_object* v_val_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3327_, v_i_3328_, v_val_3329_);
lean_dec_ref(v_s_3327_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* v_s_3331_){
_start:
{
lean_object* v_len_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v_len_3332_ = lean_string_length(v_s_3331_);
v___x_3333_ = lean_unsigned_to_nat(0u);
v___x_3334_ = lean_nat_dec_eq(v_len_3332_, v___x_3333_);
lean_dec(v_len_3332_);
if (v___x_3334_ == 0)
{
uint32_t v_c_3335_; uint32_t v___x_3336_; uint8_t v___x_3337_; 
v_c_3335_ = lean_string_utf8_get(v_s_3331_, v___x_3333_);
v___x_3336_ = 48;
v___x_3337_ = lean_uint32_dec_le(v___x_3336_, v_c_3335_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; 
v___x_3338_ = lean_box(0);
return v___x_3338_;
}
else
{
uint32_t v___x_3339_; uint8_t v___x_3340_; 
v___x_3339_ = 57;
v___x_3340_ = lean_uint32_dec_le(v_c_3335_, v___x_3339_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; 
v___x_3341_ = lean_box(0);
return v___x_3341_;
}
else
{
lean_object* v___x_3342_; 
v___x_3342_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3331_, v___x_3333_, v___x_3333_);
return v___x_3342_;
}
}
}
else
{
lean_object* v___x_3343_; 
v___x_3343_ = lean_box(0);
return v___x_3343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* v_s_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_s_3344_);
lean_dec_ref(v_s_3344_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* v_stx_3346_){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3347_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_3348_ = l_Lean_Syntax_isLit_x3f(v___x_3347_, v_stx_3346_);
if (lean_obj_tag(v___x_3348_) == 1)
{
lean_object* v_val_3349_; lean_object* v___x_3350_; 
v_val_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_val_3349_);
lean_dec_ref_known(v___x_3348_, 1);
v___x_3350_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_val_3349_);
lean_dec(v_val_3349_);
return v___x_3350_;
}
else
{
lean_object* v___x_3351_; 
lean_dec(v___x_3348_);
v___x_3351_ = lean_box(0);
return v___x_3351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* v_stx_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lean_Syntax_isScientificLit_x3f(v_stx_3352_);
lean_dec(v_stx_3352_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* v_x_3354_){
_start:
{
switch(lean_obj_tag(v_x_3354_))
{
case 2:
{
lean_object* v_val_3355_; lean_object* v___x_3356_; 
v_val_3355_ = lean_ctor_get(v_x_3354_, 1);
lean_inc_ref(v_val_3355_);
lean_dec_ref_known(v_x_3354_, 2);
v___x_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3356_, 0, v_val_3355_);
return v___x_3356_;
}
case 3:
{
lean_object* v_rawVal_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v_rawVal_3357_ = lean_ctor_get(v_x_3354_, 1);
lean_inc_ref(v_rawVal_3357_);
lean_dec_ref_known(v_x_3354_, 4);
v___x_3358_ = lean_substring_tostring(v_rawVal_3357_);
v___x_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
return v___x_3359_;
}
default: 
{
lean_object* v___x_3360_; 
lean_dec(v_x_3354_);
v___x_3360_ = lean_box(0);
return v___x_3360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* v_stx_3361_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_Lean_Syntax_isNatLit_x3f(v_stx_3361_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v___x_3363_; 
v___x_3363_ = lean_unsigned_to_nat(0u);
return v___x_3363_;
}
else
{
lean_object* v_val_3364_; 
v_val_3364_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_val_3364_);
lean_dec_ref_known(v___x_3362_, 1);
return v_val_3364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* v_stx_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Lean_Syntax_toNat(v_stx_3365_);
lean_dec(v_stx_3365_);
return v_res_3366_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = 9;
v___x_3368_ = lean_box_uint32(v___x_3367_);
return v___x_3368_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = 10;
v___x_3370_ = lean_box_uint32(v___x_3369_);
return v___x_3370_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = 13;
v___x_3372_ = lean_box_uint32(v___x_3371_);
return v___x_3372_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = 39;
v___x_3374_ = lean_box_uint32(v___x_3373_);
return v___x_3374_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = 34;
v___x_3376_ = lean_box_uint32(v___x_3375_);
return v___x_3376_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = 92;
v___x_3378_ = lean_box_uint32(v___x_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* v_s_3379_, lean_object* v_i_3380_){
_start:
{
uint32_t v_c_3381_; lean_object* v_i_3382_; uint32_t v___x_3383_; uint8_t v___x_3384_; 
v_c_3381_ = lean_string_utf8_get(v_s_3379_, v_i_3380_);
v_i_3382_ = lean_string_utf8_next(v_s_3379_, v_i_3380_);
v___x_3383_ = 92;
v___x_3384_ = lean_uint32_dec_eq(v_c_3381_, v___x_3383_);
if (v___x_3384_ == 0)
{
uint32_t v___x_3385_; uint8_t v___x_3386_; 
v___x_3385_ = 34;
v___x_3386_ = lean_uint32_dec_eq(v_c_3381_, v___x_3385_);
if (v___x_3386_ == 0)
{
uint32_t v___x_3387_; uint8_t v___x_3388_; 
v___x_3387_ = 39;
v___x_3388_ = lean_uint32_dec_eq(v_c_3381_, v___x_3387_);
if (v___x_3388_ == 0)
{
uint32_t v___x_3389_; uint8_t v___x_3390_; 
v___x_3389_ = 114;
v___x_3390_ = lean_uint32_dec_eq(v_c_3381_, v___x_3389_);
if (v___x_3390_ == 0)
{
uint32_t v___x_3391_; uint8_t v___x_3392_; 
v___x_3391_ = 110;
v___x_3392_ = lean_uint32_dec_eq(v_c_3381_, v___x_3391_);
if (v___x_3392_ == 0)
{
uint32_t v___x_3393_; uint8_t v___x_3394_; 
v___x_3393_ = 116;
v___x_3394_ = lean_uint32_dec_eq(v_c_3381_, v___x_3393_);
if (v___x_3394_ == 0)
{
uint32_t v___x_3395_; uint8_t v___x_3396_; 
v___x_3395_ = 120;
v___x_3396_ = lean_uint32_dec_eq(v_c_3381_, v___x_3395_);
if (v___x_3396_ == 0)
{
uint32_t v___x_3397_; uint8_t v___x_3398_; 
v___x_3397_ = 117;
v___x_3398_ = lean_uint32_dec_eq(v_c_3381_, v___x_3397_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; 
lean_dec(v_i_3382_);
v___x_3399_ = lean_box(0);
return v___x_3399_;
}
else
{
lean_object* v___x_3400_; 
v___x_3400_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3379_, v_i_3382_);
lean_dec(v_i_3382_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v___x_3401_; 
v___x_3401_ = lean_box(0);
return v___x_3401_;
}
else
{
lean_object* v_val_3402_; lean_object* v_fst_3403_; lean_object* v_snd_3404_; lean_object* v___x_3405_; 
v_val_3402_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_val_3402_);
lean_dec_ref_known(v___x_3400_, 1);
v_fst_3403_ = lean_ctor_get(v_val_3402_, 0);
lean_inc(v_fst_3403_);
v_snd_3404_ = lean_ctor_get(v_val_3402_, 1);
lean_inc(v_snd_3404_);
lean_dec(v_val_3402_);
v___x_3405_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3379_, v_snd_3404_);
lean_dec(v_snd_3404_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v___x_3406_; 
lean_dec(v_fst_3403_);
v___x_3406_ = lean_box(0);
return v___x_3406_;
}
else
{
lean_object* v_val_3407_; lean_object* v_fst_3408_; lean_object* v_snd_3409_; lean_object* v___x_3410_; 
v_val_3407_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_val_3407_);
lean_dec_ref_known(v___x_3405_, 1);
v_fst_3408_ = lean_ctor_get(v_val_3407_, 0);
lean_inc(v_fst_3408_);
v_snd_3409_ = lean_ctor_get(v_val_3407_, 1);
lean_inc(v_snd_3409_);
lean_dec(v_val_3407_);
v___x_3410_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3379_, v_snd_3409_);
lean_dec(v_snd_3409_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v___x_3411_; 
lean_dec(v_fst_3408_);
lean_dec(v_fst_3403_);
v___x_3411_ = lean_box(0);
return v___x_3411_;
}
else
{
lean_object* v_val_3412_; lean_object* v_fst_3413_; lean_object* v_snd_3414_; lean_object* v___x_3415_; 
v_val_3412_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_val_3412_);
lean_dec_ref_known(v___x_3410_, 1);
v_fst_3413_ = lean_ctor_get(v_val_3412_, 0);
lean_inc(v_fst_3413_);
v_snd_3414_ = lean_ctor_get(v_val_3412_, 1);
lean_inc(v_snd_3414_);
lean_dec(v_val_3412_);
v___x_3415_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3379_, v_snd_3414_);
lean_dec(v_snd_3414_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v___x_3416_; 
lean_dec(v_fst_3413_);
lean_dec(v_fst_3408_);
lean_dec(v_fst_3403_);
v___x_3416_ = lean_box(0);
return v___x_3416_;
}
else
{
lean_object* v_val_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3442_; 
v_val_3417_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3419_ = v___x_3415_;
v_isShared_3420_ = v_isSharedCheck_3442_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_val_3417_);
lean_dec(v___x_3415_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3442_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v_fst_3421_; lean_object* v_snd_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3441_; 
v_fst_3421_ = lean_ctor_get(v_val_3417_, 0);
v_snd_3422_ = lean_ctor_get(v_val_3417_, 1);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_val_3417_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3424_ = v_val_3417_;
v_isShared_3425_ = v_isSharedCheck_3441_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_snd_3422_);
lean_inc(v_fst_3421_);
lean_dec(v_val_3417_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3441_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; uint32_t v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3426_ = lean_unsigned_to_nat(16u);
v___x_3427_ = lean_nat_mul(v___x_3426_, v_fst_3403_);
lean_dec(v_fst_3403_);
v___x_3428_ = lean_nat_add(v___x_3427_, v_fst_3408_);
lean_dec(v_fst_3408_);
lean_dec(v___x_3427_);
v___x_3429_ = lean_nat_mul(v___x_3426_, v___x_3428_);
lean_dec(v___x_3428_);
v___x_3430_ = lean_nat_add(v___x_3429_, v_fst_3413_);
lean_dec(v_fst_3413_);
lean_dec(v___x_3429_);
v___x_3431_ = lean_nat_mul(v___x_3426_, v___x_3430_);
lean_dec(v___x_3430_);
v___x_3432_ = lean_nat_add(v___x_3431_, v_fst_3421_);
lean_dec(v_fst_3421_);
lean_dec(v___x_3431_);
v___x_3433_ = l_Char_ofNat(v___x_3432_);
lean_dec(v___x_3432_);
v___x_3434_ = lean_box_uint32(v___x_3433_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v___x_3434_);
v___x_3436_ = v___x_3424_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3434_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_snd_3422_);
v___x_3436_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3438_; 
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3436_);
v___x_3438_ = v___x_3419_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
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
lean_object* v___x_3443_; 
v___x_3443_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3379_, v_i_3382_);
lean_dec(v_i_3382_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v___x_3444_; 
v___x_3444_ = lean_box(0);
return v___x_3444_;
}
else
{
lean_object* v_val_3445_; lean_object* v_fst_3446_; lean_object* v_snd_3447_; lean_object* v___x_3448_; 
v_val_3445_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_val_3445_);
lean_dec_ref_known(v___x_3443_, 1);
v_fst_3446_ = lean_ctor_get(v_val_3445_, 0);
lean_inc(v_fst_3446_);
v_snd_3447_ = lean_ctor_get(v_val_3445_, 1);
lean_inc(v_snd_3447_);
lean_dec(v_val_3445_);
v___x_3448_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3379_, v_snd_3447_);
lean_dec(v_snd_3447_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v___x_3449_; 
lean_dec(v_fst_3446_);
v___x_3449_ = lean_box(0);
return v___x_3449_;
}
else
{
lean_object* v_val_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3471_; 
v_val_3450_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3452_ = v___x_3448_;
v_isShared_3453_ = v_isSharedCheck_3471_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_val_3450_);
lean_dec(v___x_3448_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3471_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_fst_3454_; lean_object* v_snd_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3470_; 
v_fst_3454_ = lean_ctor_get(v_val_3450_, 0);
v_snd_3455_ = lean_ctor_get(v_val_3450_, 1);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_val_3450_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3457_ = v_val_3450_;
v_isShared_3458_ = v_isSharedCheck_3470_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_snd_3455_);
lean_inc(v_fst_3454_);
lean_dec(v_val_3450_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3470_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; uint32_t v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3459_ = lean_unsigned_to_nat(16u);
v___x_3460_ = lean_nat_mul(v___x_3459_, v_fst_3446_);
lean_dec(v_fst_3446_);
v___x_3461_ = lean_nat_add(v___x_3460_, v_fst_3454_);
lean_dec(v_fst_3454_);
lean_dec(v___x_3460_);
v___x_3462_ = l_Char_ofNat(v___x_3461_);
lean_dec(v___x_3461_);
v___x_3463_ = lean_box_uint32(v___x_3462_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v___x_3463_);
v___x_3465_ = v___x_3457_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_snd_3455_);
v___x_3465_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3467_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3465_);
v___x_3467_ = v___x_3452_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
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
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3472_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
v___x_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
lean_ctor_set(v___x_3473_, 1, v_i_3382_);
v___x_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
return v___x_3474_;
}
}
else
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3475_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
v___x_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
lean_ctor_set(v___x_3476_, 1, v_i_3382_);
v___x_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
return v___x_3477_;
}
}
else
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
v___x_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
lean_ctor_set(v___x_3479_, 1, v_i_3382_);
v___x_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
return v___x_3480_;
}
}
else
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3481_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
v___x_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
lean_ctor_set(v___x_3482_, 1, v_i_3382_);
v___x_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
return v___x_3483_;
}
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3484_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
lean_ctor_set(v___x_3485_, 1, v_i_3382_);
v___x_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
return v___x_3486_;
}
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3487_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
v___x_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v_i_3382_);
v___x_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
return v___x_3489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* v_s_3490_, lean_object* v_i_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Lean_Syntax_decodeQuotedChar(v_s_3490_, v_i_3491_);
lean_dec(v_i_3491_);
lean_dec_ref(v_s_3490_);
return v_res_3492_;
}
}
uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t v___y_3493_){
_start:
{
uint32_t v___x_3494_; uint8_t v___x_3495_; 
v___x_3494_ = 32;
v___x_3495_ = lean_uint32_dec_eq(v___y_3493_, v___x_3494_);
if (v___x_3495_ == 0)
{
uint32_t v___x_3496_; uint8_t v___x_3497_; 
v___x_3496_ = 9;
v___x_3497_ = lean_uint32_dec_eq(v___y_3493_, v___x_3496_);
if (v___x_3497_ == 0)
{
uint32_t v___x_3498_; uint8_t v___x_3499_; 
v___x_3498_ = 13;
v___x_3499_ = lean_uint32_dec_eq(v___y_3493_, v___x_3498_);
if (v___x_3499_ == 0)
{
uint32_t v___x_3500_; uint8_t v___x_3501_; 
v___x_3500_ = 10;
v___x_3501_ = lean_uint32_dec_eq(v___y_3493_, v___x_3500_);
return v___x_3501_;
}
else
{
return v___x_3499_;
}
}
else
{
return v___x_3497_;
}
}
else
{
return v___x_3495_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_decodeStringGap___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v___y_3493_ = stack[0].m_num;
uint8_t v_res_3502_;
v_res_3502_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_3493_);
stack->m_num = v_res_3502_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* v___y_3503_){
_start:
{
uint32_t v___y_270__boxed_3504_; uint8_t v_res_3505_; lean_object* v_r_3506_; 
v___y_270__boxed_3504_ = lean_unbox_uint32(v___y_3503_);
lean_dec(v___y_3503_);
v_res_3505_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_270__boxed_3504_);
v_r_3506_ = lean_box(v_res_3505_);
return v_r_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* v_s_3508_, lean_object* v_i_3509_){
_start:
{
lean_object* v___f_3510_; uint32_t v___x_3515_; uint32_t v___x_3516_; uint8_t v___x_3517_; 
v___f_3510_ = ((lean_object*)(l_Lean_Syntax_decodeStringGap___closed__0));
v___x_3515_ = lean_string_utf8_get(v_s_3508_, v_i_3509_);
v___x_3516_ = 32;
v___x_3517_ = lean_uint32_dec_eq(v___x_3515_, v___x_3516_);
if (v___x_3517_ == 0)
{
uint32_t v___x_3518_; uint8_t v___x_3519_; 
v___x_3518_ = 9;
v___x_3519_ = lean_uint32_dec_eq(v___x_3515_, v___x_3518_);
if (v___x_3519_ == 0)
{
uint32_t v___x_3520_; uint8_t v___x_3521_; 
v___x_3520_ = 13;
v___x_3521_ = lean_uint32_dec_eq(v___x_3515_, v___x_3520_);
if (v___x_3521_ == 0)
{
uint32_t v___x_3522_; uint8_t v___x_3523_; 
v___x_3522_ = 10;
v___x_3523_ = lean_uint32_dec_eq(v___x_3515_, v___x_3522_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3524_; 
lean_dec_ref(v_s_3508_);
v___x_3524_ = lean_box(0);
return v___x_3524_;
}
else
{
goto v___jp_3511_;
}
}
else
{
goto v___jp_3511_;
}
}
else
{
goto v___jp_3511_;
}
}
else
{
goto v___jp_3511_;
}
v___jp_3511_:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = lean_string_utf8_next(v_s_3508_, v_i_3509_);
v___x_3513_ = lean_string_nextwhile(v_s_3508_, v___f_3510_, v___x_3512_);
v___x_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
return v___x_3514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* v_s_3525_, lean_object* v_i_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lean_Syntax_decodeStringGap(v_s_3525_, v_i_3526_);
lean_dec(v_i_3526_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* v_s_3528_, lean_object* v_i_3529_, lean_object* v_acc_3530_){
_start:
{
uint32_t v_c_3531_; uint32_t v___x_3532_; uint8_t v___x_3533_; 
v_c_3531_ = lean_string_utf8_get(v_s_3528_, v_i_3529_);
v___x_3532_ = 34;
v___x_3533_ = lean_uint32_dec_eq(v_c_3531_, v___x_3532_);
if (v___x_3533_ == 0)
{
lean_object* v_i_3534_; uint8_t v___x_3535_; 
v_i_3534_ = lean_string_utf8_next(v_s_3528_, v_i_3529_);
lean_dec(v_i_3529_);
v___x_3535_ = lean_string_utf8_at_end(v_s_3528_, v_i_3534_);
if (v___x_3535_ == 0)
{
uint32_t v___x_3536_; uint8_t v___x_3537_; 
v___x_3536_ = 92;
v___x_3537_ = lean_uint32_dec_eq(v_c_3531_, v___x_3536_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; 
v___x_3538_ = lean_string_push(v_acc_3530_, v_c_3531_);
v_i_3529_ = v_i_3534_;
v_acc_3530_ = v___x_3538_;
goto _start;
}
else
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Lean_Syntax_decodeQuotedChar(v_s_3528_, v_i_3534_);
if (lean_obj_tag(v___x_3540_) == 1)
{
lean_object* v_val_3541_; lean_object* v_fst_3542_; lean_object* v_snd_3543_; uint32_t v___x_3544_; lean_object* v___x_3545_; 
lean_dec(v_i_3534_);
v_val_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_val_3541_);
lean_dec_ref_known(v___x_3540_, 1);
v_fst_3542_ = lean_ctor_get(v_val_3541_, 0);
lean_inc(v_fst_3542_);
v_snd_3543_ = lean_ctor_get(v_val_3541_, 1);
lean_inc(v_snd_3543_);
lean_dec(v_val_3541_);
v___x_3544_ = lean_unbox_uint32(v_fst_3542_);
lean_dec(v_fst_3542_);
v___x_3545_ = lean_string_push(v_acc_3530_, v___x_3544_);
v_i_3529_ = v_snd_3543_;
v_acc_3530_ = v___x_3545_;
goto _start;
}
else
{
lean_object* v___x_3547_; 
lean_dec(v___x_3540_);
lean_inc_ref(v_s_3528_);
v___x_3547_ = l_Lean_Syntax_decodeStringGap(v_s_3528_, v_i_3534_);
lean_dec(v_i_3534_);
if (lean_obj_tag(v___x_3547_) == 1)
{
lean_object* v_val_3548_; 
v_val_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_val_3548_);
lean_dec_ref_known(v___x_3547_, 1);
v_i_3529_ = v_val_3548_;
goto _start;
}
else
{
lean_object* v___x_3550_; 
lean_dec(v___x_3547_);
lean_dec_ref(v_acc_3530_);
lean_dec_ref(v_s_3528_);
v___x_3550_ = lean_box(0);
return v___x_3550_;
}
}
}
}
else
{
lean_object* v___x_3551_; 
lean_dec(v_i_3534_);
lean_dec_ref(v_acc_3530_);
lean_dec_ref(v_s_3528_);
v___x_3551_ = lean_box(0);
return v___x_3551_;
}
}
else
{
lean_object* v___x_3552_; 
lean_dec(v_i_3529_);
lean_dec_ref(v_s_3528_);
v___x_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3552_, 0, v_acc_3530_);
return v___x_3552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* v_s_3553_, lean_object* v_i_3554_, lean_object* v_num_3555_){
_start:
{
uint32_t v_c_3556_; lean_object* v_i_3557_; uint32_t v___x_3558_; uint8_t v___x_3559_; 
v_c_3556_ = lean_string_utf8_get(v_s_3553_, v_i_3554_);
v_i_3557_ = lean_string_utf8_next(v_s_3553_, v_i_3554_);
lean_dec(v_i_3554_);
v___x_3558_ = 35;
v___x_3559_ = lean_uint32_dec_eq(v_c_3556_, v___x_3558_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3560_ = lean_string_utf8_byte_size(v_s_3553_);
v___x_3561_ = lean_unsigned_to_nat(1u);
v___x_3562_ = lean_nat_add(v_num_3555_, v___x_3561_);
lean_dec(v_num_3555_);
v___x_3563_ = lean_nat_sub(v___x_3560_, v___x_3562_);
lean_dec(v___x_3562_);
v___x_3564_ = lean_string_utf8_extract(v_s_3553_, v_i_3557_, v___x_3563_);
lean_dec(v___x_3563_);
lean_dec(v_i_3557_);
return v___x_3564_;
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = lean_unsigned_to_nat(1u);
v___x_3566_ = lean_nat_add(v_num_3555_, v___x_3565_);
lean_dec(v_num_3555_);
v_i_3554_ = v_i_3557_;
v_num_3555_ = v___x_3566_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* v_s_3568_, lean_object* v_i_3569_, lean_object* v_num_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3568_, v_i_3569_, v_num_3570_);
lean_dec_ref(v_s_3568_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* v_s_3572_){
_start:
{
lean_object* v___x_3573_; uint32_t v___x_3574_; uint32_t v___x_3575_; uint8_t v___x_3576_; 
v___x_3573_ = lean_unsigned_to_nat(0u);
v___x_3574_ = lean_string_utf8_get(v_s_3572_, v___x_3573_);
v___x_3575_ = 114;
v___x_3576_ = lean_uint32_dec_eq(v___x_3574_, v___x_3575_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3577_ = lean_unsigned_to_nat(1u);
v___x_3578_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_3579_ = l_Lean_Syntax_decodeStrLitAux(v_s_3572_, v___x_3577_, v___x_3578_);
return v___x_3579_;
}
else
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3580_ = lean_unsigned_to_nat(1u);
v___x_3581_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3572_, v___x_3580_, v___x_3573_);
lean_dec_ref(v_s_3572_);
v___x_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
return v___x_3582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* v_stx_3583_){
_start:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_3585_ = l_Lean_Syntax_isLit_x3f(v___x_3584_, v_stx_3583_);
if (lean_obj_tag(v___x_3585_) == 1)
{
lean_object* v_val_3586_; lean_object* v___x_3587_; 
v_val_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_val_3586_);
lean_dec_ref_known(v___x_3585_, 1);
v___x_3587_ = l_Lean_Syntax_decodeStrLit(v_val_3586_);
return v___x_3587_;
}
else
{
lean_object* v___x_3588_; 
lean_dec(v___x_3585_);
v___x_3588_ = lean_box(0);
return v___x_3588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* v_stx_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Lean_Syntax_isStrLit_x3f(v_stx_3589_);
lean_dec(v_stx_3589_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* v_s_3591_){
_start:
{
lean_object* v___x_3592_; uint32_t v_c_3593_; uint32_t v___x_3594_; uint8_t v___x_3595_; 
v___x_3592_ = lean_unsigned_to_nat(1u);
v_c_3593_ = lean_string_utf8_get(v_s_3591_, v___x_3592_);
v___x_3594_ = 92;
v___x_3595_ = lean_uint32_dec_eq(v_c_3593_, v___x_3594_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = lean_box_uint32(v_c_3593_);
v___x_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
return v___x_3597_;
}
else
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = lean_unsigned_to_nat(2u);
v___x_3599_ = l_Lean_Syntax_decodeQuotedChar(v_s_3591_, v___x_3598_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v___x_3600_; 
v___x_3600_ = lean_box(0);
return v___x_3600_;
}
else
{
lean_object* v_val_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3609_; 
v_val_3601_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3603_ = v___x_3599_;
v_isShared_3604_ = v_isSharedCheck_3609_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_val_3601_);
lean_dec(v___x_3599_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3609_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v_fst_3605_; lean_object* v___x_3607_; 
v_fst_3605_ = lean_ctor_get(v_val_3601_, 0);
lean_inc(v_fst_3605_);
lean_dec(v_val_3601_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v_fst_3605_);
v___x_3607_ = v___x_3603_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_fst_3605_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* v_s_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_Syntax_decodeCharLit(v_s_3610_);
lean_dec_ref(v_s_3610_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* v_stx_3612_){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3613_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_3614_ = l_Lean_Syntax_isLit_x3f(v___x_3613_, v_stx_3612_);
if (lean_obj_tag(v___x_3614_) == 1)
{
lean_object* v_val_3615_; lean_object* v___x_3616_; 
v_val_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_val_3615_);
lean_dec_ref_known(v___x_3614_, 1);
v___x_3616_ = l_Lean_Syntax_decodeCharLit(v_val_3615_);
lean_dec(v_val_3615_);
return v___x_3616_;
}
else
{
lean_object* v___x_3617_; 
lean_dec(v___x_3614_);
v___x_3617_ = lean_box(0);
return v___x_3617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* v_stx_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_Syntax_isCharLit_x3f(v_stx_3618_);
lean_dec(v_stx_3618_);
return v_res_3619_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t v___y_3620_){
_start:
{
uint32_t v___x_3642_; uint8_t v___x_3643_; 
v___x_3642_ = 65;
v___x_3643_ = lean_uint32_dec_le(v___x_3642_, v___y_3620_);
if (v___x_3643_ == 0)
{
goto v___jp_3637_;
}
else
{
uint32_t v___x_3644_; uint8_t v___x_3645_; 
v___x_3644_ = 90;
v___x_3645_ = lean_uint32_dec_le(v___y_3620_, v___x_3644_);
if (v___x_3645_ == 0)
{
goto v___jp_3637_;
}
else
{
return v___x_3645_;
}
}
v___jp_3621_:
{
uint32_t v___x_3622_; uint8_t v___x_3623_; 
v___x_3622_ = 95;
v___x_3623_ = lean_uint32_dec_eq(v___y_3620_, v___x_3622_);
if (v___x_3623_ == 0)
{
uint32_t v___x_3624_; uint8_t v___x_3625_; 
v___x_3624_ = 39;
v___x_3625_ = lean_uint32_dec_eq(v___y_3620_, v___x_3624_);
if (v___x_3625_ == 0)
{
uint32_t v___x_3626_; uint8_t v___x_3627_; 
v___x_3626_ = 33;
v___x_3627_ = lean_uint32_dec_eq(v___y_3620_, v___x_3626_);
if (v___x_3627_ == 0)
{
uint32_t v___x_3628_; uint8_t v___x_3629_; 
v___x_3628_ = 63;
v___x_3629_ = lean_uint32_dec_eq(v___y_3620_, v___x_3628_);
if (v___x_3629_ == 0)
{
uint8_t v___x_3630_; 
v___x_3630_ = l_Lean_isLetterLike(v___y_3620_);
if (v___x_3630_ == 0)
{
uint8_t v___x_3631_; 
v___x_3631_ = l_Lean_isSubScriptAlnum(v___y_3620_);
return v___x_3631_;
}
else
{
return v___x_3630_;
}
}
else
{
return v___x_3629_;
}
}
else
{
return v___x_3627_;
}
}
else
{
return v___x_3625_;
}
}
else
{
return v___x_3623_;
}
}
v___jp_3632_:
{
uint32_t v___x_3633_; uint8_t v___x_3634_; 
v___x_3633_ = 48;
v___x_3634_ = lean_uint32_dec_le(v___x_3633_, v___y_3620_);
if (v___x_3634_ == 0)
{
goto v___jp_3621_;
}
else
{
uint32_t v___x_3635_; uint8_t v___x_3636_; 
v___x_3635_ = 57;
v___x_3636_ = lean_uint32_dec_le(v___y_3620_, v___x_3635_);
if (v___x_3636_ == 0)
{
goto v___jp_3621_;
}
else
{
return v___x_3636_;
}
}
}
v___jp_3637_:
{
uint32_t v___x_3638_; uint8_t v___x_3639_; 
v___x_3638_ = 97;
v___x_3639_ = lean_uint32_dec_le(v___x_3638_, v___y_3620_);
if (v___x_3639_ == 0)
{
goto v___jp_3632_;
}
else
{
uint32_t v___x_3640_; uint8_t v___x_3641_; 
v___x_3640_ = 122;
v___x_3641_ = lean_uint32_dec_le(v___y_3620_, v___x_3640_);
if (v___x_3641_ == 0)
{
goto v___jp_3632_;
}
else
{
return v___x_3641_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v___y_3620_ = stack[0].m_num;
uint8_t v_res_3646_;
v_res_3646_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_3620_);
stack->m_num = v_res_3646_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* v___y_3647_){
_start:
{
uint32_t v___y_496__boxed_3648_; uint8_t v_res_3649_; lean_object* v_r_3650_; 
v___y_496__boxed_3648_ = lean_unbox_uint32(v___y_3647_);
lean_dec(v___y_3647_);
v_res_3649_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_496__boxed_3648_);
v_r_3650_ = lean_box(v_res_3649_);
return v_r_3650_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t v___x_3651_, uint32_t v___x_3652_, uint32_t v___y_3653_){
_start:
{
uint8_t v___x_3654_; 
v___x_3654_ = lean_uint32_dec_le(v___x_3651_, v___y_3653_);
if (v___x_3654_ == 0)
{
return v___x_3654_;
}
else
{
uint8_t v___x_3655_; 
v___x_3655_ = lean_uint32_dec_le(v___y_3653_, v___x_3652_);
return v___x_3655_;
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1_0interp(lean_interpreter_value* stack)
{
uint32_t v___x_3651_ = stack[0].m_num;
uint32_t v___x_3652_ = stack[1].m_num;
uint32_t v___y_3653_ = stack[2].m_num;
uint8_t v_res_3656_;
v_res_3656_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___x_3651_, v___x_3652_, v___y_3653_);
stack->m_num = v_res_3656_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* v___x_3657_, lean_object* v___x_3658_, lean_object* v___y_3659_){
_start:
{
uint32_t v___x_576__boxed_3660_; uint32_t v___x_577__boxed_3661_; uint32_t v___y_578__boxed_3662_; uint8_t v_res_3663_; lean_object* v_r_3664_; 
v___x_576__boxed_3660_ = lean_unbox_uint32(v___x_3657_);
lean_dec(v___x_3657_);
v___x_577__boxed_3661_ = lean_unbox_uint32(v___x_3658_);
lean_dec(v___x_3658_);
v___y_578__boxed_3662_ = lean_unbox_uint32(v___y_3659_);
lean_dec(v___y_3659_);
v_res_3663_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___x_576__boxed_3660_, v___x_577__boxed_3661_, v___y_578__boxed_3662_);
v_r_3664_ = lean_box(v_res_3663_);
return v_r_3664_;
}
}
uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t v___x_3665_, uint8_t v___x_3666_, uint32_t v_x_3667_){
_start:
{
uint32_t v___x_3668_; uint8_t v___x_3669_; 
v___x_3668_ = 187;
v___x_3669_ = lean_uint32_dec_eq(v_x_3667_, v___x_3668_);
if (v___x_3669_ == 0)
{
return v___x_3665_;
}
else
{
return v___x_3666_;
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3665_ = stack[0].m_num;
uint8_t v___x_3666_ = stack[1].m_num;
uint32_t v_x_3667_ = stack[2].m_num;
uint8_t v_res_3670_;
v_res_3670_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v___x_3665_, v___x_3666_, v_x_3667_);
stack->m_num = v_res_3670_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* v___x_3671_, lean_object* v___x_3672_, lean_object* v_x_3673_){
_start:
{
uint8_t v___x_597__boxed_3674_; uint8_t v___x_598__boxed_3675_; uint32_t v_x_599__boxed_3676_; uint8_t v_res_3677_; lean_object* v_r_3678_; 
v___x_597__boxed_3674_ = lean_unbox(v___x_3671_);
v___x_598__boxed_3675_ = lean_unbox(v___x_3672_);
v_x_599__boxed_3676_ = lean_unbox_uint32(v_x_3673_);
lean_dec(v_x_3673_);
v_res_3677_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v___x_597__boxed_3674_, v___x_598__boxed_3675_, v_x_599__boxed_3676_);
v_r_3678_ = lean_box(v_res_3677_);
return v_r_3678_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = 48;
v___x_3681_ = lean_box_uint32(v___x_3680_);
return v___x_3681_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2(void){
_start:
{
uint32_t v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = 57;
v___x_3683_ = lean_box_uint32(v___x_3682_);
return v___x_3683_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1(void){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___f_3686_; 
v___x_3684_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1;
v___x_3685_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2;
v___f_3686_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3686_, 0, v___x_3684_);
lean_closure_set(v___f_3686_, 1, v___x_3685_);
return v___f_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* v_ss_3687_, lean_object* v_acc_3688_){
_start:
{
lean_object* v_ss_3690_; lean_object* v_acc_3691_; uint8_t v___x_3700_; 
lean_inc_ref(v_ss_3687_);
v___x_3700_ = lean_substring_isempty(v_ss_3687_);
if (v___x_3700_ == 0)
{
uint32_t v_curr_3701_; uint32_t v___x_3702_; uint8_t v___x_3703_; 
lean_inc_ref(v_ss_3687_);
v_curr_3701_ = lean_substring_front(v_ss_3687_);
v___x_3702_ = 171;
v___x_3703_ = lean_uint32_dec_eq(v_curr_3701_, v___x_3702_);
if (v___x_3703_ == 0)
{
lean_object* v___f_3704_; uint32_t v___x_3740_; uint8_t v___x_3741_; 
v___f_3704_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0));
v___x_3740_ = 65;
v___x_3741_ = lean_uint32_dec_le(v___x_3740_, v_curr_3701_);
if (v___x_3741_ == 0)
{
goto v___jp_3735_;
}
else
{
uint32_t v___x_3742_; uint8_t v___x_3743_; 
v___x_3742_ = 90;
v___x_3743_ = lean_uint32_dec_le(v_curr_3701_, v___x_3742_);
if (v___x_3743_ == 0)
{
goto v___jp_3735_;
}
else
{
goto v___jp_3705_;
}
}
v___jp_3705_:
{
lean_object* v_idPart_3706_; lean_object* v_startPos_3707_; lean_object* v_stopPos_3708_; lean_object* v_startPos_3709_; lean_object* v_stopPos_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
lean_inc_ref(v_ss_3687_);
v_idPart_3706_ = lean_substring_takewhile(v_ss_3687_, v___f_3704_);
v_startPos_3707_ = lean_ctor_get(v_idPart_3706_, 1);
v_stopPos_3708_ = lean_ctor_get(v_idPart_3706_, 2);
v_startPos_3709_ = lean_ctor_get(v_ss_3687_, 1);
v_stopPos_3710_ = lean_ctor_get(v_ss_3687_, 2);
v___x_3711_ = lean_nat_sub(v_stopPos_3708_, v_startPos_3707_);
v___x_3712_ = lean_nat_sub(v_stopPos_3710_, v_startPos_3709_);
v___x_3713_ = lean_substring_extract(v_ss_3687_, v___x_3711_, v___x_3712_);
v___x_3714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3714_, 0, v_idPart_3706_);
lean_ctor_set(v___x_3714_, 1, v_acc_3688_);
v_ss_3690_ = v___x_3713_;
v_acc_3691_ = v___x_3714_;
goto v___jp_3689_;
}
v___jp_3715_:
{
uint32_t v___x_3716_; uint8_t v___x_3717_; 
v___x_3716_ = 95;
v___x_3717_ = lean_uint32_dec_eq(v_curr_3701_, v___x_3716_);
if (v___x_3717_ == 0)
{
uint8_t v___x_3718_; 
v___x_3718_ = l_Lean_isLetterLike(v_curr_3701_);
if (v___x_3718_ == 0)
{
uint32_t v___x_3719_; uint8_t v___x_3720_; 
v___x_3719_ = 48;
v___x_3720_ = lean_uint32_dec_le(v___x_3719_, v_curr_3701_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3721_; 
lean_dec(v_acc_3688_);
lean_dec_ref(v_ss_3687_);
v___x_3721_ = lean_box(0);
return v___x_3721_;
}
else
{
uint32_t v___x_3722_; uint8_t v___x_3723_; 
v___x_3722_ = 57;
v___x_3723_ = lean_uint32_dec_le(v_curr_3701_, v___x_3722_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3724_; 
lean_dec(v_acc_3688_);
lean_dec_ref(v_ss_3687_);
v___x_3724_ = lean_box(0);
return v___x_3724_;
}
else
{
lean_object* v___f_3725_; lean_object* v_idPart_3726_; lean_object* v_startPos_3727_; lean_object* v_stopPos_3728_; lean_object* v_startPos_3729_; lean_object* v_stopPos_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___f_3725_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1, &l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1);
lean_inc_ref(v_ss_3687_);
v_idPart_3726_ = lean_substring_takewhile(v_ss_3687_, v___f_3725_);
v_startPos_3727_ = lean_ctor_get(v_idPart_3726_, 1);
v_stopPos_3728_ = lean_ctor_get(v_idPart_3726_, 2);
v_startPos_3729_ = lean_ctor_get(v_ss_3687_, 1);
v_stopPos_3730_ = lean_ctor_get(v_ss_3687_, 2);
v___x_3731_ = lean_nat_sub(v_stopPos_3728_, v_startPos_3727_);
v___x_3732_ = lean_nat_sub(v_stopPos_3730_, v_startPos_3729_);
v___x_3733_ = lean_substring_extract(v_ss_3687_, v___x_3731_, v___x_3732_);
v___x_3734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3734_, 0, v_idPart_3726_);
lean_ctor_set(v___x_3734_, 1, v_acc_3688_);
v_ss_3690_ = v___x_3733_;
v_acc_3691_ = v___x_3734_;
goto v___jp_3689_;
}
}
}
else
{
goto v___jp_3705_;
}
}
else
{
goto v___jp_3705_;
}
}
v___jp_3735_:
{
uint32_t v___x_3736_; uint8_t v___x_3737_; 
v___x_3736_ = 97;
v___x_3737_ = lean_uint32_dec_le(v___x_3736_, v_curr_3701_);
if (v___x_3737_ == 0)
{
goto v___jp_3715_;
}
else
{
uint32_t v___x_3738_; uint8_t v___x_3739_; 
v___x_3738_ = 122;
v___x_3739_ = lean_uint32_dec_le(v_curr_3701_, v___x_3738_);
if (v___x_3739_ == 0)
{
goto v___jp_3715_;
}
else
{
goto v___jp_3705_;
}
}
}
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___f_3746_; lean_object* v_escapedPart_3747_; lean_object* v_str_3748_; lean_object* v_startPos_3749_; lean_object* v_stopPos_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3771_; 
v___x_3744_ = lean_box(v___x_3703_);
v___x_3745_ = lean_box(v___x_3700_);
v___f_3746_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3746_, 0, v___x_3744_);
lean_closure_set(v___f_3746_, 1, v___x_3745_);
lean_inc_ref(v_ss_3687_);
v_escapedPart_3747_ = lean_substring_takewhile(v_ss_3687_, v___f_3746_);
v_str_3748_ = lean_ctor_get(v_escapedPart_3747_, 0);
v_startPos_3749_ = lean_ctor_get(v_escapedPart_3747_, 1);
v_stopPos_3750_ = lean_ctor_get(v_escapedPart_3747_, 2);
v_isSharedCheck_3771_ = !lean_is_exclusive(v_escapedPart_3747_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3752_ = v_escapedPart_3747_;
v_isShared_3753_ = v_isSharedCheck_3771_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_stopPos_3750_);
lean_inc(v_startPos_3749_);
lean_inc(v_str_3748_);
lean_dec(v_escapedPart_3747_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3771_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v_startPos_3754_; lean_object* v_stopPos_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v_escapedPart_3759_; 
v_startPos_3754_ = lean_ctor_get(v_ss_3687_, 1);
v_stopPos_3755_ = lean_ctor_get(v_ss_3687_, 2);
v___x_3756_ = lean_string_utf8_next(v_str_3748_, v_stopPos_3750_);
lean_dec(v_stopPos_3750_);
lean_inc(v_stopPos_3755_);
v___x_3757_ = lean_string_pos_min(v_stopPos_3755_, v___x_3756_);
lean_inc(v___x_3757_);
lean_inc(v_startPos_3749_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 2, v___x_3757_);
v_escapedPart_3759_ = v___x_3752_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_str_3748_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v_startPos_3749_);
lean_ctor_set(v_reuseFailAlloc_3770_, 2, v___x_3757_);
v_escapedPart_3759_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; uint32_t v___x_3762_; uint32_t v___x_3763_; uint8_t v___x_3764_; 
v___x_3760_ = lean_nat_sub(v___x_3757_, v_startPos_3749_);
lean_dec(v_startPos_3749_);
lean_dec(v___x_3757_);
lean_inc(v___x_3760_);
lean_inc_ref_n(v_escapedPart_3759_, 2);
v___x_3761_ = lean_substring_prev(v_escapedPart_3759_, v___x_3760_);
v___x_3762_ = lean_substring_get(v_escapedPart_3759_, v___x_3761_);
v___x_3763_ = 187;
v___x_3764_ = lean_uint32_dec_eq(v___x_3762_, v___x_3763_);
if (v___x_3764_ == 0)
{
lean_object* v___x_3765_; 
lean_dec(v___x_3760_);
lean_dec_ref(v_escapedPart_3759_);
lean_dec(v_acc_3688_);
lean_dec_ref(v_ss_3687_);
v___x_3765_ = lean_box(0);
return v___x_3765_;
}
else
{
if (v___x_3700_ == 0)
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3766_ = lean_nat_sub(v_stopPos_3755_, v_startPos_3754_);
v___x_3767_ = lean_substring_extract(v_ss_3687_, v___x_3760_, v___x_3766_);
v___x_3768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3768_, 0, v_escapedPart_3759_);
lean_ctor_set(v___x_3768_, 1, v_acc_3688_);
v_ss_3690_ = v___x_3767_;
v_acc_3691_ = v___x_3768_;
goto v___jp_3689_;
}
else
{
lean_object* v___x_3769_; 
lean_dec(v___x_3760_);
lean_dec_ref(v_escapedPart_3759_);
lean_dec(v_acc_3688_);
lean_dec_ref(v_ss_3687_);
v___x_3769_ = lean_box(0);
return v___x_3769_;
}
}
}
}
}
}
else
{
lean_object* v___x_3772_; 
lean_dec(v_acc_3688_);
lean_dec_ref(v_ss_3687_);
v___x_3772_ = lean_box(0);
return v___x_3772_;
}
v___jp_3689_:
{
uint32_t v___x_3692_; uint32_t v___x_3693_; uint8_t v___x_3694_; 
lean_inc_ref(v_ss_3690_);
v___x_3692_ = lean_substring_front(v_ss_3690_);
v___x_3693_ = 46;
v___x_3694_ = lean_uint32_dec_eq(v___x_3692_, v___x_3693_);
if (v___x_3694_ == 0)
{
uint8_t v___x_3695_; 
v___x_3695_ = lean_substring_isempty(v_ss_3690_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; 
lean_dec(v_acc_3691_);
v___x_3696_ = lean_box(0);
return v___x_3696_;
}
else
{
return v_acc_3691_;
}
}
else
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = lean_unsigned_to_nat(1u);
v___x_3698_ = lean_substring_drop(v_ss_3690_, v___x_3697_);
v_ss_3687_ = v___x_3698_;
v_acc_3688_ = v_acc_3691_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* v_ss_3773_){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3774_ = lean_box(0);
v___x_3775_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_ss_3773_, v___x_3774_);
v___x_3776_ = l_List_reverse___redArg(v___x_3775_);
return v___x_3776_;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3780_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3781_ = lean_unsigned_to_nat(10u);
v___x_3782_ = lean_unsigned_to_nat(1253u);
v___x_3783_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3784_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3785_ = l_mkPanicMessageWithDecl(v___x_3784_, v___x_3783_, v___x_3782_, v___x_3781_, v___x_3780_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object* v_init_3786_, lean_object* v_x_3787_){
_start:
{
if (lean_obj_tag(v_x_3787_) == 0)
{
lean_inc(v_init_3786_);
return v_init_3786_;
}
else
{
lean_object* v_head_3788_; lean_object* v_tail_3789_; lean_object* v___x_3790_; lean_object* v_comp_3791_; uint32_t v___x_3792_; uint32_t v___x_3793_; uint8_t v___x_3794_; 
v_head_3788_ = lean_ctor_get(v_x_3787_, 0);
lean_inc(v_head_3788_);
v_tail_3789_ = lean_ctor_get(v_x_3787_, 1);
lean_inc(v_tail_3789_);
lean_dec_ref_known(v_x_3787_, 2);
v___x_3790_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3786_, v_tail_3789_);
v_comp_3791_ = lean_substring_tostring(v_head_3788_);
lean_inc_ref(v_comp_3791_);
v___x_3792_ = lean_string_front(v_comp_3791_);
v___x_3793_ = 171;
v___x_3794_ = lean_uint32_dec_eq(v___x_3792_, v___x_3793_);
if (v___x_3794_ == 0)
{
uint32_t v___x_3795_; uint8_t v___x_3796_; 
v___x_3795_ = 48;
v___x_3796_ = lean_uint32_dec_le(v___x_3795_, v___x_3792_);
if (v___x_3796_ == 0)
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Lean_Name_str___override(v___x_3790_, v_comp_3791_);
return v___x_3797_;
}
else
{
uint32_t v___x_3798_; uint8_t v___x_3799_; 
v___x_3798_ = 57;
v___x_3799_ = lean_uint32_dec_le(v___x_3792_, v___x_3798_);
if (v___x_3799_ == 0)
{
lean_object* v___x_3800_; 
v___x_3800_ = l_Lean_Name_str___override(v___x_3790_, v_comp_3791_);
return v___x_3800_;
}
else
{
lean_object* v___x_3801_; 
v___x_3801_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3791_);
lean_dec_ref(v_comp_3791_);
if (lean_obj_tag(v___x_3801_) == 1)
{
lean_object* v_val_3802_; lean_object* v___x_3803_; 
v_val_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_val_3802_);
lean_dec_ref_known(v___x_3801_, 1);
v___x_3803_ = l_Lean_Name_num___override(v___x_3790_, v_val_3802_);
return v___x_3803_;
}
else
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
lean_dec(v___x_3801_);
lean_dec(v___x_3790_);
v___x_3804_ = lean_obj_once(&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3, &l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3805_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3804_);
return v___x_3805_;
}
}
}
}
else
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3806_ = lean_unsigned_to_nat(1u);
v___x_3807_ = lean_string_drop(v_comp_3791_, v___x_3806_);
v___x_3808_ = lean_string_dropright(v___x_3807_, v___x_3806_);
v___x_3809_ = l_Lean_Name_str___override(v___x_3790_, v___x_3808_);
return v___x_3809_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_init_3810_, lean_object* v_x_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3810_, v_x_3811_);
lean_dec(v_init_3810_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3813_){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = lean_box(0);
v___x_3815_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3813_, v___x_3814_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v___x_3816_; 
v___x_3816_ = lean_box(0);
return v___x_3816_;
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3817_ = lean_box(0);
v___x_3818_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v___x_3817_, v___x_3815_);
return v___x_3818_;
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3819_){
_start:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3820_ = lean_unsigned_to_nat(0u);
v___x_3821_ = lean_string_utf8_byte_size(v_s_3819_);
v___x_3822_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3822_, 0, v_s_3819_);
lean_ctor_set(v___x_3822_, 1, v___x_3820_);
lean_ctor_set(v___x_3822_, 2, v___x_3821_);
v___x_3823_ = l_Substring_Raw_toName(v___x_3822_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3824_){
_start:
{
lean_object* v___x_3825_; uint32_t v___x_3826_; uint32_t v___x_3827_; uint8_t v___x_3828_; 
v___x_3825_ = lean_unsigned_to_nat(0u);
v___x_3826_ = lean_string_utf8_get(v_s_3824_, v___x_3825_);
v___x_3827_ = 96;
v___x_3828_ = lean_uint32_dec_eq(v___x_3826_, v___x_3827_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3829_; 
lean_dec_ref(v_s_3824_);
v___x_3829_ = lean_box(0);
return v___x_3829_;
}
else
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3830_ = lean_string_utf8_byte_size(v_s_3824_);
v___x_3831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3831_, 0, v_s_3824_);
lean_ctor_set(v___x_3831_, 1, v___x_3825_);
lean_ctor_set(v___x_3831_, 2, v___x_3830_);
v___x_3832_ = lean_unsigned_to_nat(1u);
v___x_3833_ = lean_substring_drop(v___x_3831_, v___x_3832_);
v___x_3834_ = l_Substring_Raw_toName(v___x_3833_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v___x_3835_; 
v___x_3835_ = lean_box(0);
return v___x_3835_;
}
else
{
lean_object* v___x_3836_; 
v___x_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3834_);
return v___x_3836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3837_){
_start:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3838_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3839_ = l_Lean_Syntax_isLit_x3f(v___x_3838_, v_stx_3837_);
if (lean_obj_tag(v___x_3839_) == 1)
{
lean_object* v_val_3840_; lean_object* v___x_3841_; 
v_val_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_val_3840_);
lean_dec_ref_known(v___x_3839_, 1);
v___x_3841_ = l_Lean_Syntax_decodeNameLit(v_val_3840_);
return v___x_3841_;
}
else
{
lean_object* v___x_3842_; 
lean_dec(v___x_3839_);
v___x_3842_ = lean_box(0);
return v___x_3842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3843_);
lean_dec(v_stx_3843_);
return v_res_3844_;
}
}
uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3845_){
_start:
{
if (lean_obj_tag(v_x_3845_) == 1)
{
lean_object* v_args_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; uint8_t v___x_3849_; 
v_args_3846_ = lean_ctor_get(v_x_3845_, 2);
v___x_3847_ = lean_unsigned_to_nat(0u);
v___x_3848_ = lean_array_get_size(v_args_3846_);
v___x_3849_ = lean_nat_dec_lt(v___x_3847_, v___x_3848_);
return v___x_3849_;
}
else
{
uint8_t v___x_3850_; 
v___x_3850_ = 0;
return v___x_3850_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_hasArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3845_ = stack[0].m_obj;
uint8_t v_res_3851_;
v_res_3851_ = l_Lean_Syntax_hasArgs(v_x_3845_);
stack->m_num = v_res_3851_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3852_){
_start:
{
uint8_t v_res_3853_; lean_object* v_r_3854_; 
v_res_3853_ = l_Lean_Syntax_hasArgs(v_x_3852_);
lean_dec(v_x_3852_);
v_r_3854_ = lean_box(v_res_3853_);
return v_r_3854_;
}
}
uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3855_){
_start:
{
if (lean_obj_tag(v_x_3855_) == 2)
{
uint8_t v___x_3856_; 
v___x_3856_ = 1;
return v___x_3856_;
}
else
{
uint8_t v___x_3857_; 
v___x_3857_ = 0;
return v___x_3857_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_isAtom_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3855_ = stack[0].m_obj;
uint8_t v_res_3858_;
v_res_3858_ = l_Lean_Syntax_isAtom(v_x_3855_);
stack->m_num = v_res_3858_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3859_){
_start:
{
uint8_t v_res_3860_; lean_object* v_r_3861_; 
v_res_3860_ = l_Lean_Syntax_isAtom(v_x_3859_);
lean_dec(v_x_3859_);
v_r_3861_ = lean_box(v_res_3860_);
return v_r_3861_;
}
}
uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3862_, lean_object* v_x_3863_){
_start:
{
if (lean_obj_tag(v_x_3863_) == 2)
{
lean_object* v_val_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; 
v_val_3864_ = lean_ctor_get(v_x_3863_, 1);
lean_inc_ref(v_val_3864_);
lean_dec_ref_known(v_x_3863_, 2);
v___x_3865_ = lean_string_trim(v_val_3864_);
v___x_3866_ = lean_string_trim(v_token_3862_);
v___x_3867_ = lean_string_dec_eq(v___x_3865_, v___x_3866_);
lean_dec_ref(v___x_3866_);
lean_dec_ref(v___x_3865_);
return v___x_3867_;
}
else
{
uint8_t v___x_3868_; 
lean_dec(v_x_3863_);
lean_dec_ref(v_token_3862_);
v___x_3868_ = 0;
return v___x_3868_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_isToken_0interp(lean_interpreter_value* stack)
{
lean_object* v_token_3862_ = stack[0].m_obj;
lean_object* v_x_3863_ = stack[1].m_obj;
uint8_t v_res_3869_;
v_res_3869_ = l_Lean_Syntax_isToken(v_token_3862_, v_x_3863_);
stack->m_num = v_res_3869_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3870_, lean_object* v_x_3871_){
_start:
{
uint8_t v_res_3872_; lean_object* v_r_3873_; 
v_res_3872_ = l_Lean_Syntax_isToken(v_token_3870_, v_x_3871_);
v_r_3873_ = lean_box(v_res_3872_);
return v_r_3873_;
}
}
uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3874_){
_start:
{
switch(lean_obj_tag(v_stx_3874_))
{
case 1:
{
lean_object* v_kind_3875_; lean_object* v_args_3876_; lean_object* v___x_3877_; uint8_t v___x_3878_; 
v_kind_3875_ = lean_ctor_get(v_stx_3874_, 1);
v_args_3876_ = lean_ctor_get(v_stx_3874_, 2);
v___x_3877_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3878_ = lean_name_eq(v_kind_3875_, v___x_3877_);
if (v___x_3878_ == 0)
{
return v___x_3878_;
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3880_; uint8_t v___x_3881_; 
v___x_3879_ = lean_array_get_size(v_args_3876_);
v___x_3880_ = lean_unsigned_to_nat(0u);
v___x_3881_ = lean_nat_dec_eq(v___x_3879_, v___x_3880_);
return v___x_3881_;
}
}
case 0:
{
uint8_t v___x_3882_; 
v___x_3882_ = 1;
return v___x_3882_;
}
default: 
{
uint8_t v___x_3883_; 
v___x_3883_ = 0;
return v___x_3883_;
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_isNone_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3874_ = stack[0].m_obj;
uint8_t v_res_3884_;
v_res_3884_ = l_Lean_Syntax_isNone(v_stx_3874_);
stack->m_num = v_res_3884_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3885_){
_start:
{
uint8_t v_res_3886_; lean_object* v_r_3887_; 
v_res_3886_ = l_Lean_Syntax_isNone(v_stx_3885_);
lean_dec(v_stx_3885_);
v_r_3887_ = lean_box(v_res_3886_);
return v_r_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3888_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_Syntax_getOptional_x3f(v_stx_3888_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v___x_3890_; 
v___x_3890_ = lean_box(0);
return v___x_3890_;
}
else
{
lean_object* v_val_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3899_; 
v_val_3891_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3893_ = v___x_3889_;
v_isShared_3894_ = v_isSharedCheck_3899_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_val_3891_);
lean_dec(v___x_3889_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3899_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3895_; lean_object* v___x_3897_; 
v___x_3895_ = l_Lean_Syntax_getId(v_val_3891_);
lean_dec(v_val_3891_);
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v___x_3895_);
v___x_3897_ = v___x_3893_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3900_);
lean_dec(v_stx_3900_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3902_, lean_object* v_x_3903_){
_start:
{
if (lean_obj_tag(v_x_3903_) == 1)
{
lean_object* v_args_3904_; lean_object* v___x_3905_; uint8_t v___x_3906_; 
v_args_3904_ = lean_ctor_get(v_x_3903_, 2);
lean_inc_ref(v_p_3902_);
lean_inc_ref(v_x_3903_);
v___x_3905_ = lean_apply_1(v_p_3902_, v_x_3903_);
v___x_3906_ = lean_unbox(v___x_3905_);
if (v___x_3906_ == 0)
{
lean_object* v___x_3907_; lean_object* v___x_3908_; size_t v_sz_3909_; size_t v___x_3910_; lean_object* v___x_3911_; lean_object* v_fst_3912_; 
lean_inc_ref(v_args_3904_);
lean_dec_ref_known(v_x_3903_, 3);
v___x_3907_ = lean_box(0);
v___x_3908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3909_ = lean_array_size(v_args_3904_);
v___x_3910_ = ((size_t)0ULL);
v___x_3911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3902_, v_args_3904_, v_sz_3909_, v___x_3910_, v___x_3908_);
lean_dec_ref(v_args_3904_);
v_fst_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_fst_3912_);
lean_dec_ref(v___x_3911_);
if (lean_obj_tag(v_fst_3912_) == 0)
{
return v___x_3907_;
}
else
{
lean_object* v_val_3913_; 
v_val_3913_ = lean_ctor_get(v_fst_3912_, 0);
lean_inc(v_val_3913_);
lean_dec_ref_known(v_fst_3912_, 1);
return v_val_3913_;
}
}
else
{
lean_object* v___x_3914_; 
lean_dec_ref(v_p_3902_);
v___x_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3914_, 0, v_x_3903_);
return v___x_3914_;
}
}
else
{
lean_object* v___x_3915_; uint8_t v___x_3916_; 
lean_inc(v_x_3903_);
v___x_3915_ = lean_apply_1(v_p_3902_, v_x_3903_);
v___x_3916_ = lean_unbox(v___x_3915_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; 
lean_dec(v_x_3903_);
v___x_3917_ = lean_box(0);
return v___x_3917_;
}
else
{
lean_object* v___x_3918_; 
v___x_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3918_, 0, v_x_3903_);
return v___x_3918_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3919_, lean_object* v_as_3920_, size_t v_sz_3921_, size_t v_i_3922_, lean_object* v_b_3923_){
_start:
{
uint8_t v___x_3924_; 
v___x_3924_ = lean_usize_dec_lt(v_i_3922_, v_sz_3921_);
if (v___x_3924_ == 0)
{
lean_dec_ref(v_p_3919_);
lean_inc_ref(v_b_3923_);
return v_b_3923_;
}
else
{
lean_object* v___x_3925_; lean_object* v_a_3926_; lean_object* v___x_3927_; 
v___x_3925_ = lean_box(0);
v_a_3926_ = lean_array_uget_borrowed(v_as_3920_, v_i_3922_);
lean_inc(v_a_3926_);
lean_inc_ref(v_p_3919_);
v___x_3927_ = l_Lean_Syntax_findAux(v_p_3919_, v_a_3926_);
if (lean_obj_tag(v___x_3927_) == 1)
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
lean_dec_ref(v_p_3919_);
v___x_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
v___x_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
lean_ctor_set(v___x_3929_, 1, v___x_3925_);
return v___x_3929_;
}
else
{
lean_object* v___x_3930_; size_t v___x_3931_; size_t v___x_3932_; 
lean_dec(v___x_3927_);
v___x_3930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3931_ = ((size_t)1ULL);
v___x_3932_ = lean_usize_add(v_i_3922_, v___x_3931_);
v_i_3922_ = v___x_3932_;
v_b_3923_ = v___x_3930_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3919_ = stack[0].m_obj;
lean_object* v_as_3920_ = stack[1].m_obj;
size_t v_sz_3921_ = stack[2].m_num;
size_t v_i_3922_ = stack[3].m_num;
lean_object* v_b_3923_ = stack[4].m_obj;
lean_object* v_res_3934_;
v_res_3934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3919_, v_as_3920_, v_sz_3921_, v_i_3922_, v_b_3923_);
stack->m_obj
 = v_res_3934_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3935_, lean_object* v_as_3936_, lean_object* v_sz_3937_, lean_object* v_i_3938_, lean_object* v_b_3939_){
_start:
{
size_t v_sz_boxed_3940_; size_t v_i_boxed_3941_; lean_object* v_res_3942_; 
v_sz_boxed_3940_ = lean_unbox_usize(v_sz_3937_);
lean_dec(v_sz_3937_);
v_i_boxed_3941_ = lean_unbox_usize(v_i_3938_);
lean_dec(v_i_3938_);
v_res_3942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3935_, v_as_3936_, v_sz_boxed_3940_, v_i_boxed_3941_, v_b_3939_);
lean_dec_ref(v_b_3939_);
lean_dec_ref(v_as_3936_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3943_, lean_object* v_p_3944_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_Syntax_findAux(v_p_3944_, v_stx_3943_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3946_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Lean_Syntax_isNatLit_x3f(v_s_3946_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v___x_3948_; 
v___x_3948_ = lean_unsigned_to_nat(0u);
return v___x_3948_;
}
else
{
lean_object* v_val_3949_; 
v_val_3949_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_val_3949_);
lean_dec_ref_known(v___x_3947_, 1);
return v_val_3949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Lean_TSyntax_getNat(v_s_3950_);
lean_dec(v_s_3950_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3955_){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3957_ = l_Lean_Syntax_isLit_x3f(v___x_3956_, v_stx_3955_);
if (lean_obj_tag(v___x_3957_) == 1)
{
lean_object* v_val_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_val_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_val_3958_);
lean_dec_ref_known(v___x_3957_, 1);
v___x_3959_ = lean_unsigned_to_nat(0u);
v___x_3960_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3958_, v___x_3959_, v___x_3959_);
lean_dec(v_val_3958_);
return v___x_3960_;
}
else
{
lean_object* v___x_3961_; 
lean_dec(v___x_3957_);
v___x_3961_ = lean_box(0);
return v___x_3961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3962_);
lean_dec(v_stx_3962_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3964_){
_start:
{
lean_object* v___x_3965_; 
v___x_3965_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3964_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v___x_3966_; 
v___x_3966_ = lean_unsigned_to_nat(0u);
return v___x_3966_;
}
else
{
lean_object* v_val_3967_; 
v_val_3967_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_val_3967_);
lean_dec_ref_known(v___x_3965_, 1);
return v_val_3967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Lean_TSyntax_getHexNumVal(v_s_3968_);
lean_dec(v_s_3968_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3970_, lean_object* v_p_3971_, lean_object* v_n_3972_){
_start:
{
uint8_t v___x_3973_; 
v___x_3973_ = lean_string_utf8_at_end(v_s_3970_, v_p_3971_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; uint32_t v___x_3975_; uint32_t v___x_3976_; uint8_t v___x_3977_; 
v___x_3974_ = lean_string_utf8_next(v_s_3970_, v_p_3971_);
v___x_3975_ = lean_string_utf8_get(v_s_3970_, v_p_3971_);
lean_dec(v_p_3971_);
v___x_3976_ = 95;
v___x_3977_ = lean_uint32_dec_eq(v___x_3975_, v___x_3976_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3978_ = lean_unsigned_to_nat(1u);
v___x_3979_ = lean_nat_add(v_n_3972_, v___x_3978_);
lean_dec(v_n_3972_);
v_p_3971_ = v___x_3974_;
v_n_3972_ = v___x_3979_;
goto _start;
}
else
{
v_p_3971_ = v___x_3974_;
goto _start;
}
}
else
{
lean_dec(v_p_3971_);
return v_n_3972_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3982_, lean_object* v_p_3983_, lean_object* v_n_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3982_, v_p_3983_, v_n_3984_);
lean_dec_ref(v_s_3982_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3986_){
_start:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3987_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3988_ = l_Lean_Syntax_isLit_x3f(v___x_3987_, v_s_3986_);
if (lean_obj_tag(v___x_3988_) == 1)
{
lean_object* v_val_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v_val_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_val_3989_);
lean_dec_ref_known(v___x_3988_, 1);
v___x_3990_ = lean_unsigned_to_nat(0u);
v___x_3991_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3989_, v___x_3990_, v___x_3990_);
lean_dec(v_val_3989_);
return v___x_3991_;
}
else
{
lean_object* v___x_3992_; 
lean_dec(v___x_3988_);
v___x_3992_ = lean_unsigned_to_nat(0u);
return v___x_3992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_TSyntax_getHexNumSize(v_s_3993_);
lean_dec(v_s_3993_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3995_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Lean_Syntax_getId(v_s_3995_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_Lean_TSyntax_getId(v_s_3997_);
lean_dec(v_s_3997_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_4006_){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = l_Lean_Syntax_isScientificLit_x3f(v_s_4006_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v___x_4008_; 
v___x_4008_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
return v___x_4008_;
}
else
{
lean_object* v_val_4009_; 
v_val_4009_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_val_4009_);
lean_dec_ref_known(v___x_4007_, 1);
return v_val_4009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l_Lean_TSyntax_getScientific(v_s_4010_);
lean_dec(v_s_4010_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_4012_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = l_Lean_Syntax_isStrLit_x3f(v_s_4012_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v___x_4014_; 
v___x_4014_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_4014_;
}
else
{
lean_object* v_val_4015_; 
v_val_4015_ = lean_ctor_get(v___x_4013_, 0);
lean_inc(v_val_4015_);
lean_dec_ref_known(v___x_4013_, 1);
return v_val_4015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_Lean_TSyntax_getString(v_s_4016_);
lean_dec(v_s_4016_);
return v_res_4017_;
}
}
uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_4018_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = l_Lean_Syntax_isCharLit_x3f(v_s_4018_);
if (lean_obj_tag(v___x_4019_) == 0)
{
uint32_t v___x_4020_; 
v___x_4020_ = 65;
return v___x_4020_;
}
else
{
lean_object* v_val_4021_; uint32_t v___x_4022_; 
v_val_4021_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_val_4021_);
lean_dec_ref_known(v___x_4019_, 1);
v___x_4022_ = lean_unbox_uint32(v_val_4021_);
lean_dec(v_val_4021_);
return v___x_4022_;
}
}
}
LEAN_EXPORT void l_Lean_TSyntax_getChar_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4018_ = stack[0].m_obj;
uint32_t v_res_4023_;
v_res_4023_ = l_Lean_TSyntax_getChar(v_s_4018_);
stack->m_num = v_res_4023_;
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_4024_){
_start:
{
uint32_t v_res_4025_; lean_object* v_r_4026_; 
v_res_4025_ = l_Lean_TSyntax_getChar(v_s_4024_);
lean_dec(v_s_4024_);
v_r_4026_ = lean_box_uint32(v_res_4025_);
return v_r_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_4027_){
_start:
{
lean_object* v___x_4028_; 
v___x_4028_ = l_Lean_Syntax_isNameLit_x3f(v_s_4027_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v___x_4029_; 
v___x_4029_ = lean_box(0);
return v___x_4029_;
}
else
{
lean_object* v_val_4030_; 
v_val_4030_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_val_4030_);
lean_dec_ref_known(v___x_4028_, 1);
return v_val_4030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l_Lean_TSyntax_getName(v_s_4031_);
lean_dec(v_s_4031_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_4033_){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4034_ = lean_unsigned_to_nat(0u);
v___x_4035_ = l_Lean_Syntax_getArg(v_s_4033_, v___x_4034_);
v___x_4036_ = l_Lean_Syntax_getId(v___x_4035_);
lean_dec(v___x_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_TSyntax_getHygieneInfo(v_s_4037_);
lean_dec(v_s_4037_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_4039_, lean_object* v_a_4040_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Lean_Syntax_SepArray_ofElems(v_sep_4039_, v_a_4040_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_4042_, v_a_4043_);
lean_dec_ref(v_a_4043_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_4045_){
_start:
{
lean_object* v___f_4046_; 
v___f_4046_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4046_, 0, v_sep_4045_);
return v___f_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_4047_, lean_object* v_sep_4048_){
_start:
{
lean_object* v___f_4049_; 
v___f_4049_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4049_, 0, v_sep_4048_);
return v___f_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_4050_, lean_object* v_sep_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_4050_, v_sep_4051_);
lean_dec(v_k_4050_);
return v_res_4052_;
}
}
lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_4053_, lean_object* v_val_4054_, uint8_t v_canonical_4055_){
_start:
{
lean_object* v___x_4056_; lean_object* v_src_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v_imported_4060_; lean_object* v_ctx_4061_; lean_object* v_scopes_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4078_; 
v___x_4056_ = lean_unsigned_to_nat(0u);
v_src_4057_ = l_Lean_Syntax_getArg(v_s_4053_, v___x_4056_);
v___x_4058_ = l_Lean_Syntax_getId(v_src_4057_);
v___x_4059_ = l_Lean_extractMacroScopes(v___x_4058_);
v_imported_4060_ = lean_ctor_get(v___x_4059_, 1);
v_ctx_4061_ = lean_ctor_get(v___x_4059_, 2);
v_scopes_4062_ = lean_ctor_get(v___x_4059_, 3);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4078_ == 0)
{
lean_object* v_unused_4079_; 
v_unused_4079_ = lean_ctor_get(v___x_4059_, 0);
lean_dec(v_unused_4079_);
v___x_4064_ = v___x_4059_;
v_isShared_4065_ = v_isSharedCheck_4078_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_scopes_4062_);
lean_inc(v_ctx_4061_);
lean_inc(v_imported_4060_);
lean_dec(v___x_4059_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4078_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4066_; lean_object* v___x_4068_; 
v___x_4066_ = l_Lean_Name_eraseMacroScopes(v_val_4054_);
if (v_isShared_4065_ == 0)
{
lean_ctor_set(v___x_4064_, 0, v___x_4066_);
v___x_4068_ = v___x_4064_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_4066_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v_imported_4060_);
lean_ctor_set(v_reuseFailAlloc_4077_, 2, v_ctx_4061_);
lean_ctor_set(v_reuseFailAlloc_4077_, 3, v_scopes_4062_);
v___x_4068_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
lean_object* v_id_4069_; lean_object* v___x_4070_; uint8_t v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v_id_4069_ = l_Lean_MacroScopesView_review(v___x_4068_);
v___x_4070_ = l_Lean_SourceInfo_fromRef(v_src_4057_, v_canonical_4055_);
lean_dec(v_src_4057_);
v___x_4071_ = 1;
v___x_4072_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_4054_, v___x_4071_);
v___x_4073_ = lean_string_utf8_byte_size(v___x_4072_);
v___x_4074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4072_);
lean_ctor_set(v___x_4074_, 1, v___x_4056_);
lean_ctor_set(v___x_4074_, 2, v___x_4073_);
v___x_4075_ = lean_box(0);
v___x_4076_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4070_);
lean_ctor_set(v___x_4076_, 1, v___x_4074_);
lean_ctor_set(v___x_4076_, 2, v_id_4069_);
lean_ctor_set(v___x_4076_, 3, v___x_4075_);
return v___x_4076_;
}
}
}
}
LEAN_EXPORT void l_Lean_HygieneInfo_mkIdent_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4053_ = stack[0].m_obj;
lean_object* v_val_4054_ = stack[1].m_obj;
uint8_t v_canonical_4055_ = stack[2].m_num;
lean_object* v_res_4080_;
v_res_4080_ = l_Lean_HygieneInfo_mkIdent(v_s_4053_, v_val_4054_, v_canonical_4055_);
stack->m_obj
 = v_res_4080_;
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_4081_, lean_object* v_val_4082_, lean_object* v_canonical_4083_){
_start:
{
uint8_t v_canonical_boxed_4084_; lean_object* v_res_4085_; 
v_canonical_boxed_4084_ = lean_unbox(v_canonical_4083_);
v_res_4085_ = l_Lean_HygieneInfo_mkIdent(v_s_4081_, v_val_4082_, v_canonical_boxed_4084_);
lean_dec(v_s_4081_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_4086_, lean_object* v_inst_4087_, lean_object* v_a_4088_){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4089_ = lean_apply_1(v_inst_4086_, v_a_4088_);
v___x_4090_ = lean_apply_1(v_inst_4087_, v___x_4089_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_4091_, lean_object* v_inst_4092_){
_start:
{
lean_object* v___f_4093_; 
v___f_4093_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4093_, 0, v_inst_4091_);
lean_closure_set(v___f_4093_, 1, v_inst_4092_);
return v___f_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_4094_, lean_object* v_k_4095_, lean_object* v_k_x27_4096_, lean_object* v_inst_4097_, lean_object* v_inst_4098_){
_start:
{
lean_object* v___f_4099_; 
v___f_4099_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4099_, 0, v_inst_4097_);
lean_closure_set(v___f_4099_, 1, v_inst_4098_);
return v___f_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_4100_, lean_object* v_k_4101_, lean_object* v_k_x27_4102_, lean_object* v_inst_4103_, lean_object* v_inst_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_4100_, v_k_4101_, v_k_x27_4102_, v_inst_4103_, v_inst_4104_);
lean_dec(v_k_x27_4102_);
lean_dec(v_k_4101_);
return v_res_4105_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4113_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4114_ = l_Lean_mkCIdent(v___x_4113_);
return v___x_4114_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4119_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4120_ = l_Lean_mkCIdent(v___x_4119_);
return v___x_4120_;
}
}
lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4121_){
_start:
{
if (v_x_4121_ == 0)
{
lean_object* v___x_4122_; 
v___x_4122_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4122_;
}
else
{
lean_object* v___x_4123_; 
v___x_4123_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4123_;
}
}
}
LEAN_EXPORT void l_Lean_instQuoteBoolMkStr1___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_4121_ = stack[0].m_num;
lean_object* v_res_4124_;
v_res_4124_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_4121_);
stack->m_obj
 = v_res_4124_;
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4125_){
_start:
{
uint8_t v_x_85__boxed_4126_; lean_object* v_res_4127_; 
v_x_85__boxed_4126_ = lean_unbox(v_x_4125_);
v_res_4127_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4126_);
return v_res_4127_;
}
}
lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4130_){
_start:
{
lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4131_ = lean_box(2);
v___x_4132_ = l_Lean_Syntax_mkCharLit(v_val_4130_, v___x_4131_);
return v___x_4132_;
}
}
LEAN_EXPORT void l_Lean_instQuoteCharCharLitKind___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_val_4130_ = stack[0].m_num;
lean_object* v_res_4133_;
v_res_4133_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_4130_);
stack->m_obj
 = v_res_4133_;
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4134_){
_start:
{
uint32_t v_val_boxed_4135_; lean_object* v_res_4136_; 
v_val_boxed_4135_ = lean_unbox_uint32(v_val_4134_);
lean_dec(v_val_4134_);
v_res_4136_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4135_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4139_){
_start:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4140_ = lean_box(2);
v___x_4141_ = l_Lean_Syntax_mkStrLit(v_val_4139_, v___x_4140_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4144_){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4145_ = l_Nat_reprFast(v_n_4144_);
v___x_4146_ = lean_box(2);
v___x_4147_ = l_Lean_Syntax_mkNumLit(v___x_4145_, v___x_4146_);
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4155_){
_start:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4156_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4157_ = lean_substring_tostring(v_s_4155_);
v___x_4158_ = lean_box(2);
v___x_4159_ = l_Lean_Syntax_mkStrLit(v___x_4157_, v___x_4158_);
v___x_4160_ = lean_unsigned_to_nat(1u);
v___x_4161_ = lean_mk_empty_array_with_capacity(v___x_4160_);
v___x_4162_ = lean_array_push(v___x_4161_, v___x_4159_);
v___x_4163_ = l_Lean_Syntax_mkCApp(v___x_4156_, v___x_4162_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4166_, lean_object* v_x_4167_){
_start:
{
switch(lean_obj_tag(v_x_4167_))
{
case 0:
{
uint8_t v___x_4168_; 
v___x_4168_ = l_List_isEmpty___redArg(v_acc_4166_);
if (v___x_4168_ == 0)
{
lean_object* v___x_4169_; 
v___x_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4169_, 0, v_acc_4166_);
return v___x_4169_;
}
else
{
lean_object* v___x_4170_; 
lean_dec(v_acc_4166_);
v___x_4170_ = lean_box(0);
return v___x_4170_;
}
}
case 1:
{
lean_object* v_pre_4171_; lean_object* v_str_4172_; lean_object* v_val_4174_; lean_object* v___x_4177_; lean_object* v___x_4178_; uint8_t v___x_4179_; 
v_pre_4171_ = lean_ctor_get(v_x_4167_, 0);
lean_inc(v_pre_4171_);
v_str_4172_ = lean_ctor_get(v_x_4167_, 1);
lean_inc_ref(v_str_4172_);
lean_dec_ref_known(v_x_4167_, 2);
v___x_4177_ = lean_unsigned_to_nat(0u);
v___x_4178_ = lean_string_utf8_byte_size(v_str_4172_);
v___x_4179_ = lean_nat_dec_lt(v___x_4177_, v___x_4178_);
if (v___x_4179_ == 0)
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4180_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_4181_ = lean_string_append(v___x_4180_, v_str_4172_);
lean_dec_ref(v_str_4172_);
v___x_4182_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_4183_ = lean_string_append(v___x_4181_, v___x_4182_);
v_val_4174_ = v___x_4183_;
goto v___jp_4173_;
}
else
{
lean_object* v___f_4184_; uint8_t v___y_4186_; lean_object* v___f_4193_; uint32_t v___y_4200_; uint32_t v___y_4205_; uint8_t v_c_4219_; uint8_t v___x_4228_; uint8_t v___x_4229_; 
v___f_4184_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v___f_4193_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_4219_ = lean_string_get_byte_fast(v_str_4172_, v___x_4177_);
v___x_4228_ = 97;
v___x_4229_ = lean_uint8_dec_le(v___x_4228_, v_c_4219_);
if (v___x_4229_ == 0)
{
goto v___jp_4223_;
}
else
{
uint8_t v___x_4230_; uint8_t v___x_4231_; 
v___x_4230_ = 122;
v___x_4231_ = lean_uint8_dec_le(v_c_4219_, v___x_4230_);
if (v___x_4231_ == 0)
{
goto v___jp_4223_;
}
else
{
goto v___jp_4216_;
}
}
v___jp_4185_:
{
if (v___y_4186_ == 0)
{
uint8_t v___x_4187_; 
lean_inc_ref(v_str_4172_);
v___x_4187_ = lean_string_any(v_str_4172_, v___f_4184_);
if (v___x_4187_ == 0)
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4188_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_4189_ = lean_string_append(v___x_4188_, v_str_4172_);
lean_dec_ref(v_str_4172_);
v___x_4190_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_4191_ = lean_string_append(v___x_4189_, v___x_4190_);
v_val_4174_ = v___x_4191_;
goto v___jp_4173_;
}
else
{
lean_object* v___x_4192_; 
lean_dec_ref(v_str_4172_);
lean_dec(v_pre_4171_);
lean_dec(v_acc_4166_);
v___x_4192_ = lean_box(0);
return v___x_4192_;
}
}
else
{
v_val_4174_ = v_str_4172_;
goto v___jp_4173_;
}
}
v___jp_4194_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; 
lean_inc_ref(v_str_4172_);
v___x_4195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4195_, 0, v_str_4172_);
lean_ctor_set(v___x_4195_, 1, v___x_4177_);
lean_ctor_set(v___x_4195_, 2, v___x_4178_);
v___x_4196_ = lean_unsigned_to_nat(1u);
v___x_4197_ = lean_substring_drop(v___x_4195_, v___x_4196_);
v___x_4198_ = lean_substring_all(v___x_4197_, v___f_4193_);
v___y_4186_ = v___x_4198_;
goto v___jp_4185_;
}
v___jp_4199_:
{
uint32_t v___x_4201_; uint8_t v___x_4202_; 
v___x_4201_ = 95;
v___x_4202_ = lean_uint32_dec_eq(v___y_4200_, v___x_4201_);
if (v___x_4202_ == 0)
{
uint8_t v___x_4203_; 
v___x_4203_ = l_Lean_isLetterLike(v___y_4200_);
if (v___x_4203_ == 0)
{
v___y_4186_ = v___x_4203_;
goto v___jp_4185_;
}
else
{
goto v___jp_4194_;
}
}
else
{
goto v___jp_4194_;
}
}
v___jp_4204_:
{
uint32_t v___x_4206_; uint8_t v___x_4207_; 
v___x_4206_ = 97;
v___x_4207_ = lean_uint32_dec_le(v___x_4206_, v___y_4205_);
if (v___x_4207_ == 0)
{
v___y_4200_ = v___y_4205_;
goto v___jp_4199_;
}
else
{
uint32_t v___x_4208_; uint8_t v___x_4209_; 
v___x_4208_ = 122;
v___x_4209_ = lean_uint32_dec_le(v___y_4205_, v___x_4208_);
if (v___x_4209_ == 0)
{
v___y_4200_ = v___y_4205_;
goto v___jp_4199_;
}
else
{
goto v___jp_4194_;
}
}
}
v___jp_4210_:
{
uint32_t v___x_4211_; uint32_t v___x_4212_; uint8_t v___x_4213_; 
v___x_4211_ = lean_string_utf8_get(v_str_4172_, v___x_4177_);
v___x_4212_ = 65;
v___x_4213_ = lean_uint32_dec_le(v___x_4212_, v___x_4211_);
if (v___x_4213_ == 0)
{
v___y_4205_ = v___x_4211_;
goto v___jp_4204_;
}
else
{
uint32_t v___x_4214_; uint8_t v___x_4215_; 
v___x_4214_ = 90;
v___x_4215_ = lean_uint32_dec_le(v___x_4211_, v___x_4214_);
if (v___x_4215_ == 0)
{
v___y_4205_ = v___x_4211_;
goto v___jp_4204_;
}
else
{
goto v___jp_4194_;
}
}
}
v___jp_4216_:
{
lean_object* v___x_4217_; uint8_t v___x_4218_; 
v___x_4217_ = lean_unsigned_to_nat(1u);
v___x_4218_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4172_, v___x_4217_);
if (v___x_4218_ == 0)
{
goto v___jp_4210_;
}
else
{
v___y_4186_ = v___x_4218_;
goto v___jp_4185_;
}
}
v___jp_4220_:
{
uint8_t v___x_4221_; uint8_t v___x_4222_; 
v___x_4221_ = 95;
v___x_4222_ = lean_uint8_dec_eq(v_c_4219_, v___x_4221_);
if (v___x_4222_ == 0)
{
goto v___jp_4210_;
}
else
{
goto v___jp_4216_;
}
}
v___jp_4223_:
{
uint8_t v___x_4224_; uint8_t v___x_4225_; 
v___x_4224_ = 65;
v___x_4225_ = lean_uint8_dec_le(v___x_4224_, v_c_4219_);
if (v___x_4225_ == 0)
{
goto v___jp_4220_;
}
else
{
uint8_t v___x_4226_; uint8_t v___x_4227_; 
v___x_4226_ = 90;
v___x_4227_ = lean_uint8_dec_le(v_c_4219_, v___x_4226_);
if (v___x_4227_ == 0)
{
goto v___jp_4220_;
}
else
{
goto v___jp_4216_;
}
}
}
}
v___jp_4173_:
{
lean_object* v___x_4175_; 
v___x_4175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4175_, 0, v_val_4174_);
lean_ctor_set(v___x_4175_, 1, v_acc_4166_);
v_acc_4166_ = v___x_4175_;
v_x_4167_ = v_pre_4171_;
goto _start;
}
}
default: 
{
lean_object* v___x_4232_; 
lean_dec_ref_known(v_x_4167_, 2);
lean_dec(v_acc_4166_);
v___x_4232_ = lean_box(0);
return v___x_4232_;
}
}
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__3(void){
_start:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4239_ = ((lean_object*)(l_Lean_quoteNameMk___closed__2));
v___x_4240_ = l_Lean_mkCIdent(v___x_4239_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object* v_x_4251_){
_start:
{
switch(lean_obj_tag(v_x_4251_))
{
case 0:
{
lean_object* v___x_4252_; 
v___x_4252_ = lean_obj_once(&l_Lean_quoteNameMk___closed__3, &l_Lean_quoteNameMk___closed__3_once, _init_l_Lean_quoteNameMk___closed__3);
return v___x_4252_;
}
case 1:
{
lean_object* v_pre_4253_; lean_object* v_str_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v_pre_4253_ = lean_ctor_get(v_x_4251_, 0);
lean_inc(v_pre_4253_);
v_str_4254_ = lean_ctor_get(v_x_4251_, 1);
lean_inc_ref(v_str_4254_);
lean_dec_ref_known(v_x_4251_, 2);
v___x_4255_ = ((lean_object*)(l_Lean_quoteNameMk___closed__5));
v___x_4256_ = l_Lean_quoteNameMk(v_pre_4253_);
v___x_4257_ = lean_box(2);
v___x_4258_ = l_Lean_Syntax_mkStrLit(v_str_4254_, v___x_4257_);
v___x_4259_ = lean_unsigned_to_nat(2u);
v___x_4260_ = lean_mk_empty_array_with_capacity(v___x_4259_);
v___x_4261_ = lean_array_push(v___x_4260_, v___x_4256_);
v___x_4262_ = lean_array_push(v___x_4261_, v___x_4258_);
v___x_4263_ = l_Lean_Syntax_mkCApp(v___x_4255_, v___x_4262_);
return v___x_4263_;
}
default: 
{
lean_object* v_pre_4264_; lean_object* v_i_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v_pre_4264_ = lean_ctor_get(v_x_4251_, 0);
lean_inc(v_pre_4264_);
v_i_4265_ = lean_ctor_get(v_x_4251_, 1);
lean_inc(v_i_4265_);
lean_dec_ref_known(v_x_4251_, 2);
v___x_4266_ = ((lean_object*)(l_Lean_quoteNameMk___closed__7));
v___x_4267_ = l_Lean_quoteNameMk(v_pre_4264_);
v___x_4268_ = l_Nat_reprFast(v_i_4265_);
v___x_4269_ = lean_box(2);
v___x_4270_ = l_Lean_Syntax_mkNumLit(v___x_4268_, v___x_4269_);
v___x_4271_ = lean_unsigned_to_nat(2u);
v___x_4272_ = lean_mk_empty_array_with_capacity(v___x_4271_);
v___x_4273_ = lean_array_push(v___x_4272_, v___x_4267_);
v___x_4274_ = lean_array_push(v___x_4273_, v___x_4270_);
v___x_4275_ = l_Lean_Syntax_mkCApp(v___x_4266_, v___x_4274_);
return v___x_4275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object* v_n_4282_){
_start:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4283_ = lean_box(0);
lean_inc(v_n_4282_);
v___x_4284_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4283_, v_n_4282_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_object* v___x_4285_; 
v___x_4285_ = l_Lean_quoteNameMk(v_n_4282_);
return v___x_4285_;
}
else
{
lean_object* v_val_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; 
lean_dec(v_n_4282_);
v_val_4286_ = lean_ctor_get(v___x_4284_, 0);
lean_inc(v_val_4286_);
lean_dec_ref_known(v___x_4284_, 1);
v___x_4287_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4288_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4289_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4290_ = lean_string_intercalate(v___x_4289_, v_val_4286_);
v___x_4291_ = lean_string_append(v___x_4288_, v___x_4290_);
lean_dec_ref(v___x_4290_);
v___x_4292_ = lean_box(2);
v___x_4293_ = l_Lean_Syntax_mkNameLit(v___x_4291_, v___x_4292_);
v___x_4294_ = lean_unsigned_to_nat(1u);
v___x_4295_ = lean_mk_empty_array_with_capacity(v___x_4294_);
v___x_4296_ = lean_array_push(v___x_4295_, v___x_4293_);
v___x_4297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4292_);
lean_ctor_set(v___x_4297_, 1, v___x_4287_);
lean_ctor_set(v___x_4297_, 2, v___x_4296_);
return v___x_4297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object* v_n_4298_){
_start:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4299_ = lean_box(0);
lean_inc(v_n_4298_);
v___x_4300_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4299_, v_n_4298_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v___x_4301_; 
v___x_4301_ = l_Lean_quoteNameMk(v_n_4298_);
return v___x_4301_;
}
else
{
lean_object* v_val_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
lean_dec(v_n_4298_);
v_val_4302_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_val_4302_);
lean_dec_ref_known(v___x_4300_, 1);
v___x_4303_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4304_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4305_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4306_ = lean_string_intercalate(v___x_4305_, v_val_4302_);
v___x_4307_ = lean_string_append(v___x_4304_, v___x_4306_);
lean_dec_ref(v___x_4306_);
v___x_4308_ = lean_box(2);
v___x_4309_ = l_Lean_Syntax_mkNameLit(v___x_4307_, v___x_4308_);
v___x_4310_ = lean_unsigned_to_nat(1u);
v___x_4311_ = lean_mk_empty_array_with_capacity(v___x_4310_);
v___x_4312_ = lean_array_push(v___x_4311_, v___x_4309_);
v___x_4313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4308_);
lean_ctor_set(v___x_4313_, 1, v___x_4303_);
lean_ctor_set(v___x_4313_, 2, v___x_4312_);
return v___x_4313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object* v_inst_4321_, lean_object* v_inst_4322_, lean_object* v_x_4323_){
_start:
{
lean_object* v_fst_4324_; lean_object* v_snd_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v_fst_4324_ = lean_ctor_get(v_x_4323_, 0);
lean_inc(v_fst_4324_);
v_snd_4325_ = lean_ctor_get(v_x_4323_, 1);
lean_inc(v_snd_4325_);
lean_dec_ref(v_x_4323_);
v___x_4326_ = ((lean_object*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2));
v___x_4327_ = lean_apply_1(v_inst_4321_, v_fst_4324_);
v___x_4328_ = lean_apply_1(v_inst_4322_, v_snd_4325_);
v___x_4329_ = lean_unsigned_to_nat(2u);
v___x_4330_ = lean_mk_empty_array_with_capacity(v___x_4329_);
v___x_4331_ = lean_array_push(v___x_4330_, v___x_4327_);
v___x_4332_ = lean_array_push(v___x_4331_, v___x_4328_);
v___x_4333_ = l_Lean_Syntax_mkCApp(v___x_4326_, v___x_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object* v_inst_4334_, lean_object* v_inst_4335_){
_start:
{
lean_object* v___f_4336_; 
v___f_4336_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4336_, 0, v_inst_4334_);
lean_closure_set(v___f_4336_, 1, v_inst_4335_);
return v___f_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object* v_00_u03b1_4337_, lean_object* v_00_u03b2_4338_, lean_object* v_inst_4339_, lean_object* v_inst_4340_){
_start:
{
lean_object* v___f_4341_; 
v___f_4341_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4341_, 0, v_inst_4339_);
lean_closure_set(v___f_4341_, 1, v_inst_4340_);
return v___f_4341_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3(void){
_start:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4347_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2));
v___x_4348_ = l_Lean_mkCIdent(v___x_4347_);
return v___x_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object* v_inst_4353_, lean_object* v_x_4354_){
_start:
{
if (lean_obj_tag(v_x_4354_) == 0)
{
lean_object* v___x_4355_; 
lean_dec_ref(v_inst_4353_);
v___x_4355_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3);
return v___x_4355_;
}
else
{
lean_object* v_head_4356_; lean_object* v_tail_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v_head_4356_ = lean_ctor_get(v_x_4354_, 0);
lean_inc(v_head_4356_);
v_tail_4357_ = lean_ctor_get(v_x_4354_, 1);
lean_inc(v_tail_4357_);
lean_dec_ref_known(v_x_4354_, 2);
v___x_4358_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5));
lean_inc_ref(v_inst_4353_);
v___x_4359_ = lean_apply_1(v_inst_4353_, v_head_4356_);
v___x_4360_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4353_, v_tail_4357_);
v___x_4361_ = lean_unsigned_to_nat(2u);
v___x_4362_ = lean_mk_empty_array_with_capacity(v___x_4361_);
v___x_4363_ = lean_array_push(v___x_4362_, v___x_4359_);
v___x_4364_ = lean_array_push(v___x_4363_, v___x_4360_);
v___x_4365_ = l_Lean_Syntax_mkCApp(v___x_4358_, v___x_4364_);
return v___x_4365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object* v_00_u03b1_4366_, lean_object* v_inst_4367_, lean_object* v_x_4368_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4367_, v_x_4368_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object* v_inst_4370_, lean_object* v_a_4371_){
_start:
{
lean_object* v___x_4372_; 
v___x_4372_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4370_, v_a_4371_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object* v_00_u03b1_4373_, lean_object* v_inst_4374_, lean_object* v_a_4375_){
_start:
{
lean_object* v___x_4376_; 
v___x_4376_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4374_, v_a_4375_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object* v_inst_4377_){
_start:
{
lean_object* v___x_4378_; 
v___x_4378_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4378_, 0, lean_box(0));
lean_closure_set(v___x_4378_, 1, v_inst_4377_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object* v_00_u03b1_4379_, lean_object* v_inst_4380_){
_start:
{
lean_object* v___x_4381_; 
v___x_4381_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4381_, 0, lean_box(0));
lean_closure_set(v___x_4381_, 1, v_inst_4380_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object* v_inst_4384_, lean_object* v_xs_4385_, lean_object* v_i_4386_, lean_object* v_args_4387_){
_start:
{
lean_object* v___x_4388_; uint8_t v___x_4389_; 
v___x_4388_ = lean_array_get_size(v_xs_4385_);
v___x_4389_ = lean_nat_dec_lt(v_i_4386_, v___x_4388_);
if (v___x_4389_ == 0)
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
lean_dec(v_i_4386_);
lean_dec_ref(v_inst_4384_);
v___x_4390_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0));
v___x_4391_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1));
v___x_4392_ = l_Nat_reprFast(v___x_4388_);
v___x_4393_ = lean_string_append(v___x_4391_, v___x_4392_);
lean_dec_ref(v___x_4392_);
v___x_4394_ = l_Lean_Name_mkStr2(v___x_4390_, v___x_4393_);
v___x_4395_ = l_Lean_Syntax_mkCApp(v___x_4394_, v_args_4387_);
return v___x_4395_;
}
else
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4396_ = lean_unsigned_to_nat(1u);
v___x_4397_ = lean_nat_add(v_i_4386_, v___x_4396_);
v___x_4398_ = lean_array_fget_borrowed(v_xs_4385_, v_i_4386_);
lean_dec(v_i_4386_);
lean_inc_ref(v_inst_4384_);
lean_inc(v___x_4398_);
v___x_4399_ = lean_apply_1(v_inst_4384_, v___x_4398_);
v___x_4400_ = lean_array_push(v_args_4387_, v___x_4399_);
v_i_4386_ = v___x_4397_;
v_args_4387_ = v___x_4400_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object* v_inst_4402_, lean_object* v_xs_4403_, lean_object* v_i_4404_, lean_object* v_args_4405_){
_start:
{
lean_object* v_res_4406_; 
v_res_4406_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4402_, v_xs_4403_, v_i_4404_, v_args_4405_);
lean_dec_ref(v_xs_4403_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object* v_00_u03b1_4407_, lean_object* v_inst_4408_, lean_object* v_xs_4409_, lean_object* v_i_4410_, lean_object* v_args_4411_){
_start:
{
lean_object* v___x_4412_; 
v___x_4412_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4408_, v_xs_4409_, v_i_4410_, v_args_4411_);
return v___x_4412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object* v_00_u03b1_4413_, lean_object* v_inst_4414_, lean_object* v_xs_4415_, lean_object* v_i_4416_, lean_object* v_args_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go(v_00_u03b1_4413_, v_inst_4414_, v_xs_4415_, v_i_4416_, v_args_4417_);
lean_dec_ref(v_xs_4415_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object* v_inst_4423_, lean_object* v_xs_4424_){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; uint8_t v___x_4427_; 
v___x_4425_ = lean_array_get_size(v_xs_4424_);
v___x_4426_ = lean_unsigned_to_nat(8u);
v___x_4427_ = lean_nat_dec_le(v___x_4425_, v___x_4426_);
if (v___x_4427_ == 0)
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4428_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1));
v___x_4429_ = lean_array_to_list(v_xs_4424_);
v___x_4430_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4423_, v___x_4429_);
v___x_4431_ = lean_unsigned_to_nat(1u);
v___x_4432_ = lean_mk_empty_array_with_capacity(v___x_4431_);
v___x_4433_ = lean_array_push(v___x_4432_, v___x_4430_);
v___x_4434_ = l_Lean_Syntax_mkCApp(v___x_4428_, v___x_4433_);
return v___x_4434_;
}
else
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4435_ = lean_unsigned_to_nat(0u);
v___x_4436_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4437_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4423_, v_xs_4424_, v___x_4435_, v___x_4436_);
lean_dec_ref(v_xs_4424_);
return v___x_4437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object* v_00_u03b1_4438_, lean_object* v_inst_4439_, lean_object* v_xs_4440_){
_start:
{
lean_object* v___x_4441_; 
v___x_4441_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4439_, v_xs_4440_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object* v_inst_4442_, lean_object* v_xs_4443_){
_start:
{
lean_object* v___x_4444_; 
v___x_4444_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4442_, v_xs_4443_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object* v_00_u03b1_4445_, lean_object* v_inst_4446_, lean_object* v_xs_4447_){
_start:
{
lean_object* v___x_4448_; 
v___x_4448_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4446_, v_xs_4447_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object* v_inst_4449_){
_start:
{
lean_object* v___x_4450_; 
v___x_4450_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4450_, 0, lean_box(0));
lean_closure_set(v___x_4450_, 1, v_inst_4449_);
return v___x_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object* v_00_u03b1_4451_, lean_object* v_inst_4452_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4453_, 0, lean_box(0));
lean_closure_set(v___x_4453_, 1, v_inst_4452_);
return v___x_4453_;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4459_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__2));
v___x_4460_ = l_Lean_mkIdent(v___x_4459_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object* v_inst_4465_, lean_object* v_x_4466_){
_start:
{
if (lean_obj_tag(v_x_4466_) == 0)
{
lean_object* v___x_4467_; 
lean_dec_ref(v_inst_4465_);
v___x_4467_ = lean_obj_once(&l_Lean_Option_hasQuote___redArg___lam__0___closed__3, &l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once, _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3);
return v___x_4467_;
}
else
{
lean_object* v_val_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v_val_4468_ = lean_ctor_get(v_x_4466_, 0);
lean_inc(v_val_4468_);
lean_dec_ref_known(v_x_4466_, 1);
v___x_4469_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__5));
v___x_4470_ = lean_apply_1(v_inst_4465_, v_val_4468_);
v___x_4471_ = lean_unsigned_to_nat(1u);
v___x_4472_ = lean_mk_empty_array_with_capacity(v___x_4471_);
v___x_4473_ = lean_array_push(v___x_4472_, v___x_4470_);
v___x_4474_ = l_Lean_Syntax_mkCApp(v___x_4469_, v___x_4473_);
return v___x_4474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object* v_inst_4475_){
_start:
{
lean_object* v___f_4476_; 
v___f_4476_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4476_, 0, v_inst_4475_);
return v___f_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object* v_00_u03b1_4477_, lean_object* v_inst_4478_){
_start:
{
lean_object* v___f_4479_; 
v___f_4479_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4479_, 0, v_inst_4478_);
return v___f_4479_;
}
}
uint8_t l_Lean_evalPrec___lam__0(uint8_t v___x_4480_, lean_object* v_k_4481_){
_start:
{
lean_object* v___x_4482_; uint8_t v___x_4483_; 
v___x_4482_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_4483_ = lean_name_eq(v_k_4481_, v___x_4482_);
if (v___x_4483_ == 0)
{
uint8_t v___x_4484_; 
v___x_4484_ = 1;
return v___x_4484_;
}
else
{
return v___x_4480_;
}
}
}
LEAN_EXPORT void l_Lean_evalPrec___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_4480_ = stack[0].m_num;
lean_object* v_k_4481_ = stack[1].m_obj;
uint8_t v_res_4485_;
v_res_4485_ = l_Lean_evalPrec___lam__0(v___x_4480_, v_k_4481_);
stack->m_num = v_res_4485_;
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v___x_4486_, lean_object* v_k_4487_){
_start:
{
uint8_t v___x_442__boxed_4488_; uint8_t v_res_4489_; lean_object* v_r_4490_; 
v___x_442__boxed_4488_ = lean_unbox(v___x_4486_);
v_res_4489_ = l_Lean_evalPrec___lam__0(v___x_442__boxed_4488_, v_k_4487_);
lean_dec(v_k_4487_);
v_r_4490_ = lean_box(v_res_4489_);
return v_r_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_){
_start:
{
lean_object* v_methods_4495_; lean_object* v_quotContext_4496_; lean_object* v_currMacroScope_4497_; lean_object* v_currRecDepth_4498_; lean_object* v_maxRecDepth_4499_; lean_object* v_ref_4500_; uint8_t v___x_4501_; 
v_methods_4495_ = lean_ctor_get(v_a_4493_, 0);
v_quotContext_4496_ = lean_ctor_get(v_a_4493_, 1);
v_currMacroScope_4497_ = lean_ctor_get(v_a_4493_, 2);
v_currRecDepth_4498_ = lean_ctor_get(v_a_4493_, 3);
v_maxRecDepth_4499_ = lean_ctor_get(v_a_4493_, 4);
v_ref_4500_ = lean_ctor_get(v_a_4493_, 5);
v___x_4501_ = lean_nat_dec_eq(v_currRecDepth_4498_, v_maxRecDepth_4499_);
if (v___x_4501_ == 0)
{
lean_object* v___x_4502_; lean_object* v___f_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4502_ = lean_box(v___x_4501_);
v___f_4503_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4503_, 0, v___x_4502_);
v___x_4504_ = lean_unsigned_to_nat(1u);
v___x_4505_ = lean_nat_add(v_currRecDepth_4498_, v___x_4504_);
lean_inc(v_ref_4500_);
lean_inc(v_maxRecDepth_4499_);
lean_inc(v_currMacroScope_4497_);
lean_inc(v_quotContext_4496_);
lean_inc(v_methods_4495_);
v___x_4506_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4506_, 0, v_methods_4495_);
lean_ctor_set(v___x_4506_, 1, v_quotContext_4496_);
lean_ctor_set(v___x_4506_, 2, v_currMacroScope_4497_);
lean_ctor_set(v___x_4506_, 3, v___x_4505_);
lean_ctor_set(v___x_4506_, 4, v_maxRecDepth_4499_);
lean_ctor_set(v___x_4506_, 5, v_ref_4500_);
lean_inc_ref(v___x_4506_);
v___x_4507_ = l_Lean_expandMacros(v_stx_4492_, v___f_4503_, v___x_4506_, v_a_4494_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v_a_4508_; lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4521_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
v_a_4509_ = lean_ctor_get(v___x_4507_, 1);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4511_ = v___x_4507_;
v_isShared_4512_ = v_isSharedCheck_4521_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_inc(v_a_4508_);
lean_dec(v___x_4507_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4521_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4513_; uint8_t v___x_4514_; 
v___x_4513_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4508_);
v___x_4514_ = l_Lean_Syntax_isOfKind(v_a_4508_, v___x_4513_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
lean_del_object(v___x_4511_);
v___x_4515_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4516_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4508_, v___x_4515_, v___x_4506_, v_a_4509_);
lean_dec_ref_known(v___x_4506_, 6);
lean_dec(v_a_4508_);
return v___x_4516_;
}
else
{
lean_object* v___x_4517_; lean_object* v___x_4519_; 
lean_dec_ref_known(v___x_4506_, 6);
v___x_4517_ = l_Lean_TSyntax_getNat(v_a_4508_);
lean_dec(v_a_4508_);
if (v_isShared_4512_ == 0)
{
lean_ctor_set(v___x_4511_, 0, v___x_4517_);
v___x_4519_ = v___x_4511_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v___x_4517_);
lean_ctor_set(v_reuseFailAlloc_4520_, 1, v_a_4509_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
}
else
{
lean_object* v_a_4522_; lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
lean_dec_ref_known(v___x_4506_, 6);
v_a_4522_ = lean_ctor_get(v___x_4507_, 0);
v_a_4523_ = lean_ctor_get(v___x_4507_, 1);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4507_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_inc(v_a_4522_);
lean_dec(v___x_4507_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4522_);
lean_ctor_set(v_reuseFailAlloc_4529_, 1, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
}
else
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4531_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4532_, 0, v_stx_4492_);
lean_ctor_set(v___x_4532_, 1, v___x_4531_);
v___x_4533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4532_);
lean_ctor_set(v___x_4533_, 1, v_a_4494_);
return v___x_4533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object* v_stx_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Lean_evalPrec(v_stx_4534_, v_a_4535_, v_a_4536_);
lean_dec_ref(v_a_4535_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_){
_start:
{
lean_object* v_methods_4542_; lean_object* v_quotContext_4543_; lean_object* v_currMacroScope_4544_; lean_object* v_currRecDepth_4545_; lean_object* v_maxRecDepth_4546_; lean_object* v_ref_4547_; uint8_t v___x_4548_; 
v_methods_4542_ = lean_ctor_get(v_a_4540_, 0);
v_quotContext_4543_ = lean_ctor_get(v_a_4540_, 1);
v_currMacroScope_4544_ = lean_ctor_get(v_a_4540_, 2);
v_currRecDepth_4545_ = lean_ctor_get(v_a_4540_, 3);
v_maxRecDepth_4546_ = lean_ctor_get(v_a_4540_, 4);
v_ref_4547_ = lean_ctor_get(v_a_4540_, 5);
v___x_4548_ = lean_nat_dec_eq(v_currRecDepth_4545_, v_maxRecDepth_4546_);
if (v___x_4548_ == 0)
{
lean_object* v___x_4549_; lean_object* v___f_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4549_ = lean_box(v___x_4548_);
v___f_4550_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4550_, 0, v___x_4549_);
v___x_4551_ = lean_unsigned_to_nat(1u);
v___x_4552_ = lean_nat_add(v_currRecDepth_4545_, v___x_4551_);
lean_inc(v_ref_4547_);
lean_inc(v_maxRecDepth_4546_);
lean_inc(v_currMacroScope_4544_);
lean_inc(v_quotContext_4543_);
lean_inc(v_methods_4542_);
v___x_4553_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4553_, 0, v_methods_4542_);
lean_ctor_set(v___x_4553_, 1, v_quotContext_4543_);
lean_ctor_set(v___x_4553_, 2, v_currMacroScope_4544_);
lean_ctor_set(v___x_4553_, 3, v___x_4552_);
lean_ctor_set(v___x_4553_, 4, v_maxRecDepth_4546_);
lean_ctor_set(v___x_4553_, 5, v_ref_4547_);
lean_inc_ref(v___x_4553_);
v___x_4554_ = l_Lean_expandMacros(v_stx_4539_, v___f_4550_, v___x_4553_, v_a_4541_);
if (lean_obj_tag(v___x_4554_) == 0)
{
lean_object* v_a_4555_; lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4568_; 
v_a_4555_ = lean_ctor_get(v___x_4554_, 0);
v_a_4556_ = lean_ctor_get(v___x_4554_, 1);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4554_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4558_ = v___x_4554_;
v_isShared_4559_ = v_isSharedCheck_4568_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_inc(v_a_4555_);
lean_dec(v___x_4554_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4568_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4560_; uint8_t v___x_4561_; 
v___x_4560_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4555_);
v___x_4561_ = l_Lean_Syntax_isOfKind(v_a_4555_, v___x_4560_);
if (v___x_4561_ == 0)
{
lean_object* v___x_4562_; lean_object* v___x_4563_; 
lean_del_object(v___x_4558_);
v___x_4562_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
v___x_4563_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4555_, v___x_4562_, v___x_4553_, v_a_4556_);
lean_dec_ref_known(v___x_4553_, 6);
lean_dec(v_a_4555_);
return v___x_4563_;
}
else
{
lean_object* v___x_4564_; lean_object* v___x_4566_; 
lean_dec_ref_known(v___x_4553_, 6);
v___x_4564_ = l_Lean_TSyntax_getNat(v_a_4555_);
lean_dec(v_a_4555_);
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 0, v___x_4564_);
v___x_4566_ = v___x_4558_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v___x_4564_);
lean_ctor_set(v_reuseFailAlloc_4567_, 1, v_a_4556_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
}
else
{
lean_object* v_a_4569_; lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
lean_dec_ref_known(v___x_4553_, 6);
v_a_4569_ = lean_ctor_get(v___x_4554_, 0);
v_a_4570_ = lean_ctor_get(v___x_4554_, 1);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4554_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4572_ = v___x_4554_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_inc(v_a_4569_);
lean_dec(v___x_4554_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4575_; 
if (v_isShared_4573_ == 0)
{
v___x_4575_ = v___x_4572_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4569_);
lean_ctor_set(v_reuseFailAlloc_4576_, 1, v_a_4570_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
}
else
{
lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4578_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4579_, 0, v_stx_4539_);
lean_ctor_set(v___x_4579_, 1, v___x_4578_);
v___x_4580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
lean_ctor_set(v___x_4580_, 1, v_a_4541_);
return v___x_4580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object* v_stx_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l_Lean_evalPrio(v_stx_4581_, v_a_4582_, v_a_4583_);
lean_dec_ref(v_a_4582_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_){
_start:
{
if (lean_obj_tag(v_x_4585_) == 0)
{
lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4588_ = lean_unsigned_to_nat(1000u);
v___x_4589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
lean_ctor_set(v___x_4589_, 1, v_a_4587_);
return v___x_4589_;
}
else
{
lean_object* v_val_4590_; lean_object* v___x_4591_; 
v_val_4590_ = lean_ctor_get(v_x_4585_, 0);
lean_inc(v_val_4590_);
lean_dec_ref_known(v_x_4585_, 1);
v___x_4591_ = l_Lean_evalPrio(v_val_4590_, v_a_4586_, v_a_4587_);
return v___x_4591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object* v_x_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l_Lean_evalOptPrio(v_x_4592_, v_a_4593_, v_a_4594_);
lean_dec_ref(v_a_4593_);
return v_res_4595_;
}
}
lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4596_, lean_object* v_x1_4597_, lean_object* v_x2_4598_){
_start:
{
lean_object* v_fst_4599_; uint8_t v___x_4600_; 
v_fst_4599_ = lean_ctor_get(v_x1_4597_, 0);
v___x_4600_ = lean_unbox(v_fst_4599_);
if (v___x_4600_ == 0)
{
lean_object* v_snd_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4609_; 
lean_dec(v_x2_4598_);
v_snd_4601_ = lean_ctor_get(v_x1_4597_, 1);
v_isSharedCheck_4609_ = !lean_is_exclusive(v_x1_4597_);
if (v_isSharedCheck_4609_ == 0)
{
lean_object* v_unused_4610_; 
v_unused_4610_ = lean_ctor_get(v_x1_4597_, 0);
lean_dec(v_unused_4610_);
v___x_4603_ = v_x1_4597_;
v_isShared_4604_ = v_isSharedCheck_4609_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_snd_4601_);
lean_dec(v_x1_4597_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4609_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4605_; lean_object* v___x_4607_; 
v___x_4605_ = lean_box(v___x_4596_);
if (v_isShared_4604_ == 0)
{
lean_ctor_set(v___x_4603_, 0, v___x_4605_);
v___x_4607_ = v___x_4603_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4605_);
lean_ctor_set(v_reuseFailAlloc_4608_, 1, v_snd_4601_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
}
else
{
lean_object* v_snd_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4621_; 
v_snd_4611_ = lean_ctor_get(v_x1_4597_, 1);
v_isSharedCheck_4621_ = !lean_is_exclusive(v_x1_4597_);
if (v_isSharedCheck_4621_ == 0)
{
lean_object* v_unused_4622_; 
v_unused_4622_ = lean_ctor_get(v_x1_4597_, 0);
lean_dec(v_unused_4622_);
v___x_4613_ = v_x1_4597_;
v_isShared_4614_ = v_isSharedCheck_4621_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_snd_4611_);
lean_dec(v_x1_4597_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4621_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
uint8_t v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4619_; 
v___x_4615_ = 0;
v___x_4616_ = lean_array_push(v_snd_4611_, v_x2_4598_);
v___x_4617_ = lean_box(v___x_4615_);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 1, v___x_4616_);
lean_ctor_set(v___x_4613_, 0, v___x_4617_);
v___x_4619_ = v___x_4613_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4617_);
lean_ctor_set(v_reuseFailAlloc_4620_, 1, v___x_4616_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
}
}
LEAN_EXPORT void l_Array_getSepElems___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_4596_ = stack[0].m_num;
lean_object* v_x1_4597_ = stack[1].m_obj;
lean_object* v_x2_4598_ = stack[2].m_obj;
lean_object* v_res_4623_;
v_res_4623_ = l_Array_getSepElems___redArg___lam__0(v___x_4596_, v_x1_4597_, v_x2_4598_);
stack->m_obj
 = v_res_4623_;
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4624_, lean_object* v_x1_4625_, lean_object* v_x2_4626_){
_start:
{
uint8_t v___x_87__boxed_4627_; lean_object* v_res_4628_; 
v___x_87__boxed_4627_ = lean_unbox(v___x_4624_);
v_res_4628_ = l_Array_getSepElems___redArg___lam__0(v___x_87__boxed_4627_, v_x1_4625_, v_x2_4626_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4650_){
_start:
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; uint8_t v___x_4655_; 
v___x_4651_ = lean_unsigned_to_nat(0u);
v___x_4652_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4653_ = lean_array_get_size(v_as_4650_);
v___x_4654_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4655_ = lean_nat_dec_lt(v___x_4651_, v___x_4653_);
if (v___x_4655_ == 0)
{
lean_dec_ref(v_as_4650_);
return v___x_4652_;
}
else
{
lean_object* v___x_4656_; lean_object* v___f_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; size_t v___x_4660_; size_t v___x_4661_; lean_object* v___x_4662_; lean_object* v_snd_4663_; 
v___x_4656_ = lean_box(v___x_4655_);
v___f_4657_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4657_, 0, v___x_4656_);
v___x_4658_ = lean_box(v___x_4655_);
v___x_4659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4658_);
lean_ctor_set(v___x_4659_, 1, v___x_4652_);
v___x_4660_ = ((size_t)0ULL);
v___x_4661_ = lean_usize_of_nat(v___x_4653_);
v___x_4662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4654_, v___f_4657_, v_as_4650_, v___x_4660_, v___x_4661_, v___x_4659_);
v_snd_4663_ = lean_ctor_get(v___x_4662_, 1);
lean_inc(v_snd_4663_);
lean_dec(v___x_4662_);
return v_snd_4663_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4664_, lean_object* v_as_4665_){
_start:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; uint8_t v___x_4670_; 
v___x_4666_ = lean_unsigned_to_nat(0u);
v___x_4667_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4668_ = lean_array_get_size(v_as_4665_);
v___x_4669_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4670_ = lean_nat_dec_lt(v___x_4666_, v___x_4668_);
if (v___x_4670_ == 0)
{
lean_dec_ref(v_as_4665_);
return v___x_4667_;
}
else
{
lean_object* v___x_4671_; lean_object* v___f_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; size_t v___x_4675_; size_t v___x_4676_; lean_object* v___x_4677_; lean_object* v_snd_4678_; 
v___x_4671_ = lean_box(v___x_4670_);
v___f_4672_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4672_, 0, v___x_4671_);
v___x_4673_ = lean_box(v___x_4670_);
v___x_4674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4673_);
lean_ctor_set(v___x_4674_, 1, v___x_4667_);
v___x_4675_ = ((size_t)0ULL);
v___x_4676_ = lean_usize_of_nat(v___x_4668_);
v___x_4677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4669_, v___f_4672_, v_as_4665_, v___x_4675_, v___x_4676_, v___x_4674_);
v_snd_4678_ = lean_ctor_get(v___x_4677_, 1);
lean_inc(v_snd_4678_);
lean_dec(v___x_4677_);
return v_snd_4678_;
}
}
}
lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4679_, lean_object* v_inst_4680_, lean_object* v_a_4681_, lean_object* v_p_4682_, lean_object* v_acc_4683_, lean_object* v_stx_4684_, uint8_t v_____do__lift_4685_){
_start:
{
if (v_____do__lift_4685_ == 0)
{
lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
lean_dec(v_stx_4684_);
v___x_4694_ = lean_unsigned_to_nat(2u);
v___x_4695_ = lean_nat_add(v_i_4679_, v___x_4694_);
v___x_4696_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4680_, v_a_4681_, v_p_4682_, v___x_4695_, v_acc_4683_);
return v___x_4696_;
}
else
{
lean_object* v___x_4697_; lean_object* v___x_4698_; uint8_t v___x_4699_; 
v___x_4697_ = lean_array_get_size(v_acc_4683_);
v___x_4698_ = lean_unsigned_to_nat(0u);
v___x_4699_ = lean_nat_dec_eq(v___x_4697_, v___x_4698_);
if (v___x_4699_ == 0)
{
uint8_t v___x_4700_; 
v___x_4700_ = lean_nat_dec_eq(v_i_4679_, v___x_4698_);
if (v___x_4700_ == 0)
{
goto v___jp_4686_;
}
else
{
if (v___x_4699_ == 0)
{
lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4701_ = lean_unsigned_to_nat(2u);
v___x_4702_ = lean_nat_add(v_i_4679_, v___x_4701_);
v___x_4703_ = lean_array_push(v_acc_4683_, v_stx_4684_);
v___x_4704_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4680_, v_a_4681_, v_p_4682_, v___x_4702_, v___x_4703_);
return v___x_4704_;
}
else
{
goto v___jp_4686_;
}
}
}
else
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4705_ = lean_unsigned_to_nat(2u);
v___x_4706_ = lean_nat_add(v_i_4679_, v___x_4705_);
v___x_4707_ = lean_array_push(v_acc_4683_, v_stx_4684_);
v___x_4708_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4680_, v_a_4681_, v_p_4682_, v___x_4706_, v___x_4707_);
return v___x_4708_;
}
}
v___jp_4686_:
{
lean_object* v___x_4687_; lean_object* v_sepStx_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4687_ = lean_nat_pred(v_i_4679_);
v_sepStx_4688_ = lean_array_fget_borrowed(v_a_4681_, v___x_4687_);
lean_dec(v___x_4687_);
v___x_4689_ = lean_unsigned_to_nat(2u);
v___x_4690_ = lean_nat_add(v_i_4679_, v___x_4689_);
lean_inc(v_sepStx_4688_);
v___x_4691_ = lean_array_push(v_acc_4683_, v_sepStx_4688_);
v___x_4692_ = lean_array_push(v___x_4691_, v_stx_4684_);
v___x_4693_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4680_, v_a_4681_, v_p_4682_, v___x_4690_, v___x_4692_);
return v___x_4693_;
}
}
}
LEAN_EXPORT void l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_4679_ = stack[0].m_obj;
lean_object* v_inst_4680_ = stack[1].m_obj;
lean_object* v_a_4681_ = stack[2].m_obj;
lean_object* v_p_4682_ = stack[3].m_obj;
lean_object* v_acc_4683_ = stack[4].m_obj;
lean_object* v_stx_4684_ = stack[5].m_obj;
uint8_t v_____do__lift_4685_ = stack[6].m_num;
lean_object* v_res_4709_;
v_res_4709_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4679_, v_inst_4680_, v_a_4681_, v_p_4682_, v_acc_4683_, v_stx_4684_, v_____do__lift_4685_);
stack->m_obj
 = v_res_4709_;
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4710_, lean_object* v_inst_4711_, lean_object* v_a_4712_, lean_object* v_p_4713_, lean_object* v_acc_4714_, lean_object* v_stx_4715_, lean_object* v_____do__lift_4716_){
_start:
{
uint8_t v_____do__lift_208__boxed_4717_; lean_object* v_res_4718_; 
v_____do__lift_208__boxed_4717_ = lean_unbox(v_____do__lift_4716_);
v_res_4718_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4710_, v_inst_4711_, v_a_4712_, v_p_4713_, v_acc_4714_, v_stx_4715_, v_____do__lift_208__boxed_4717_);
lean_dec(v_i_4710_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4719_, lean_object* v_a_4720_, lean_object* v_p_4721_, lean_object* v_i_4722_, lean_object* v_acc_4723_){
_start:
{
lean_object* v_toApplicative_4724_; lean_object* v_toBind_4725_; lean_object* v_toPure_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; 
v_toApplicative_4724_ = lean_ctor_get(v_inst_4719_, 0);
v_toBind_4725_ = lean_ctor_get(v_inst_4719_, 1);
lean_inc(v_toBind_4725_);
v_toPure_4726_ = lean_ctor_get(v_toApplicative_4724_, 1);
v___x_4727_ = lean_array_get_size(v_a_4720_);
v___x_4728_ = lean_nat_dec_lt(v_i_4722_, v___x_4727_);
if (v___x_4728_ == 0)
{
lean_object* v___x_4729_; 
lean_inc(v_toPure_4726_);
lean_dec(v_toBind_4725_);
lean_dec(v_i_4722_);
lean_dec(v_p_4721_);
lean_dec_ref(v_a_4720_);
lean_dec_ref(v_inst_4719_);
v___x_4729_ = lean_apply_2(v_toPure_4726_, lean_box(0), v_acc_4723_);
return v___x_4729_;
}
else
{
lean_object* v_stx_4730_; lean_object* v___f_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
v_stx_4730_ = lean_array_fget(v_a_4720_, v_i_4722_);
lean_inc(v_stx_4730_);
lean_inc(v_p_4721_);
v___f_4731_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4731_, 0, v_i_4722_);
lean_closure_set(v___f_4731_, 1, v_inst_4719_);
lean_closure_set(v___f_4731_, 2, v_a_4720_);
lean_closure_set(v___f_4731_, 3, v_p_4721_);
lean_closure_set(v___f_4731_, 4, v_acc_4723_);
lean_closure_set(v___f_4731_, 5, v_stx_4730_);
v___x_4732_ = lean_apply_1(v_p_4721_, v_stx_4730_);
v___x_4733_ = lean_apply_4(v_toBind_4725_, lean_box(0), lean_box(0), v___x_4732_, v___f_4731_);
return v___x_4733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4734_, lean_object* v_inst_4735_, lean_object* v_a_4736_, lean_object* v_p_4737_, lean_object* v_i_4738_, lean_object* v_acc_4739_){
_start:
{
lean_object* v___x_4740_; 
v___x_4740_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4735_, v_a_4736_, v_p_4737_, v_i_4738_, v_acc_4739_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4741_, lean_object* v_a_4742_, lean_object* v_p_4743_){
_start:
{
lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; 
v___x_4744_ = lean_unsigned_to_nat(0u);
v___x_4745_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4746_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4741_, v_a_4742_, v_p_4743_, v___x_4744_, v___x_4745_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4747_, lean_object* v_inst_4748_, lean_object* v_a_4749_, lean_object* v_p_4750_){
_start:
{
lean_object* v___x_4751_; 
v___x_4751_ = l_Array_filterSepElemsM___redArg(v_inst_4748_, v_a_4749_, v_p_4750_);
return v___x_4751_;
}
}
uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4752_, lean_object* v_x_4753_){
_start:
{
lean_object* v___x_4754_; uint8_t v___x_4755_; 
v___x_4754_ = lean_apply_1(v_p_4752_, v_x_4753_);
v___x_4755_ = lean_unbox(v___x_4754_);
return v___x_4755_;
}
}
LEAN_EXPORT void l_Array_filterSepElems___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_4752_ = stack[0].m_obj;
lean_object* v_x_4753_ = stack[1].m_obj;
uint8_t v_res_4756_;
v_res_4756_ = l_Array_filterSepElems___lam__0(v_p_4752_, v_x_4753_);
stack->m_num = v_res_4756_;
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4757_, lean_object* v_x_4758_){
_start:
{
uint8_t v_res_4759_; lean_object* v_r_4760_; 
v_res_4759_ = l_Array_filterSepElems___lam__0(v_p_4757_, v_x_4758_);
v_r_4760_ = lean_box(v_res_4759_);
return v_r_4760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4761_, lean_object* v_p_4762_, lean_object* v_i_4763_, lean_object* v_acc_4764_){
_start:
{
lean_object* v___x_4765_; uint8_t v___x_4766_; 
v___x_4765_ = lean_array_get_size(v_a_4761_);
v___x_4766_ = lean_nat_dec_lt(v_i_4763_, v___x_4765_);
if (v___x_4766_ == 0)
{
lean_dec(v_i_4763_);
lean_dec_ref(v_p_4762_);
return v_acc_4764_;
}
else
{
lean_object* v_stx_4767_; lean_object* v___x_4776_; uint8_t v___x_4777_; 
v_stx_4767_ = lean_array_fget_borrowed(v_a_4761_, v_i_4763_);
lean_inc_ref(v_p_4762_);
lean_inc(v_stx_4767_);
v___x_4776_ = lean_apply_1(v_p_4762_, v_stx_4767_);
v___x_4777_ = lean_unbox(v___x_4776_);
if (v___x_4777_ == 0)
{
lean_object* v___x_4778_; lean_object* v___x_4779_; 
v___x_4778_ = lean_unsigned_to_nat(2u);
v___x_4779_ = lean_nat_add(v_i_4763_, v___x_4778_);
lean_dec(v_i_4763_);
v_i_4763_ = v___x_4779_;
goto _start;
}
else
{
lean_object* v___x_4781_; lean_object* v___x_4782_; uint8_t v___x_4783_; 
v___x_4781_ = lean_array_get_size(v_acc_4764_);
v___x_4782_ = lean_unsigned_to_nat(0u);
v___x_4783_ = lean_nat_dec_eq(v___x_4781_, v___x_4782_);
if (v___x_4783_ == 0)
{
uint8_t v___x_4784_; 
v___x_4784_ = lean_nat_dec_eq(v_i_4763_, v___x_4782_);
if (v___x_4784_ == 0)
{
goto v___jp_4768_;
}
else
{
if (v___x_4783_ == 0)
{
lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4785_ = lean_unsigned_to_nat(2u);
v___x_4786_ = lean_nat_add(v_i_4763_, v___x_4785_);
lean_dec(v_i_4763_);
lean_inc(v_stx_4767_);
v___x_4787_ = lean_array_push(v_acc_4764_, v_stx_4767_);
v_i_4763_ = v___x_4786_;
v_acc_4764_ = v___x_4787_;
goto _start;
}
else
{
goto v___jp_4768_;
}
}
}
else
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4789_ = lean_unsigned_to_nat(2u);
v___x_4790_ = lean_nat_add(v_i_4763_, v___x_4789_);
lean_dec(v_i_4763_);
lean_inc(v_stx_4767_);
v___x_4791_ = lean_array_push(v_acc_4764_, v_stx_4767_);
v_i_4763_ = v___x_4790_;
v_acc_4764_ = v___x_4791_;
goto _start;
}
}
v___jp_4768_:
{
lean_object* v___x_4769_; lean_object* v_sepStx_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4769_ = lean_nat_pred(v_i_4763_);
v_sepStx_4770_ = lean_array_fget_borrowed(v_a_4761_, v___x_4769_);
lean_dec(v___x_4769_);
v___x_4771_ = lean_unsigned_to_nat(2u);
v___x_4772_ = lean_nat_add(v_i_4763_, v___x_4771_);
lean_dec(v_i_4763_);
lean_inc(v_sepStx_4770_);
v___x_4773_ = lean_array_push(v_acc_4764_, v_sepStx_4770_);
lean_inc(v_stx_4767_);
v___x_4774_ = lean_array_push(v___x_4773_, v_stx_4767_);
v_i_4763_ = v___x_4772_;
v_acc_4764_ = v___x_4774_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4793_, lean_object* v_p_4794_, lean_object* v_i_4795_, lean_object* v_acc_4796_){
_start:
{
lean_object* v_res_4797_; 
v_res_4797_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4793_, v_p_4794_, v_i_4795_, v_acc_4796_);
lean_dec_ref(v_a_4793_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4798_, lean_object* v_p_4799_){
_start:
{
lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4800_ = lean_unsigned_to_nat(0u);
v___x_4801_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4802_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4798_, v_p_4799_, v___x_4800_, v___x_4801_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4803_, lean_object* v_p_4804_){
_start:
{
lean_object* v_res_4805_; 
v_res_4805_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4803_, v_p_4804_);
lean_dec_ref(v_a_4803_);
return v_res_4805_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4806_, lean_object* v_p_4807_){
_start:
{
lean_object* v___f_4808_; lean_object* v___x_4809_; 
v___f_4808_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4808_, 0, v_p_4807_);
v___x_4809_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4806_, v___f_4808_);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4810_, lean_object* v_p_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l_Array_filterSepElems(v_a_4810_, v_p_4811_);
lean_dec_ref(v_a_4810_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4813_, lean_object* v_acc_4814_, lean_object* v_inst_4815_, lean_object* v_a_4816_, lean_object* v_f_4817_, lean_object* v_stx_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4813_, v_acc_4814_, v_inst_4815_, v_a_4816_, v_f_4817_, v_stx_4818_);
lean_dec(v_i_4813_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4820_, lean_object* v_a_4821_, lean_object* v_f_4822_, lean_object* v_i_4823_, lean_object* v_acc_4824_){
_start:
{
lean_object* v_toApplicative_4825_; lean_object* v_toBind_4826_; lean_object* v_toPure_4827_; lean_object* v___x_4828_; uint8_t v___x_4829_; 
v_toApplicative_4825_ = lean_ctor_get(v_inst_4820_, 0);
v_toBind_4826_ = lean_ctor_get(v_inst_4820_, 1);
v_toPure_4827_ = lean_ctor_get(v_toApplicative_4825_, 1);
v___x_4828_ = lean_array_get_size(v_a_4821_);
v___x_4829_ = lean_nat_dec_lt(v_i_4823_, v___x_4828_);
if (v___x_4829_ == 0)
{
lean_object* v___x_4830_; 
lean_inc(v_toPure_4827_);
lean_dec(v_i_4823_);
lean_dec(v_f_4822_);
lean_dec_ref(v_a_4821_);
lean_dec_ref(v_inst_4820_);
v___x_4830_ = lean_apply_2(v_toPure_4827_, lean_box(0), v_acc_4824_);
return v___x_4830_;
}
else
{
lean_object* v_stx_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; uint8_t v___x_4835_; 
v_stx_4831_ = lean_array_fget_borrowed(v_a_4821_, v_i_4823_);
v___x_4832_ = lean_unsigned_to_nat(2u);
v___x_4833_ = lean_nat_mod(v_i_4823_, v___x_4832_);
v___x_4834_ = lean_unsigned_to_nat(0u);
v___x_4835_ = lean_nat_dec_eq(v___x_4833_, v___x_4834_);
lean_dec(v___x_4833_);
if (v___x_4835_ == 0)
{
lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4836_ = lean_unsigned_to_nat(1u);
v___x_4837_ = lean_nat_add(v_i_4823_, v___x_4836_);
lean_dec(v_i_4823_);
lean_inc(v_stx_4831_);
v___x_4838_ = lean_array_push(v_acc_4824_, v_stx_4831_);
v_i_4823_ = v___x_4837_;
v_acc_4824_ = v___x_4838_;
goto _start;
}
else
{
lean_object* v___f_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
lean_inc(v_stx_4831_);
lean_inc(v_toBind_4826_);
lean_inc(v_f_4822_);
v___f_4840_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4840_, 0, v_i_4823_);
lean_closure_set(v___f_4840_, 1, v_acc_4824_);
lean_closure_set(v___f_4840_, 2, v_inst_4820_);
lean_closure_set(v___f_4840_, 3, v_a_4821_);
lean_closure_set(v___f_4840_, 4, v_f_4822_);
v___x_4841_ = lean_apply_1(v_f_4822_, v_stx_4831_);
v___x_4842_ = lean_apply_4(v_toBind_4826_, lean_box(0), lean_box(0), v___x_4841_, v___f_4840_);
return v___x_4842_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4843_, lean_object* v_acc_4844_, lean_object* v_inst_4845_, lean_object* v_a_4846_, lean_object* v_f_4847_, lean_object* v_stx_4848_){
_start:
{
lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; 
v___x_4849_ = lean_unsigned_to_nat(1u);
v___x_4850_ = lean_nat_add(v_i_4843_, v___x_4849_);
v___x_4851_ = lean_array_push(v_acc_4844_, v_stx_4848_);
v___x_4852_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4845_, v_a_4846_, v_f_4847_, v___x_4850_, v___x_4851_);
return v___x_4852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4853_, lean_object* v_inst_4854_, lean_object* v_a_4855_, lean_object* v_f_4856_, lean_object* v_i_4857_, lean_object* v_acc_4858_){
_start:
{
lean_object* v___x_4859_; 
v___x_4859_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4854_, v_a_4855_, v_f_4856_, v_i_4857_, v_acc_4858_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4860_, lean_object* v_a_4861_, lean_object* v_f_4862_){
_start:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4863_ = lean_unsigned_to_nat(0u);
v___x_4864_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4865_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4860_, v_a_4861_, v_f_4862_, v___x_4863_, v___x_4864_);
return v___x_4865_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4866_, lean_object* v_inst_4867_, lean_object* v_a_4868_, lean_object* v_f_4869_){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l_Array_mapSepElemsM___redArg(v_inst_4867_, v_a_4868_, v_f_4869_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4871_, lean_object* v_x_4872_){
_start:
{
lean_object* v___x_4873_; 
v___x_4873_ = lean_apply_1(v_f_4871_, v_x_4872_);
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4874_, lean_object* v_f_4875_, lean_object* v_i_4876_, lean_object* v_acc_4877_){
_start:
{
lean_object* v___x_4878_; uint8_t v___x_4879_; 
v___x_4878_ = lean_array_get_size(v_a_4874_);
v___x_4879_ = lean_nat_dec_lt(v_i_4876_, v___x_4878_);
if (v___x_4879_ == 0)
{
lean_dec(v_i_4876_);
lean_dec_ref(v_f_4875_);
return v_acc_4877_;
}
else
{
lean_object* v_stx_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; uint8_t v___x_4884_; 
v_stx_4880_ = lean_array_fget_borrowed(v_a_4874_, v_i_4876_);
v___x_4881_ = lean_unsigned_to_nat(2u);
v___x_4882_ = lean_nat_mod(v_i_4876_, v___x_4881_);
v___x_4883_ = lean_unsigned_to_nat(0u);
v___x_4884_ = lean_nat_dec_eq(v___x_4882_, v___x_4883_);
lean_dec(v___x_4882_);
if (v___x_4884_ == 0)
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4885_ = lean_unsigned_to_nat(1u);
v___x_4886_ = lean_nat_add(v_i_4876_, v___x_4885_);
lean_dec(v_i_4876_);
lean_inc(v_stx_4880_);
v___x_4887_ = lean_array_push(v_acc_4877_, v_stx_4880_);
v_i_4876_ = v___x_4886_;
v_acc_4877_ = v___x_4887_;
goto _start;
}
else
{
lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; 
lean_inc_ref(v_f_4875_);
lean_inc(v_stx_4880_);
v___x_4889_ = lean_apply_1(v_f_4875_, v_stx_4880_);
v___x_4890_ = lean_unsigned_to_nat(1u);
v___x_4891_ = lean_nat_add(v_i_4876_, v___x_4890_);
lean_dec(v_i_4876_);
v___x_4892_ = lean_array_push(v_acc_4877_, v___x_4889_);
v_i_4876_ = v___x_4891_;
v_acc_4877_ = v___x_4892_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4894_, lean_object* v_f_4895_, lean_object* v_i_4896_, lean_object* v_acc_4897_){
_start:
{
lean_object* v_res_4898_; 
v_res_4898_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4894_, v_f_4895_, v_i_4896_, v_acc_4897_);
lean_dec_ref(v_a_4894_);
return v_res_4898_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4899_, lean_object* v_f_4900_){
_start:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4901_ = lean_unsigned_to_nat(0u);
v___x_4902_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4903_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4899_, v_f_4900_, v___x_4901_, v___x_4902_);
return v___x_4903_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4904_, lean_object* v_f_4905_){
_start:
{
lean_object* v_res_4906_; 
v_res_4906_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4904_, v_f_4905_);
lean_dec_ref(v_a_4904_);
return v_res_4906_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4907_, lean_object* v_f_4908_){
_start:
{
lean_object* v___f_4909_; lean_object* v___x_4910_; 
v___f_4909_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4909_, 0, v_f_4908_);
v___x_4910_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4907_, v___f_4909_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4911_, lean_object* v_f_4912_){
_start:
{
lean_object* v_res_4913_; 
v_res_4913_ = l_Array_mapSepElems(v_a_4911_, v_f_4912_);
lean_dec_ref(v_a_4911_);
return v_res_4913_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4914_, size_t v_i_4915_, size_t v_stop_4916_, lean_object* v_b_4917_){
_start:
{
lean_object* v___y_4919_; uint8_t v___x_4923_; 
v___x_4923_ = lean_usize_dec_eq(v_i_4915_, v_stop_4916_);
if (v___x_4923_ == 0)
{
lean_object* v_fst_4924_; uint8_t v___x_4925_; 
v_fst_4924_ = lean_ctor_get(v_b_4917_, 0);
v___x_4925_ = lean_unbox(v_fst_4924_);
if (v___x_4925_ == 0)
{
lean_object* v_snd_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4935_; 
v_snd_4926_ = lean_ctor_get(v_b_4917_, 1);
v_isSharedCheck_4935_ = !lean_is_exclusive(v_b_4917_);
if (v_isSharedCheck_4935_ == 0)
{
lean_object* v_unused_4936_; 
v_unused_4936_ = lean_ctor_get(v_b_4917_, 0);
lean_dec(v_unused_4936_);
v___x_4928_ = v_b_4917_;
v_isShared_4929_ = v_isSharedCheck_4935_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_snd_4926_);
lean_dec(v_b_4917_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4935_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
uint8_t v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4933_; 
v___x_4930_ = 1;
v___x_4931_ = lean_box(v___x_4930_);
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 0, v___x_4931_);
v___x_4933_ = v___x_4928_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4931_);
lean_ctor_set(v_reuseFailAlloc_4934_, 1, v_snd_4926_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
v___y_4919_ = v___x_4933_;
goto v___jp_4918_;
}
}
}
else
{
lean_object* v_snd_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4947_; 
v_snd_4937_ = lean_ctor_get(v_b_4917_, 1);
v_isSharedCheck_4947_ = !lean_is_exclusive(v_b_4917_);
if (v_isSharedCheck_4947_ == 0)
{
lean_object* v_unused_4948_; 
v_unused_4948_ = lean_ctor_get(v_b_4917_, 0);
lean_dec(v_unused_4948_);
v___x_4939_ = v_b_4917_;
v_isShared_4940_ = v_isSharedCheck_4947_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_snd_4937_);
lean_dec(v_b_4917_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4947_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4945_; 
v___x_4941_ = lean_array_uget_borrowed(v_as_4914_, v_i_4915_);
lean_inc(v___x_4941_);
v___x_4942_ = lean_array_push(v_snd_4937_, v___x_4941_);
v___x_4943_ = lean_box(v___x_4923_);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 1, v___x_4942_);
lean_ctor_set(v___x_4939_, 0, v___x_4943_);
v___x_4945_ = v___x_4939_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v___x_4943_);
lean_ctor_set(v_reuseFailAlloc_4946_, 1, v___x_4942_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
v___y_4919_ = v___x_4945_;
goto v___jp_4918_;
}
}
}
}
else
{
return v_b_4917_;
}
v___jp_4918_:
{
size_t v___x_4920_; size_t v___x_4921_; 
v___x_4920_ = ((size_t)1ULL);
v___x_4921_ = lean_usize_add(v_i_4915_, v___x_4920_);
v_i_4915_ = v___x_4921_;
v_b_4917_ = v___y_4919_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4914_ = stack[0].m_obj;
size_t v_i_4915_ = stack[1].m_num;
size_t v_stop_4916_ = stack[2].m_num;
lean_object* v_b_4917_ = stack[3].m_obj;
lean_object* v_res_4949_;
v_res_4949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4914_, v_i_4915_, v_stop_4916_, v_b_4917_);
stack->m_obj
 = v_res_4949_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4950_, lean_object* v_i_4951_, lean_object* v_stop_4952_, lean_object* v_b_4953_){
_start:
{
size_t v_i_boxed_4954_; size_t v_stop_boxed_4955_; lean_object* v_res_4956_; 
v_i_boxed_4954_ = lean_unbox_usize(v_i_4951_);
lean_dec(v_i_4951_);
v_stop_boxed_4955_ = lean_unbox_usize(v_stop_4952_);
lean_dec(v_stop_4952_);
v_res_4956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4950_, v_i_boxed_4954_, v_stop_boxed_4955_, v_b_4953_);
lean_dec_ref(v_as_4950_);
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4957_){
_start:
{
lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; uint8_t v___x_4961_; 
v___x_4958_ = lean_unsigned_to_nat(0u);
v___x_4959_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4960_ = lean_array_get_size(v_sa_4957_);
v___x_4961_ = lean_nat_dec_lt(v___x_4958_, v___x_4960_);
if (v___x_4961_ == 0)
{
return v___x_4959_;
}
else
{
lean_object* v___x_4962_; lean_object* v___x_4963_; size_t v___x_4964_; size_t v___x_4965_; lean_object* v___x_4966_; lean_object* v_snd_4967_; 
v___x_4962_ = lean_box(v___x_4961_);
v___x_4963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4963_, 0, v___x_4962_);
lean_ctor_set(v___x_4963_, 1, v___x_4959_);
v___x_4964_ = ((size_t)0ULL);
v___x_4965_ = lean_usize_of_nat(v___x_4960_);
v___x_4966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4957_, v___x_4964_, v___x_4965_, v___x_4963_);
v_snd_4967_ = lean_ctor_get(v___x_4966_, 1);
lean_inc(v_snd_4967_);
lean_dec_ref(v___x_4966_);
return v_snd_4967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4968_);
lean_dec_ref(v_sa_4968_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4970_, lean_object* v_sa_4971_){
_start:
{
lean_object* v___x_4972_; 
v___x_4972_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4971_);
return v___x_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4973_, lean_object* v_sa_4974_){
_start:
{
lean_object* v_res_4975_; 
v_res_4975_ = l_Lean_Syntax_SepArray_getElems(v_sep_4973_, v_sa_4974_);
lean_dec_ref(v_sa_4974_);
lean_dec_ref(v_sep_4973_);
return v_res_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4976_){
_start:
{
lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; uint8_t v___x_4980_; 
v___x_4977_ = lean_unsigned_to_nat(0u);
v___x_4978_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4979_ = lean_array_get_size(v_sa_4976_);
v___x_4980_ = lean_nat_dec_lt(v___x_4977_, v___x_4979_);
if (v___x_4980_ == 0)
{
return v___x_4978_;
}
else
{
lean_object* v___x_4981_; lean_object* v___x_4982_; size_t v___x_4983_; size_t v___x_4984_; lean_object* v___x_4985_; lean_object* v_snd_4986_; 
v___x_4981_ = lean_box(v___x_4980_);
v___x_4982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4982_, 0, v___x_4981_);
lean_ctor_set(v___x_4982_, 1, v___x_4978_);
v___x_4983_ = ((size_t)0ULL);
v___x_4984_ = lean_usize_of_nat(v___x_4979_);
v___x_4985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4976_, v___x_4983_, v___x_4984_, v___x_4982_);
v_snd_4986_ = lean_ctor_get(v___x_4985_, 1);
lean_inc(v_snd_4986_);
lean_dec_ref(v___x_4985_);
return v_snd_4986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4987_);
lean_dec_ref(v_sa_4987_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4989_, lean_object* v_sep_4990_, lean_object* v_sa_4991_){
_start:
{
lean_object* v___x_4992_; 
v___x_4992_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4991_);
return v___x_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4993_, lean_object* v_sep_4994_, lean_object* v_sa_4995_){
_start:
{
lean_object* v_res_4996_; 
v_res_4996_ = l_Lean_Syntax_TSepArray_getElems(v_k_4993_, v_sep_4994_, v_sa_4995_);
lean_dec_ref(v_sa_4995_);
lean_dec_ref(v_sep_4994_);
lean_dec(v_k_4993_);
return v_res_4996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4997_, lean_object* v_sa_4998_, lean_object* v_e_4999_){
_start:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; uint8_t v___x_5002_; 
v___x_5000_ = lean_array_get_size(v_sa_4998_);
v___x_5001_ = lean_unsigned_to_nat(0u);
v___x_5002_ = lean_nat_dec_eq(v___x_5000_, v___x_5001_);
if (v___x_5002_ == 0)
{
lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_5003_ = l_Lean_mkAtom(v_sep_4997_);
v___x_5004_ = lean_array_push(v_sa_4998_, v___x_5003_);
v___x_5005_ = lean_array_push(v___x_5004_, v_e_4999_);
return v___x_5005_;
}
else
{
lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; 
lean_dec_ref(v_sa_4998_);
lean_dec_ref(v_sep_4997_);
v___x_5006_ = lean_unsigned_to_nat(1u);
v___x_5007_ = lean_mk_empty_array_with_capacity(v___x_5006_);
v___x_5008_ = lean_array_push(v___x_5007_, v_e_4999_);
return v___x_5008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_5009_, lean_object* v_sep_5010_, lean_object* v_sa_5011_, lean_object* v_e_5012_){
_start:
{
lean_object* v___x_5013_; 
v___x_5013_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_5010_, v_sa_5011_, v_e_5012_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_5014_, lean_object* v_sep_5015_, lean_object* v_sa_5016_, lean_object* v_e_5017_){
_start:
{
lean_object* v_res_5018_; 
v_res_5018_ = l_Lean_Syntax_TSepArray_push(v_k_5014_, v_sep_5015_, v_sa_5016_, v_e_5017_);
lean_dec(v_k_5014_);
return v_res_5018_;
}
}
lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg(){
_start:
{
lean_object* v___x_5020_; 
v___x_5020_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_5020_;
}
}
LEAN_EXPORT void l_Lean_Syntax_instEmptyCollectionSepArray___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5021_;
v_res_5021_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
stack->m_obj
 = v_res_5021_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg___boxed(lean_object* v___dummy_5022_){
_start:
{
lean_object* v_res_5023_; 
v_res_5023_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v_res_5023_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0(void){
_start:
{
lean_object* v___x_5024_; 
v___x_5024_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v___x_5024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_5025_){
_start:
{
lean_object* v___x_5026_; 
v___x_5026_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0);
return v___x_5026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_5027_);
lean_dec_ref(v_sep_5027_);
return v_res_5028_;
}
}
lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg(){
_start:
{
lean_object* v___x_5030_; 
v___x_5030_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_5030_;
}
}
LEAN_EXPORT void l_Lean_Syntax_instEmptyCollectionTSepArray___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5031_;
v_res_5031_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
stack->m_obj
 = v_res_5031_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg___boxed(lean_object* v___dummy_5032_){
_start:
{
lean_object* v_res_5033_; 
v_res_5033_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v_res_5033_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0(void){
_start:
{
lean_object* v___x_5034_; 
v___x_5034_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v___x_5034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_5035_, lean_object* v_k_5036_){
_start:
{
lean_object* v___x_5037_; 
v___x_5037_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0);
return v___x_5037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_5038_, lean_object* v_k_5039_){
_start:
{
lean_object* v_res_5040_; 
v_res_5040_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_5038_, v_k_5039_);
lean_dec_ref(v_k_5039_);
lean_dec(v_sep_5038_);
return v_res_5040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(lean_object* v_v_5041_){
_start:
{
lean_inc_ref(v_v_5041_);
return v_v_5041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0___boxed(lean_object* v_v_5042_){
_start:
{
lean_object* v_res_5043_; 
v_res_5043_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(v_v_5042_);
lean_dec_ref(v_v_5042_);
return v_res_5043_;
}
}
lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg(){
_start:
{
lean_object* v___f_5046_; 
v___f_5046_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_5046_;
}
}
LEAN_EXPORT void l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5047_;
v_res_5047_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg();
stack->m_obj
 = v_res_5047_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___boxed(lean_object* v___dummy_5048_){
_start:
{
lean_object* v_res_5049_; 
v_res_5049_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg();
return v_res_5049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray(lean_object* v_k_5050_, lean_object* v_sep_5051_){
_start:
{
lean_object* v___f_5052_; 
v___f_5052_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___boxed(lean_object* v_k_5053_, lean_object* v_sep_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Lean_Syntax_instCoeOutTSepArraySepArray(v_k_5053_, v_sep_5054_);
lean_dec_ref(v_sep_5054_);
lean_dec(v_k_5053_);
return v_res_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_5056_, lean_object* v_sep_5057_){
_start:
{
lean_object* v___x_5058_; 
v___x_5058_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_5058_, 0, v_k_5056_);
lean_closure_set(v___x_5058_, 1, v_sep_5057_);
return v___x_5058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_5059_, lean_object* v_x_5060_){
_start:
{
lean_object* v___x_5061_; 
v___x_5061_ = lean_apply_1(v_inst_5059_, v_x_5060_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_5062_, lean_object* v_a_5063_){
_start:
{
lean_object* v___x_5064_; size_t v_sz_5065_; size_t v___x_5066_; lean_object* v___x_5067_; 
v___x_5064_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_5065_ = lean_array_size(v_a_5063_);
v___x_5066_ = ((size_t)0ULL);
v___x_5067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5064_, v___f_5062_, v_sz_5065_, v___x_5066_, v_a_5063_);
return v___x_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_5068_){
_start:
{
lean_object* v___f_5069_; lean_object* v___f_5070_; 
v___f_5069_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5069_, 0, v_inst_5068_);
v___f_5070_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5070_, 0, v___f_5069_);
return v___f_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_5071_, lean_object* v_k_x27_5072_, lean_object* v_inst_5073_){
_start:
{
lean_object* v___x_5074_; 
v___x_5074_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_5073_);
return v___x_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_5075_, lean_object* v_k_x27_5076_, lean_object* v_inst_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_5075_, v_k_x27_5076_, v_inst_5077_);
lean_dec(v_k_x27_5076_);
lean_dec(v_k_5075_);
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(lean_object* v_a_5079_){
_start:
{
lean_inc_ref(v_a_5079_);
return v_a_5079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0___boxed(lean_object* v_a_5080_){
_start:
{
lean_object* v_res_5081_; 
v_res_5081_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(v_a_5080_);
lean_dec_ref(v_a_5080_);
return v_res_5081_;
}
}
lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg(){
_start:
{
lean_object* v___f_5084_; 
v___f_5084_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_5084_;
}
}
LEAN_EXPORT void l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5085_;
v_res_5085_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg();
stack->m_obj
 = v_res_5085_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___boxed(lean_object* v___dummy_5086_){
_start:
{
lean_object* v_res_5087_; 
v_res_5087_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg();
return v_res_5087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_5088_){
_start:
{
lean_object* v___f_5089_; 
v___f_5089_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* v_k_5090_){
_start:
{
lean_object* v_res_5091_; 
v_res_5091_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(v_k_5090_);
lean_dec(v_k_5090_);
return v_res_5091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_5098_){
_start:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5099_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1));
v___x_5100_ = lean_box(2);
v___x_5101_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
v___x_5102_ = lean_unsigned_to_nat(2u);
v___x_5103_ = lean_mk_empty_array_with_capacity(v___x_5102_);
v___x_5104_ = lean_array_push(v___x_5103_, v_id_5098_);
v___x_5105_ = lean_array_push(v___x_5104_, v___x_5101_);
v___x_5106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5100_);
lean_ctor_set(v___x_5106_, 1, v___x_5099_);
lean_ctor_set(v___x_5106_, 2, v___x_5105_);
return v___x_5106_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_5110_; lean_object* v___x_5111_; 
v___x_5110_ = 123;
v___x_5111_ = lean_box_uint32(v___x_5110_);
return v___x_5111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* v_s_5112_, lean_object* v_i_5113_){
_start:
{
lean_object* v___x_5114_; 
v___x_5114_ = l_Lean_Syntax_decodeQuotedChar(v_s_5112_, v_i_5113_);
if (lean_obj_tag(v___x_5114_) == 0)
{
uint32_t v_c_5115_; uint32_t v___x_5116_; uint8_t v___x_5117_; 
v_c_5115_ = lean_string_utf8_get(v_s_5112_, v_i_5113_);
v___x_5116_ = 123;
v___x_5117_ = lean_uint32_dec_eq(v_c_5115_, v___x_5116_);
if (v___x_5117_ == 0)
{
return v___x_5114_;
}
else
{
lean_object* v_i_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; 
v_i_5118_ = lean_string_utf8_next(v_s_5112_, v_i_5113_);
v___x_5119_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
v___x_5120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5120_, 0, v___x_5119_);
lean_ctor_set(v___x_5120_, 1, v_i_5118_);
v___x_5121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5121_, 0, v___x_5120_);
return v___x_5121_;
}
}
else
{
return v___x_5114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* v_s_5122_, lean_object* v_i_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5122_, v_i_5123_);
lean_dec(v_i_5123_);
lean_dec_ref(v_s_5122_);
return v_res_5124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* v_s_5125_, lean_object* v_i_5126_, lean_object* v_acc_5127_){
_start:
{
uint32_t v_c_5128_; uint32_t v___x_5129_; uint8_t v___x_5130_; 
v_c_5128_ = lean_string_utf8_get(v_s_5125_, v_i_5126_);
v___x_5129_ = 34;
v___x_5130_ = lean_uint32_dec_eq(v_c_5128_, v___x_5129_);
if (v___x_5130_ == 0)
{
uint32_t v___x_5131_; uint8_t v___x_5132_; 
v___x_5131_ = 123;
v___x_5132_ = lean_uint32_dec_eq(v_c_5128_, v___x_5131_);
if (v___x_5132_ == 0)
{
lean_object* v_i_5133_; uint8_t v___x_5134_; 
v_i_5133_ = lean_string_utf8_next(v_s_5125_, v_i_5126_);
lean_dec(v_i_5126_);
v___x_5134_ = lean_string_utf8_at_end(v_s_5125_, v_i_5133_);
if (v___x_5134_ == 0)
{
uint32_t v___x_5135_; uint8_t v___x_5136_; 
v___x_5135_ = 92;
v___x_5136_ = lean_uint32_dec_eq(v_c_5128_, v___x_5135_);
if (v___x_5136_ == 0)
{
lean_object* v___x_5137_; 
v___x_5137_ = lean_string_push(v_acc_5127_, v_c_5128_);
v_i_5126_ = v_i_5133_;
v_acc_5127_ = v___x_5137_;
goto _start;
}
else
{
lean_object* v___x_5139_; 
v___x_5139_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5125_, v_i_5133_);
if (lean_obj_tag(v___x_5139_) == 1)
{
lean_object* v_val_5140_; lean_object* v_fst_5141_; lean_object* v_snd_5142_; uint32_t v___x_5143_; lean_object* v___x_5144_; 
lean_dec(v_i_5133_);
v_val_5140_ = lean_ctor_get(v___x_5139_, 0);
lean_inc(v_val_5140_);
lean_dec_ref_known(v___x_5139_, 1);
v_fst_5141_ = lean_ctor_get(v_val_5140_, 0);
lean_inc(v_fst_5141_);
v_snd_5142_ = lean_ctor_get(v_val_5140_, 1);
lean_inc(v_snd_5142_);
lean_dec(v_val_5140_);
v___x_5143_ = lean_unbox_uint32(v_fst_5141_);
lean_dec(v_fst_5141_);
v___x_5144_ = lean_string_push(v_acc_5127_, v___x_5143_);
v_i_5126_ = v_snd_5142_;
v_acc_5127_ = v___x_5144_;
goto _start;
}
else
{
lean_object* v___x_5146_; 
lean_dec(v___x_5139_);
lean_inc_ref(v_s_5125_);
v___x_5146_ = l_Lean_Syntax_decodeStringGap(v_s_5125_, v_i_5133_);
lean_dec(v_i_5133_);
if (lean_obj_tag(v___x_5146_) == 1)
{
lean_object* v_val_5147_; 
v_val_5147_ = lean_ctor_get(v___x_5146_, 0);
lean_inc(v_val_5147_);
lean_dec_ref_known(v___x_5146_, 1);
v_i_5126_ = v_val_5147_;
goto _start;
}
else
{
lean_object* v___x_5149_; 
lean_dec(v___x_5146_);
lean_dec_ref(v_acc_5127_);
lean_dec_ref(v_s_5125_);
v___x_5149_ = lean_box(0);
return v___x_5149_;
}
}
}
}
else
{
lean_object* v___x_5150_; 
lean_dec(v_i_5133_);
lean_dec_ref(v_acc_5127_);
lean_dec_ref(v_s_5125_);
v___x_5150_ = lean_box(0);
return v___x_5150_;
}
}
else
{
lean_object* v___x_5151_; 
lean_dec(v_i_5126_);
lean_dec_ref(v_s_5125_);
v___x_5151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5151_, 0, v_acc_5127_);
return v___x_5151_;
}
}
else
{
lean_object* v___x_5152_; 
lean_dec(v_i_5126_);
lean_dec_ref(v_s_5125_);
v___x_5152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5152_, 0, v_acc_5127_);
return v___x_5152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5153_){
_start:
{
lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; 
v___x_5154_ = lean_unsigned_to_nat(1u);
v___x_5155_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5156_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5153_, v___x_5154_, v___x_5155_);
return v___x_5156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5160_){
_start:
{
lean_object* v___x_5161_; lean_object* v___x_5162_; 
v___x_5161_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5162_ = l_Lean_Syntax_isLit_x3f(v___x_5161_, v_stx_5160_);
if (lean_obj_tag(v___x_5162_) == 0)
{
return v___x_5162_;
}
else
{
lean_object* v_val_5163_; lean_object* v___x_5164_; 
v_val_5163_ = lean_ctor_get(v___x_5162_, 0);
lean_inc(v_val_5163_);
lean_dec_ref_known(v___x_5162_, 1);
v___x_5164_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5163_);
return v___x_5164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5165_){
_start:
{
lean_object* v_res_5166_; 
v_res_5166_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5165_);
lean_dec(v_stx_5165_);
return v_res_5166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5167_){
_start:
{
lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; uint8_t v___x_5172_; 
v___x_5168_ = l_Lean_Syntax_getArgs(v_stx_5167_);
v___x_5169_ = lean_unsigned_to_nat(0u);
v___x_5170_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5171_ = lean_array_get_size(v___x_5168_);
v___x_5172_ = lean_nat_dec_lt(v___x_5169_, v___x_5171_);
if (v___x_5172_ == 0)
{
lean_dec_ref(v___x_5168_);
return v___x_5170_;
}
else
{
lean_object* v___x_5173_; lean_object* v___x_5174_; size_t v___x_5175_; size_t v___x_5176_; lean_object* v___x_5177_; lean_object* v_snd_5178_; 
v___x_5173_ = lean_box(v___x_5172_);
v___x_5174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5174_, 0, v___x_5173_);
lean_ctor_set(v___x_5174_, 1, v___x_5170_);
v___x_5175_ = ((size_t)0ULL);
v___x_5176_ = lean_usize_of_nat(v___x_5171_);
v___x_5177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5168_, v___x_5175_, v___x_5176_, v___x_5174_);
lean_dec_ref(v___x_5168_);
v_snd_5178_ = lean_ctor_get(v___x_5177_, 1);
lean_inc(v_snd_5178_);
lean_dec_ref(v___x_5177_);
return v_snd_5178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5179_){
_start:
{
lean_object* v_res_5180_; 
v_res_5180_ = l_Lean_Syntax_getSepArgs(v_stx_5179_);
lean_dec(v_stx_5179_);
return v_res_5180_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5181_, lean_object* v_mkElem_5182_, lean_object* v_mkLit_5183_, lean_object* v_as_5184_, size_t v_sz_5185_, size_t v_i_5186_, lean_object* v_b_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_){
_start:
{
lean_object* v_a_5191_; lean_object* v_a_5192_; lean_object* v_elem_5197_; lean_object* v___y_5198_; lean_object* v___y_5199_; uint8_t v___x_5204_; 
v___x_5204_ = lean_usize_dec_lt(v_i_5186_, v_sz_5185_);
if (v___x_5204_ == 0)
{
lean_object* v___x_5205_; 
lean_dec_ref(v_mkLit_5183_);
lean_dec_ref(v_mkElem_5182_);
lean_dec_ref(v_mkAppend_5181_);
v___x_5205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5205_, 0, v_b_5187_);
lean_ctor_set(v___x_5205_, 1, v___y_5189_);
return v___x_5205_;
}
else
{
lean_object* v_a_5206_; lean_object* v___x_5207_; 
v_a_5206_ = lean_array_uget_borrowed(v_as_5184_, v_i_5186_);
v___x_5207_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5206_);
if (lean_obj_tag(v___x_5207_) == 0)
{
lean_object* v_methods_5208_; lean_object* v_quotContext_5209_; lean_object* v_currMacroScope_5210_; lean_object* v_currRecDepth_5211_; lean_object* v_maxRecDepth_5212_; lean_object* v_ref_5213_; lean_object* v_ref_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; 
v_methods_5208_ = lean_ctor_get(v___y_5188_, 0);
v_quotContext_5209_ = lean_ctor_get(v___y_5188_, 1);
v_currMacroScope_5210_ = lean_ctor_get(v___y_5188_, 2);
v_currRecDepth_5211_ = lean_ctor_get(v___y_5188_, 3);
v_maxRecDepth_5212_ = lean_ctor_get(v___y_5188_, 4);
v_ref_5213_ = lean_ctor_get(v___y_5188_, 5);
v_ref_5214_ = l_Lean_replaceRef(v_a_5206_, v_ref_5213_);
lean_inc(v_maxRecDepth_5212_);
lean_inc(v_currRecDepth_5211_);
lean_inc(v_currMacroScope_5210_);
lean_inc(v_quotContext_5209_);
lean_inc(v_methods_5208_);
v___x_5215_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5215_, 0, v_methods_5208_);
lean_ctor_set(v___x_5215_, 1, v_quotContext_5209_);
lean_ctor_set(v___x_5215_, 2, v_currMacroScope_5210_);
lean_ctor_set(v___x_5215_, 3, v_currRecDepth_5211_);
lean_ctor_set(v___x_5215_, 4, v_maxRecDepth_5212_);
lean_ctor_set(v___x_5215_, 5, v_ref_5214_);
lean_inc_ref(v_mkElem_5182_);
lean_inc(v_a_5206_);
v___x_5216_ = lean_apply_3(v_mkElem_5182_, v_a_5206_, v___x_5215_, v___y_5189_);
if (lean_obj_tag(v___x_5216_) == 0)
{
lean_object* v_a_5217_; lean_object* v_a_5218_; 
v_a_5217_ = lean_ctor_get(v___x_5216_, 0);
lean_inc(v_a_5217_);
v_a_5218_ = lean_ctor_get(v___x_5216_, 1);
lean_inc(v_a_5218_);
lean_dec_ref_known(v___x_5216_, 2);
v_elem_5197_ = v_a_5217_;
v___y_5198_ = v___y_5188_;
v___y_5199_ = v_a_5218_;
goto v___jp_5196_;
}
else
{
lean_dec(v_b_5187_);
lean_dec_ref(v_mkLit_5183_);
lean_dec_ref(v_mkElem_5182_);
lean_dec_ref(v_mkAppend_5181_);
return v___x_5216_;
}
}
else
{
lean_object* v_val_5219_; uint8_t v___x_5220_; 
v_val_5219_ = lean_ctor_get(v___x_5207_, 0);
lean_inc_n(v_val_5219_, 2);
lean_dec_ref_known(v___x_5207_, 1);
v___x_5220_ = lean_string_isempty(v_val_5219_);
if (v___x_5220_ == 0)
{
lean_object* v_methods_5221_; lean_object* v_quotContext_5222_; lean_object* v_currMacroScope_5223_; lean_object* v_currRecDepth_5224_; lean_object* v_maxRecDepth_5225_; lean_object* v_ref_5226_; lean_object* v_ref_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; 
v_methods_5221_ = lean_ctor_get(v___y_5188_, 0);
v_quotContext_5222_ = lean_ctor_get(v___y_5188_, 1);
v_currMacroScope_5223_ = lean_ctor_get(v___y_5188_, 2);
v_currRecDepth_5224_ = lean_ctor_get(v___y_5188_, 3);
v_maxRecDepth_5225_ = lean_ctor_get(v___y_5188_, 4);
v_ref_5226_ = lean_ctor_get(v___y_5188_, 5);
v_ref_5227_ = l_Lean_replaceRef(v_a_5206_, v_ref_5226_);
lean_inc(v_maxRecDepth_5225_);
lean_inc(v_currRecDepth_5224_);
lean_inc(v_currMacroScope_5223_);
lean_inc(v_quotContext_5222_);
lean_inc(v_methods_5221_);
v___x_5228_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5228_, 0, v_methods_5221_);
lean_ctor_set(v___x_5228_, 1, v_quotContext_5222_);
lean_ctor_set(v___x_5228_, 2, v_currMacroScope_5223_);
lean_ctor_set(v___x_5228_, 3, v_currRecDepth_5224_);
lean_ctor_set(v___x_5228_, 4, v_maxRecDepth_5225_);
lean_ctor_set(v___x_5228_, 5, v_ref_5227_);
lean_inc_ref(v_mkLit_5183_);
v___x_5229_ = lean_apply_3(v_mkLit_5183_, v_val_5219_, v___x_5228_, v___y_5189_);
if (lean_obj_tag(v___x_5229_) == 0)
{
lean_object* v_a_5230_; lean_object* v_a_5231_; 
v_a_5230_ = lean_ctor_get(v___x_5229_, 0);
lean_inc(v_a_5230_);
v_a_5231_ = lean_ctor_get(v___x_5229_, 1);
lean_inc(v_a_5231_);
lean_dec_ref_known(v___x_5229_, 2);
v_elem_5197_ = v_a_5230_;
v___y_5198_ = v___y_5188_;
v___y_5199_ = v_a_5231_;
goto v___jp_5196_;
}
else
{
lean_dec(v_b_5187_);
lean_dec_ref(v_mkLit_5183_);
lean_dec_ref(v_mkElem_5182_);
lean_dec_ref(v_mkAppend_5181_);
return v___x_5229_;
}
}
else
{
lean_dec(v_val_5219_);
v_a_5191_ = v_b_5187_;
v_a_5192_ = v___y_5189_;
goto v___jp_5190_;
}
}
}
v___jp_5190_:
{
size_t v___x_5193_; size_t v___x_5194_; 
v___x_5193_ = ((size_t)1ULL);
v___x_5194_ = lean_usize_add(v_i_5186_, v___x_5193_);
v_i_5186_ = v___x_5194_;
v_b_5187_ = v_a_5191_;
v___y_5189_ = v_a_5192_;
goto _start;
}
v___jp_5196_:
{
uint8_t v___x_5200_; 
v___x_5200_ = l_Lean_Syntax_isMissing(v_b_5187_);
if (v___x_5200_ == 0)
{
lean_object* v___x_5201_; 
lean_inc_ref(v_mkAppend_5181_);
lean_inc_ref(v___y_5198_);
v___x_5201_ = lean_apply_4(v_mkAppend_5181_, v_b_5187_, v_elem_5197_, v___y_5198_, v___y_5199_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_object* v_a_5202_; lean_object* v_a_5203_; 
v_a_5202_ = lean_ctor_get(v___x_5201_, 0);
lean_inc(v_a_5202_);
v_a_5203_ = lean_ctor_get(v___x_5201_, 1);
lean_inc(v_a_5203_);
lean_dec_ref_known(v___x_5201_, 2);
v_a_5191_ = v_a_5202_;
v_a_5192_ = v_a_5203_;
goto v___jp_5190_;
}
else
{
lean_dec_ref(v_mkLit_5183_);
lean_dec_ref(v_mkElem_5182_);
lean_dec_ref(v_mkAppend_5181_);
return v___x_5201_;
}
}
else
{
lean_dec(v_b_5187_);
v_a_5191_ = v_elem_5197_;
v_a_5192_ = v___y_5199_;
goto v___jp_5190_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mkAppend_5181_ = stack[0].m_obj;
lean_object* v_mkElem_5182_ = stack[1].m_obj;
lean_object* v_mkLit_5183_ = stack[2].m_obj;
lean_object* v_as_5184_ = stack[3].m_obj;
size_t v_sz_5185_ = stack[4].m_num;
size_t v_i_5186_ = stack[5].m_num;
lean_object* v_b_5187_ = stack[6].m_obj;
lean_object* v___y_5188_ = stack[7].m_obj;
lean_object* v___y_5189_ = stack[8].m_obj;
lean_object* v_res_5232_;
v_res_5232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5181_, v_mkElem_5182_, v_mkLit_5183_, v_as_5184_, v_sz_5185_, v_i_5186_, v_b_5187_, v___y_5188_, v___y_5189_);
stack->m_obj
 = v_res_5232_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5233_, lean_object* v_mkElem_5234_, lean_object* v_mkLit_5235_, lean_object* v_as_5236_, lean_object* v_sz_5237_, lean_object* v_i_5238_, lean_object* v_b_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_){
_start:
{
size_t v_sz_boxed_5242_; size_t v_i_boxed_5243_; lean_object* v_res_5244_; 
v_sz_boxed_5242_ = lean_unbox_usize(v_sz_5237_);
lean_dec(v_sz_5237_);
v_i_boxed_5243_ = lean_unbox_usize(v_i_5238_);
lean_dec(v_i_5238_);
v_res_5244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5233_, v_mkElem_5234_, v_mkLit_5235_, v_as_5236_, v_sz_boxed_5242_, v_i_boxed_5243_, v_b_5239_, v___y_5240_, v___y_5241_);
lean_dec_ref(v___y_5240_);
lean_dec_ref(v_as_5236_);
return v_res_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5245_, lean_object* v_mkAppend_5246_, lean_object* v_mkElem_5247_, lean_object* v_mkLit_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_){
_start:
{
lean_object* v_result_5251_; size_t v_sz_5252_; size_t v___x_5253_; lean_object* v___x_5254_; 
v_result_5251_ = lean_box(0);
v_sz_5252_ = lean_array_size(v_chunks_5245_);
v___x_5253_ = ((size_t)0ULL);
lean_inc_ref(v_mkLit_5248_);
v___x_5254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5246_, v_mkElem_5247_, v_mkLit_5248_, v_chunks_5245_, v_sz_5252_, v___x_5253_, v_result_5251_, v_a_5249_, v_a_5250_);
if (lean_obj_tag(v___x_5254_) == 0)
{
lean_object* v_a_5255_; lean_object* v_a_5256_; uint8_t v___x_5257_; 
v_a_5255_ = lean_ctor_get(v___x_5254_, 0);
v_a_5256_ = lean_ctor_get(v___x_5254_, 1);
v___x_5257_ = l_Lean_Syntax_isMissing(v_a_5255_);
if (v___x_5257_ == 0)
{
lean_dec_ref(v_mkLit_5248_);
return v___x_5254_;
}
else
{
lean_object* v___x_5258_; lean_object* v___x_5259_; 
lean_inc(v_a_5256_);
lean_dec_ref_known(v___x_5254_, 2);
v___x_5258_ = ((lean_object*)(l_Lean_versionString___closed__0));
lean_inc_ref(v_a_5249_);
v___x_5259_ = lean_apply_3(v_mkLit_5248_, v___x_5258_, v_a_5249_, v_a_5256_);
return v___x_5259_;
}
}
else
{
lean_dec_ref(v_mkLit_5248_);
return v___x_5254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5260_, lean_object* v_mkAppend_5261_, lean_object* v_mkElem_5262_, lean_object* v_mkLit_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_){
_start:
{
lean_object* v_res_5266_; 
v_res_5266_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5260_, v_mkAppend_5261_, v_mkElem_5262_, v_mkLit_5263_, v_a_5264_, v_a_5265_);
lean_dec_ref(v_a_5264_);
lean_dec_ref(v_chunks_5260_);
return v_res_5266_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5271_, lean_object* v_b_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_){
_start:
{
lean_object* v_ref_5275_; uint8_t v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; 
v_ref_5275_ = lean_ctor_get(v___y_5273_, 5);
v___x_5276_ = 0;
v___x_5277_ = l_Lean_SourceInfo_fromRef(v_ref_5275_, v___x_5276_);
v___x_5278_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5279_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5277_);
v___x_5280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5280_, 0, v___x_5277_);
lean_ctor_set(v___x_5280_, 1, v___x_5279_);
v___x_5281_ = l_Lean_Syntax_node3(v___x_5277_, v___x_5278_, v_a_5271_, v___x_5280_, v_b_5272_);
v___x_5282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5282_, 0, v___x_5281_);
lean_ctor_set(v___x_5282_, 1, v___y_5274_);
return v___x_5282_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5283_, lean_object* v_b_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_){
_start:
{
lean_object* v_res_5287_; 
v_res_5287_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5283_, v_b_5284_, v___y_5285_, v___y_5286_);
lean_dec_ref(v___y_5285_);
return v_res_5287_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5288_, lean_object* v_a_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_){
_start:
{
lean_object* v_ref_5292_; uint8_t v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; 
v_ref_5292_ = lean_ctor_get(v___y_5290_, 5);
v___x_5293_ = 0;
v___x_5294_ = l_Lean_SourceInfo_fromRef(v_ref_5292_, v___x_5293_);
v___x_5295_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5296_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5294_);
v___x_5297_ = l_Lean_Syntax_node1(v___x_5294_, v___x_5296_, v_a_5289_);
v___x_5298_ = l_Lean_Syntax_node2(v___x_5294_, v___x_5295_, v_ofInterpFn_5288_, v___x_5297_);
v___x_5299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5299_, 0, v___x_5298_);
lean_ctor_set(v___x_5299_, 1, v___y_5291_);
return v___x_5299_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5300_, lean_object* v_a_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_){
_start:
{
lean_object* v_res_5304_; 
v_res_5304_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5300_, v_a_5301_, v___y_5302_, v___y_5303_);
lean_dec_ref(v___y_5302_);
return v_res_5304_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5305_, lean_object* v_s_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_){
_start:
{
lean_object* v_ref_5309_; uint8_t v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
v_ref_5309_ = lean_ctor_get(v___y_5307_, 5);
v___x_5310_ = 0;
v___x_5311_ = l_Lean_SourceInfo_fromRef(v_ref_5309_, v___x_5310_);
v___x_5312_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5313_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5314_ = lean_box(2);
v___x_5315_ = l_Lean_Syntax_mkStrLit(v_s_5306_, v___x_5314_);
lean_inc(v___x_5311_);
v___x_5316_ = l_Lean_Syntax_node1(v___x_5311_, v___x_5313_, v___x_5315_);
v___x_5317_ = l_Lean_Syntax_node2(v___x_5311_, v___x_5312_, v_ofLitFn_5305_, v___x_5316_);
v___x_5318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5318_, 0, v___x_5317_);
lean_ctor_set(v___x_5318_, 1, v___y_5308_);
return v___x_5318_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5319_, lean_object* v_s_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_){
_start:
{
lean_object* v_res_5323_; 
v_res_5323_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5319_, v_s_5320_, v___y_5321_, v___y_5322_);
lean_dec_ref(v___y_5321_);
return v_res_5323_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5341_; lean_object* v___x_5342_; 
v___x_5341_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5342_ = l_String_toRawSubstring_x27(v___x_5341_);
return v___x_5342_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5363_, lean_object* v_type_5364_, lean_object* v_ofInterpFn_5365_, lean_object* v_ofLitFn_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_){
_start:
{
lean_object* v___f_5369_; lean_object* v___f_5370_; lean_object* v___f_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; 
v___f_5369_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5370_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5370_, 0, v_ofInterpFn_5365_);
v___f_5371_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5371_, 0, v_ofLitFn_5366_);
v___x_5372_ = l_Lean_Syntax_getArgs(v_interpStr_5363_);
v___x_5373_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5372_, v___f_5369_, v___f_5370_, v___f_5371_, v_a_5367_, v_a_5368_);
lean_dec_ref(v___x_5372_);
if (lean_obj_tag(v___x_5373_) == 0)
{
lean_object* v_a_5374_; lean_object* v_a_5375_; lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5406_; 
v_a_5374_ = lean_ctor_get(v___x_5373_, 0);
v_a_5375_ = lean_ctor_get(v___x_5373_, 1);
v_isSharedCheck_5406_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5406_ == 0)
{
v___x_5377_ = v___x_5373_;
v_isShared_5378_ = v_isSharedCheck_5406_;
goto v_resetjp_5376_;
}
else
{
lean_inc(v_a_5375_);
lean_inc(v_a_5374_);
lean_dec(v___x_5373_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5406_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
lean_object* v_quotContext_5379_; lean_object* v_currMacroScope_5380_; lean_object* v_ref_5381_; uint8_t v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5404_; 
v_quotContext_5379_ = lean_ctor_get(v_a_5367_, 1);
v_currMacroScope_5380_ = lean_ctor_get(v_a_5367_, 2);
v_ref_5381_ = lean_ctor_get(v_a_5367_, 5);
v___x_5382_ = 0;
v___x_5383_ = l_Lean_SourceInfo_fromRef(v_ref_5381_, v___x_5382_);
v___x_5384_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5385_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5386_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc_n(v___x_5383_, 7);
v___x_5387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5387_, 0, v___x_5383_);
lean_ctor_set(v___x_5387_, 1, v___x_5386_);
v___x_5388_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5389_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5390_ = lean_box(0);
lean_inc(v_currMacroScope_5380_);
lean_inc(v_quotContext_5379_);
v___x_5391_ = l_Lean_addMacroScope(v_quotContext_5379_, v___x_5390_, v_currMacroScope_5380_);
v___x_5392_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
v___x_5393_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5393_, 0, v___x_5383_);
lean_ctor_set(v___x_5393_, 1, v___x_5389_);
lean_ctor_set(v___x_5393_, 2, v___x_5391_);
lean_ctor_set(v___x_5393_, 3, v___x_5392_);
v___x_5394_ = l_Lean_Syntax_node1(v___x_5383_, v___x_5388_, v___x_5393_);
v___x_5395_ = l_Lean_Syntax_node2(v___x_5383_, v___x_5385_, v___x_5387_, v___x_5394_);
v___x_5396_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_5397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5397_, 0, v___x_5383_);
lean_ctor_set(v___x_5397_, 1, v___x_5396_);
v___x_5398_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5399_ = l_Lean_Syntax_node1(v___x_5383_, v___x_5398_, v_type_5364_);
v___x_5400_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
v___x_5401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5401_, 0, v___x_5383_);
lean_ctor_set(v___x_5401_, 1, v___x_5400_);
v___x_5402_ = l_Lean_Syntax_node5(v___x_5383_, v___x_5384_, v___x_5395_, v_a_5374_, v___x_5397_, v___x_5399_, v___x_5401_);
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 0, v___x_5402_);
v___x_5404_ = v___x_5377_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v___x_5402_);
lean_ctor_set(v_reuseFailAlloc_5405_, 1, v_a_5375_);
v___x_5404_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5403_;
}
v_reusejp_5403_:
{
return v___x_5404_;
}
}
}
else
{
lean_object* v_a_5407_; lean_object* v_a_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5415_; 
lean_dec(v_type_5364_);
v_a_5407_ = lean_ctor_get(v___x_5373_, 0);
v_a_5408_ = lean_ctor_get(v___x_5373_, 1);
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5410_ = v___x_5373_;
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_a_5408_);
lean_inc(v_a_5407_);
lean_dec(v___x_5373_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v___x_5413_; 
if (v_isShared_5411_ == 0)
{
v___x_5413_ = v___x_5410_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5407_);
lean_ctor_set(v_reuseFailAlloc_5414_, 1, v_a_5408_);
v___x_5413_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
return v___x_5413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5416_, lean_object* v_type_5417_, lean_object* v_ofInterpFn_5418_, lean_object* v_ofLitFn_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_){
_start:
{
lean_object* v_res_5422_; 
v_res_5422_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5416_, v_type_5417_, v_ofInterpFn_5418_, v_ofLitFn_5419_, v_a_5420_, v_a_5421_);
lean_dec_ref(v_a_5420_);
lean_dec(v_interpStr_5416_);
return v_res_5422_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5423_){
_start:
{
lean_object* v___x_5424_; lean_object* v___x_5425_; 
v___x_5424_ = lean_unsigned_to_nat(1u);
v___x_5425_ = l_Lean_Syntax_getArg(v_stx_5423_, v___x_5424_);
if (lean_obj_tag(v___x_5425_) == 1)
{
lean_object* v_kind_5426_; 
v_kind_5426_ = lean_ctor_get(v___x_5425_, 1);
lean_inc(v_kind_5426_);
if (lean_obj_tag(v_kind_5426_) == 1)
{
lean_object* v_pre_5427_; 
v_pre_5427_ = lean_ctor_get(v_kind_5426_, 0);
lean_inc(v_pre_5427_);
if (lean_obj_tag(v_pre_5427_) == 1)
{
lean_object* v_pre_5428_; 
v_pre_5428_ = lean_ctor_get(v_pre_5427_, 0);
lean_inc(v_pre_5428_);
if (lean_obj_tag(v_pre_5428_) == 1)
{
lean_object* v_pre_5429_; 
v_pre_5429_ = lean_ctor_get(v_pre_5428_, 0);
lean_inc(v_pre_5429_);
if (lean_obj_tag(v_pre_5429_) == 1)
{
lean_object* v_pre_5430_; 
v_pre_5430_ = lean_ctor_get(v_pre_5429_, 0);
if (lean_obj_tag(v_pre_5430_) == 0)
{
lean_object* v_args_5431_; lean_object* v_str_5432_; lean_object* v_str_5433_; lean_object* v_str_5434_; lean_object* v_str_5435_; lean_object* v___x_5436_; uint8_t v___x_5437_; 
v_args_5431_ = lean_ctor_get(v___x_5425_, 2);
lean_inc_ref(v_args_5431_);
lean_dec_ref_known(v___x_5425_, 3);
v_str_5432_ = lean_ctor_get(v_kind_5426_, 1);
lean_inc_ref(v_str_5432_);
lean_dec_ref_known(v_kind_5426_, 2);
v_str_5433_ = lean_ctor_get(v_pre_5427_, 1);
lean_inc_ref(v_str_5433_);
lean_dec_ref_known(v_pre_5427_, 2);
v_str_5434_ = lean_ctor_get(v_pre_5428_, 1);
lean_inc_ref(v_str_5434_);
lean_dec_ref_known(v_pre_5428_, 2);
v_str_5435_ = lean_ctor_get(v_pre_5429_, 1);
lean_inc_ref(v_str_5435_);
lean_dec_ref_known(v_pre_5429_, 2);
v___x_5436_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__0));
v___x_5437_ = lean_string_dec_eq(v_str_5435_, v___x_5436_);
lean_dec_ref(v_str_5435_);
if (v___x_5437_ == 0)
{
lean_object* v___x_5438_; 
lean_dec_ref(v_str_5434_);
lean_dec_ref(v_str_5433_);
lean_dec_ref(v_str_5432_);
lean_dec_ref(v_args_5431_);
v___x_5438_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5438_;
}
else
{
lean_object* v___x_5439_; uint8_t v___x_5440_; 
v___x_5439_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__1));
v___x_5440_ = lean_string_dec_eq(v_str_5434_, v___x_5439_);
lean_dec_ref(v_str_5434_);
if (v___x_5440_ == 0)
{
lean_object* v___x_5441_; 
lean_dec_ref(v_str_5433_);
lean_dec_ref(v_str_5432_);
lean_dec_ref(v_args_5431_);
v___x_5441_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5441_;
}
else
{
lean_object* v___x_5442_; uint8_t v___x_5443_; 
v___x_5442_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__0));
v___x_5443_ = lean_string_dec_eq(v_str_5433_, v___x_5442_);
lean_dec_ref(v_str_5433_);
if (v___x_5443_ == 0)
{
lean_object* v___x_5444_; 
lean_dec_ref(v_str_5432_);
lean_dec_ref(v_args_5431_);
v___x_5444_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5444_;
}
else
{
lean_object* v___x_5445_; uint8_t v___x_5446_; 
v___x_5445_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__1));
v___x_5446_ = lean_string_dec_eq(v_str_5432_, v___x_5445_);
lean_dec_ref(v_str_5432_);
if (v___x_5446_ == 0)
{
lean_object* v___x_5447_; 
lean_dec_ref(v_args_5431_);
v___x_5447_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5447_;
}
else
{
lean_object* v___x_5448_; lean_object* v___x_5449_; uint8_t v___x_5450_; 
v___x_5448_ = lean_array_get_size(v_args_5431_);
v___x_5449_ = lean_unsigned_to_nat(2u);
v___x_5450_ = lean_nat_dec_eq(v___x_5448_, v___x_5449_);
if (v___x_5450_ == 0)
{
lean_object* v___x_5451_; 
lean_dec_ref(v_args_5431_);
v___x_5451_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5451_;
}
else
{
lean_object* v___x_5452_; lean_object* v___x_5453_; 
v___x_5452_ = lean_unsigned_to_nat(0u);
v___x_5453_ = lean_array_fget(v_args_5431_, v___x_5452_);
lean_dec_ref(v_args_5431_);
if (lean_obj_tag(v___x_5453_) == 2)
{
lean_object* v_val_5454_; 
v_val_5454_ = lean_ctor_get(v___x_5453_, 1);
lean_inc_ref(v_val_5454_);
lean_dec_ref_known(v___x_5453_, 2);
return v_val_5454_;
}
else
{
lean_object* v___x_5455_; 
lean_dec(v___x_5453_);
v___x_5455_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5455_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5456_; 
lean_dec_ref_known(v_pre_5429_, 2);
lean_dec_ref_known(v_pre_5428_, 2);
lean_dec_ref_known(v_pre_5427_, 2);
lean_dec_ref_known(v_kind_5426_, 2);
lean_dec_ref_known(v___x_5425_, 3);
v___x_5456_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5456_;
}
}
else
{
lean_object* v___x_5457_; 
lean_dec_ref_known(v_pre_5428_, 2);
lean_dec(v_pre_5429_);
lean_dec_ref_known(v_pre_5427_, 2);
lean_dec_ref_known(v_kind_5426_, 2);
lean_dec_ref_known(v___x_5425_, 3);
v___x_5457_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5457_;
}
}
else
{
lean_object* v___x_5458_; 
lean_dec(v_pre_5428_);
lean_dec_ref_known(v_pre_5427_, 2);
lean_dec_ref_known(v_kind_5426_, 2);
lean_dec_ref_known(v___x_5425_, 3);
v___x_5458_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5458_;
}
}
else
{
lean_object* v___x_5459_; 
lean_dec_ref_known(v_kind_5426_, 2);
lean_dec(v_pre_5427_);
lean_dec_ref_known(v___x_5425_, 3);
v___x_5459_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5459_;
}
}
else
{
lean_object* v___x_5460_; 
lean_dec(v_kind_5426_);
lean_dec_ref_known(v___x_5425_, 3);
v___x_5460_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5460_;
}
}
else
{
lean_object* v___x_5461_; 
lean_dec(v___x_5425_);
v___x_5461_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* v_stx_5462_){
_start:
{
lean_object* v_res_5463_; 
v_res_5463_ = l_Lean_TSyntax_getDocString(v_stx_5462_);
lean_dec(v_stx_5462_);
return v_res_5463_;
}
}
lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5482_, lean_object* v_prec_5483_){
_start:
{
lean_object* v___y_5485_; lean_object* v___y_5492_; lean_object* v___y_5499_; lean_object* v___y_5506_; lean_object* v___y_5513_; lean_object* v___y_5520_; 
switch(v_x_5482_)
{
case 0:
{
lean_object* v___x_5526_; uint8_t v___x_5527_; 
v___x_5526_ = lean_unsigned_to_nat(1024u);
v___x_5527_ = lean_nat_dec_le(v___x_5526_, v_prec_5483_);
if (v___x_5527_ == 0)
{
lean_object* v___x_5528_; 
v___x_5528_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5485_ = v___x_5528_;
goto v___jp_5484_;
}
else
{
lean_object* v___x_5529_; 
v___x_5529_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5485_ = v___x_5529_;
goto v___jp_5484_;
}
}
case 1:
{
lean_object* v___x_5530_; uint8_t v___x_5531_; 
v___x_5530_ = lean_unsigned_to_nat(1024u);
v___x_5531_ = lean_nat_dec_le(v___x_5530_, v_prec_5483_);
if (v___x_5531_ == 0)
{
lean_object* v___x_5532_; 
v___x_5532_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5492_ = v___x_5532_;
goto v___jp_5491_;
}
else
{
lean_object* v___x_5533_; 
v___x_5533_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5492_ = v___x_5533_;
goto v___jp_5491_;
}
}
case 2:
{
lean_object* v___x_5534_; uint8_t v___x_5535_; 
v___x_5534_ = lean_unsigned_to_nat(1024u);
v___x_5535_ = lean_nat_dec_le(v___x_5534_, v_prec_5483_);
if (v___x_5535_ == 0)
{
lean_object* v___x_5536_; 
v___x_5536_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5499_ = v___x_5536_;
goto v___jp_5498_;
}
else
{
lean_object* v___x_5537_; 
v___x_5537_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5499_ = v___x_5537_;
goto v___jp_5498_;
}
}
case 3:
{
lean_object* v___x_5538_; uint8_t v___x_5539_; 
v___x_5538_ = lean_unsigned_to_nat(1024u);
v___x_5539_ = lean_nat_dec_le(v___x_5538_, v_prec_5483_);
if (v___x_5539_ == 0)
{
lean_object* v___x_5540_; 
v___x_5540_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5506_ = v___x_5540_;
goto v___jp_5505_;
}
else
{
lean_object* v___x_5541_; 
v___x_5541_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5506_ = v___x_5541_;
goto v___jp_5505_;
}
}
case 4:
{
lean_object* v___x_5542_; uint8_t v___x_5543_; 
v___x_5542_ = lean_unsigned_to_nat(1024u);
v___x_5543_ = lean_nat_dec_le(v___x_5542_, v_prec_5483_);
if (v___x_5543_ == 0)
{
lean_object* v___x_5544_; 
v___x_5544_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5513_ = v___x_5544_;
goto v___jp_5512_;
}
else
{
lean_object* v___x_5545_; 
v___x_5545_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5513_ = v___x_5545_;
goto v___jp_5512_;
}
}
default: 
{
lean_object* v___x_5546_; uint8_t v___x_5547_; 
v___x_5546_ = lean_unsigned_to_nat(1024u);
v___x_5547_ = lean_nat_dec_le(v___x_5546_, v_prec_5483_);
if (v___x_5547_ == 0)
{
lean_object* v___x_5548_; 
v___x_5548_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5520_ = v___x_5548_;
goto v___jp_5519_;
}
else
{
lean_object* v___x_5549_; 
v___x_5549_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5520_ = v___x_5549_;
goto v___jp_5519_;
}
}
}
v___jp_5484_:
{
lean_object* v___x_5486_; lean_object* v___x_5487_; uint8_t v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; 
v___x_5486_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
lean_inc(v___y_5485_);
v___x_5487_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5487_, 0, v___y_5485_);
lean_ctor_set(v___x_5487_, 1, v___x_5486_);
v___x_5488_ = 0;
v___x_5489_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5489_, 0, v___x_5487_);
lean_ctor_set_uint8(v___x_5489_, sizeof(void*)*1, v___x_5488_);
v___x_5490_ = l_Repr_addAppParen(v___x_5489_, v_prec_5483_);
return v___x_5490_;
}
v___jp_5491_:
{
lean_object* v___x_5493_; lean_object* v___x_5494_; uint8_t v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; 
v___x_5493_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__3));
lean_inc(v___y_5492_);
v___x_5494_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5494_, 0, v___y_5492_);
lean_ctor_set(v___x_5494_, 1, v___x_5493_);
v___x_5495_ = 0;
v___x_5496_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5496_, 0, v___x_5494_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*1, v___x_5495_);
v___x_5497_ = l_Repr_addAppParen(v___x_5496_, v_prec_5483_);
return v___x_5497_;
}
v___jp_5498_:
{
lean_object* v___x_5500_; lean_object* v___x_5501_; uint8_t v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; 
v___x_5500_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__5));
lean_inc(v___y_5499_);
v___x_5501_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5501_, 0, v___y_5499_);
lean_ctor_set(v___x_5501_, 1, v___x_5500_);
v___x_5502_ = 0;
v___x_5503_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5503_, 0, v___x_5501_);
lean_ctor_set_uint8(v___x_5503_, sizeof(void*)*1, v___x_5502_);
v___x_5504_ = l_Repr_addAppParen(v___x_5503_, v_prec_5483_);
return v___x_5504_;
}
v___jp_5505_:
{
lean_object* v___x_5507_; lean_object* v___x_5508_; uint8_t v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; 
v___x_5507_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__7));
lean_inc(v___y_5506_);
v___x_5508_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5508_, 0, v___y_5506_);
lean_ctor_set(v___x_5508_, 1, v___x_5507_);
v___x_5509_ = 0;
v___x_5510_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5510_, 0, v___x_5508_);
lean_ctor_set_uint8(v___x_5510_, sizeof(void*)*1, v___x_5509_);
v___x_5511_ = l_Repr_addAppParen(v___x_5510_, v_prec_5483_);
return v___x_5511_;
}
v___jp_5512_:
{
lean_object* v___x_5514_; lean_object* v___x_5515_; uint8_t v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; 
v___x_5514_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__9));
lean_inc(v___y_5513_);
v___x_5515_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5515_, 0, v___y_5513_);
lean_ctor_set(v___x_5515_, 1, v___x_5514_);
v___x_5516_ = 0;
v___x_5517_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5517_, 0, v___x_5515_);
lean_ctor_set_uint8(v___x_5517_, sizeof(void*)*1, v___x_5516_);
v___x_5518_ = l_Repr_addAppParen(v___x_5517_, v_prec_5483_);
return v___x_5518_;
}
v___jp_5519_:
{
lean_object* v___x_5521_; lean_object* v___x_5522_; uint8_t v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; 
v___x_5521_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__11));
lean_inc(v___y_5520_);
v___x_5522_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5522_, 0, v___y_5520_);
lean_ctor_set(v___x_5522_, 1, v___x_5521_);
v___x_5523_ = 0;
v___x_5524_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5524_, 0, v___x_5522_);
lean_ctor_set_uint8(v___x_5524_, sizeof(void*)*1, v___x_5523_);
v___x_5525_ = l_Repr_addAppParen(v___x_5524_, v_prec_5483_);
return v___x_5525_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReprTransparencyMode_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_5482_ = stack[0].m_num;
lean_object* v_prec_5483_ = stack[1].m_obj;
lean_object* v_res_5550_;
v_res_5550_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_5482_, v_prec_5483_);
stack->m_obj
 = v_res_5550_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5551_, lean_object* v_prec_5552_){
_start:
{
uint8_t v_x_329__boxed_5553_; lean_object* v_res_5554_; 
v_x_329__boxed_5553_ = lean_unbox(v_x_5551_);
v_res_5554_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_329__boxed_5553_, v_prec_5552_);
lean_dec(v_prec_5552_);
return v_res_5554_;
}
}
lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5566_, lean_object* v_prec_5567_){
_start:
{
lean_object* v___y_5569_; lean_object* v___y_5576_; lean_object* v___y_5583_; 
switch(v_x_5566_)
{
case 0:
{
lean_object* v___x_5589_; uint8_t v___x_5590_; 
v___x_5589_ = lean_unsigned_to_nat(1024u);
v___x_5590_ = lean_nat_dec_le(v___x_5589_, v_prec_5567_);
if (v___x_5590_ == 0)
{
lean_object* v___x_5591_; 
v___x_5591_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5569_ = v___x_5591_;
goto v___jp_5568_;
}
else
{
lean_object* v___x_5592_; 
v___x_5592_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5569_ = v___x_5592_;
goto v___jp_5568_;
}
}
case 1:
{
lean_object* v___x_5593_; uint8_t v___x_5594_; 
v___x_5593_ = lean_unsigned_to_nat(1024u);
v___x_5594_ = lean_nat_dec_le(v___x_5593_, v_prec_5567_);
if (v___x_5594_ == 0)
{
lean_object* v___x_5595_; 
v___x_5595_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5576_ = v___x_5595_;
goto v___jp_5575_;
}
else
{
lean_object* v___x_5596_; 
v___x_5596_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5576_ = v___x_5596_;
goto v___jp_5575_;
}
}
default: 
{
lean_object* v___x_5597_; uint8_t v___x_5598_; 
v___x_5597_ = lean_unsigned_to_nat(1024u);
v___x_5598_ = lean_nat_dec_le(v___x_5597_, v_prec_5567_);
if (v___x_5598_ == 0)
{
lean_object* v___x_5599_; 
v___x_5599_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5583_ = v___x_5599_;
goto v___jp_5582_;
}
else
{
lean_object* v___x_5600_; 
v___x_5600_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5583_ = v___x_5600_;
goto v___jp_5582_;
}
}
}
v___jp_5568_:
{
lean_object* v___x_5570_; lean_object* v___x_5571_; uint8_t v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; 
v___x_5570_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
lean_inc(v___y_5569_);
v___x_5571_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5571_, 0, v___y_5569_);
lean_ctor_set(v___x_5571_, 1, v___x_5570_);
v___x_5572_ = 0;
v___x_5573_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5573_, 0, v___x_5571_);
lean_ctor_set_uint8(v___x_5573_, sizeof(void*)*1, v___x_5572_);
v___x_5574_ = l_Repr_addAppParen(v___x_5573_, v_prec_5567_);
return v___x_5574_;
}
v___jp_5575_:
{
lean_object* v___x_5577_; lean_object* v___x_5578_; uint8_t v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; 
v___x_5577_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
lean_inc(v___y_5576_);
v___x_5578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5578_, 0, v___y_5576_);
lean_ctor_set(v___x_5578_, 1, v___x_5577_);
v___x_5579_ = 0;
v___x_5580_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5580_, 0, v___x_5578_);
lean_ctor_set_uint8(v___x_5580_, sizeof(void*)*1, v___x_5579_);
v___x_5581_ = l_Repr_addAppParen(v___x_5580_, v_prec_5567_);
return v___x_5581_;
}
v___jp_5582_:
{
lean_object* v___x_5584_; lean_object* v___x_5585_; uint8_t v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; 
v___x_5584_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
lean_inc(v___y_5583_);
v___x_5585_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5585_, 0, v___y_5583_);
lean_ctor_set(v___x_5585_, 1, v___x_5584_);
v___x_5586_ = 0;
v___x_5587_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5587_, 0, v___x_5585_);
lean_ctor_set_uint8(v___x_5587_, sizeof(void*)*1, v___x_5586_);
v___x_5588_ = l_Repr_addAppParen(v___x_5587_, v_prec_5567_);
return v___x_5588_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReprEtaStructMode_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_5566_ = stack[0].m_num;
lean_object* v_prec_5567_ = stack[1].m_obj;
lean_object* v_res_5601_;
v_res_5601_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_5566_, v_prec_5567_);
stack->m_obj
 = v_res_5601_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5602_, lean_object* v_prec_5603_){
_start:
{
uint8_t v_x_167__boxed_5604_; lean_object* v_res_5605_; 
v_x_167__boxed_5604_ = lean_unbox(v_x_5602_);
v_res_5605_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_167__boxed_5604_, v_prec_5603_);
lean_dec(v_prec_5603_);
return v_res_5605_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5617_; lean_object* v___x_5618_; 
v___x_5617_ = lean_unsigned_to_nat(8u);
v___x_5618_ = lean_nat_to_int(v___x_5617_);
return v___x_5618_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5628_; lean_object* v___x_5629_; 
v___x_5628_ = lean_unsigned_to_nat(13u);
v___x_5629_ = lean_nat_to_int(v___x_5628_);
return v___x_5629_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5639_; lean_object* v___x_5640_; 
v___x_5639_ = lean_unsigned_to_nat(10u);
v___x_5640_ = lean_nat_to_int(v___x_5639_);
return v___x_5640_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5644_; lean_object* v___x_5645_; 
v___x_5644_ = lean_unsigned_to_nat(14u);
v___x_5645_ = lean_nat_to_int(v___x_5644_);
return v___x_5645_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5649_; lean_object* v___x_5650_; 
v___x_5649_ = lean_unsigned_to_nat(19u);
v___x_5650_ = lean_nat_to_int(v___x_5649_);
return v___x_5650_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5654_; lean_object* v___x_5655_; 
v___x_5654_ = lean_unsigned_to_nat(20u);
v___x_5655_ = lean_nat_to_int(v___x_5654_);
return v___x_5655_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5662_; lean_object* v___x_5663_; 
v___x_5662_ = lean_unsigned_to_nat(9u);
v___x_5663_ = lean_nat_to_int(v___x_5662_);
return v___x_5663_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5670_; lean_object* v___x_5671_; 
v___x_5670_ = lean_unsigned_to_nat(12u);
v___x_5671_ = lean_nat_to_int(v___x_5670_);
return v___x_5671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5678_){
_start:
{
uint8_t v_zeta_5679_; uint8_t v_beta_5680_; uint8_t v_eta_5681_; uint8_t v_etaStruct_5682_; uint8_t v_iota_5683_; uint8_t v_proj_5684_; uint8_t v_decide_5685_; uint8_t v_autoUnfold_5686_; uint8_t v_failIfUnchanged_5687_; uint8_t v_unfoldPartialApp_5688_; uint8_t v_zetaDelta_5689_; uint8_t v_index_5690_; uint8_t v_zetaUnused_5691_; uint8_t v_zetaHave_5692_; uint8_t v_locals_5693_; uint8_t v_instances_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; uint8_t v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; 
v_zeta_5679_ = lean_ctor_get_uint8(v_x_5678_, 0);
v_beta_5680_ = lean_ctor_get_uint8(v_x_5678_, 1);
v_eta_5681_ = lean_ctor_get_uint8(v_x_5678_, 2);
v_etaStruct_5682_ = lean_ctor_get_uint8(v_x_5678_, 3);
v_iota_5683_ = lean_ctor_get_uint8(v_x_5678_, 4);
v_proj_5684_ = lean_ctor_get_uint8(v_x_5678_, 5);
v_decide_5685_ = lean_ctor_get_uint8(v_x_5678_, 6);
v_autoUnfold_5686_ = lean_ctor_get_uint8(v_x_5678_, 7);
v_failIfUnchanged_5687_ = lean_ctor_get_uint8(v_x_5678_, 8);
v_unfoldPartialApp_5688_ = lean_ctor_get_uint8(v_x_5678_, 9);
v_zetaDelta_5689_ = lean_ctor_get_uint8(v_x_5678_, 10);
v_index_5690_ = lean_ctor_get_uint8(v_x_5678_, 11);
v_zetaUnused_5691_ = lean_ctor_get_uint8(v_x_5678_, 12);
v_zetaHave_5692_ = lean_ctor_get_uint8(v_x_5678_, 13);
v_locals_5693_ = lean_ctor_get_uint8(v_x_5678_, 14);
v_instances_5694_ = lean_ctor_get_uint8(v_x_5678_, 15);
v___x_5695_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5696_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5697_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5698_ = lean_unsigned_to_nat(0u);
v___x_5699_ = l_Bool_repr___redArg(v_zeta_5679_);
v___x_5700_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5697_);
lean_ctor_set(v___x_5700_, 1, v___x_5699_);
v___x_5701_ = 0;
v___x_5702_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5702_, 0, v___x_5700_);
lean_ctor_set_uint8(v___x_5702_, sizeof(void*)*1, v___x_5701_);
v___x_5703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5703_, 0, v___x_5696_);
lean_ctor_set(v___x_5703_, 1, v___x_5702_);
v___x_5704_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5705_, 0, v___x_5703_);
lean_ctor_set(v___x_5705_, 1, v___x_5704_);
v___x_5706_ = lean_box(1);
v___x_5707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5707_, 0, v___x_5705_);
lean_ctor_set(v___x_5707_, 1, v___x_5706_);
v___x_5708_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5707_);
lean_ctor_set(v___x_5709_, 1, v___x_5708_);
v___x_5710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5710_, 0, v___x_5709_);
lean_ctor_set(v___x_5710_, 1, v___x_5695_);
v___x_5711_ = l_Bool_repr___redArg(v_beta_5680_);
v___x_5712_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5712_, 0, v___x_5697_);
lean_ctor_set(v___x_5712_, 1, v___x_5711_);
v___x_5713_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5713_, 0, v___x_5712_);
lean_ctor_set_uint8(v___x_5713_, sizeof(void*)*1, v___x_5701_);
v___x_5714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5710_);
lean_ctor_set(v___x_5714_, 1, v___x_5713_);
v___x_5715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5714_);
lean_ctor_set(v___x_5715_, 1, v___x_5704_);
v___x_5716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5716_, 0, v___x_5715_);
lean_ctor_set(v___x_5716_, 1, v___x_5706_);
v___x_5717_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5718_, 0, v___x_5716_);
lean_ctor_set(v___x_5718_, 1, v___x_5717_);
v___x_5719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5719_, 0, v___x_5718_);
lean_ctor_set(v___x_5719_, 1, v___x_5695_);
v___x_5720_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5721_ = l_Bool_repr___redArg(v_eta_5681_);
v___x_5722_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5722_, 0, v___x_5720_);
lean_ctor_set(v___x_5722_, 1, v___x_5721_);
v___x_5723_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5723_, 0, v___x_5722_);
lean_ctor_set_uint8(v___x_5723_, sizeof(void*)*1, v___x_5701_);
v___x_5724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5724_, 0, v___x_5719_);
lean_ctor_set(v___x_5724_, 1, v___x_5723_);
v___x_5725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5725_, 0, v___x_5724_);
lean_ctor_set(v___x_5725_, 1, v___x_5704_);
v___x_5726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5726_, 0, v___x_5725_);
lean_ctor_set(v___x_5726_, 1, v___x_5706_);
v___x_5727_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5726_);
lean_ctor_set(v___x_5728_, 1, v___x_5727_);
v___x_5729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5728_);
lean_ctor_set(v___x_5729_, 1, v___x_5695_);
v___x_5730_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5731_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5682_, v___x_5698_);
v___x_5732_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5730_);
lean_ctor_set(v___x_5732_, 1, v___x_5731_);
v___x_5733_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5733_, 0, v___x_5732_);
lean_ctor_set_uint8(v___x_5733_, sizeof(void*)*1, v___x_5701_);
v___x_5734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5734_, 0, v___x_5729_);
lean_ctor_set(v___x_5734_, 1, v___x_5733_);
v___x_5735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5735_, 0, v___x_5734_);
lean_ctor_set(v___x_5735_, 1, v___x_5704_);
v___x_5736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5735_);
lean_ctor_set(v___x_5736_, 1, v___x_5706_);
v___x_5737_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5736_);
lean_ctor_set(v___x_5738_, 1, v___x_5737_);
v___x_5739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5739_, 0, v___x_5738_);
lean_ctor_set(v___x_5739_, 1, v___x_5695_);
v___x_5740_ = l_Bool_repr___redArg(v_iota_5683_);
v___x_5741_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5741_, 0, v___x_5697_);
lean_ctor_set(v___x_5741_, 1, v___x_5740_);
v___x_5742_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5742_, 0, v___x_5741_);
lean_ctor_set_uint8(v___x_5742_, sizeof(void*)*1, v___x_5701_);
v___x_5743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5739_);
lean_ctor_set(v___x_5743_, 1, v___x_5742_);
v___x_5744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5744_, 0, v___x_5743_);
lean_ctor_set(v___x_5744_, 1, v___x_5704_);
v___x_5745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5745_, 0, v___x_5744_);
lean_ctor_set(v___x_5745_, 1, v___x_5706_);
v___x_5746_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5747_, 0, v___x_5745_);
lean_ctor_set(v___x_5747_, 1, v___x_5746_);
v___x_5748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5748_, 0, v___x_5747_);
lean_ctor_set(v___x_5748_, 1, v___x_5695_);
v___x_5749_ = l_Bool_repr___redArg(v_proj_5684_);
v___x_5750_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5750_, 0, v___x_5697_);
lean_ctor_set(v___x_5750_, 1, v___x_5749_);
v___x_5751_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5751_, 0, v___x_5750_);
lean_ctor_set_uint8(v___x_5751_, sizeof(void*)*1, v___x_5701_);
v___x_5752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5752_, 0, v___x_5748_);
lean_ctor_set(v___x_5752_, 1, v___x_5751_);
v___x_5753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5753_, 0, v___x_5752_);
lean_ctor_set(v___x_5753_, 1, v___x_5704_);
v___x_5754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5754_, 0, v___x_5753_);
lean_ctor_set(v___x_5754_, 1, v___x_5706_);
v___x_5755_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5754_);
lean_ctor_set(v___x_5756_, 1, v___x_5755_);
v___x_5757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5757_, 0, v___x_5756_);
lean_ctor_set(v___x_5757_, 1, v___x_5695_);
v___x_5758_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5759_ = l_Bool_repr___redArg(v_decide_5685_);
v___x_5760_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5760_, 0, v___x_5758_);
lean_ctor_set(v___x_5760_, 1, v___x_5759_);
v___x_5761_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5761_, 0, v___x_5760_);
lean_ctor_set_uint8(v___x_5761_, sizeof(void*)*1, v___x_5701_);
v___x_5762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5762_, 0, v___x_5757_);
lean_ctor_set(v___x_5762_, 1, v___x_5761_);
v___x_5763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5763_, 0, v___x_5762_);
lean_ctor_set(v___x_5763_, 1, v___x_5704_);
v___x_5764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5764_, 0, v___x_5763_);
lean_ctor_set(v___x_5764_, 1, v___x_5706_);
v___x_5765_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5766_, 0, v___x_5764_);
lean_ctor_set(v___x_5766_, 1, v___x_5765_);
v___x_5767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5767_, 0, v___x_5766_);
lean_ctor_set(v___x_5767_, 1, v___x_5695_);
v___x_5768_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5769_ = l_Bool_repr___redArg(v_autoUnfold_5686_);
v___x_5770_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5770_, 0, v___x_5768_);
lean_ctor_set(v___x_5770_, 1, v___x_5769_);
v___x_5771_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5771_, 0, v___x_5770_);
lean_ctor_set_uint8(v___x_5771_, sizeof(void*)*1, v___x_5701_);
v___x_5772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5772_, 0, v___x_5767_);
lean_ctor_set(v___x_5772_, 1, v___x_5771_);
v___x_5773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5773_, 0, v___x_5772_);
lean_ctor_set(v___x_5773_, 1, v___x_5704_);
v___x_5774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5774_, 0, v___x_5773_);
lean_ctor_set(v___x_5774_, 1, v___x_5706_);
v___x_5775_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5776_, 0, v___x_5774_);
lean_ctor_set(v___x_5776_, 1, v___x_5775_);
v___x_5777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5777_, 0, v___x_5776_);
lean_ctor_set(v___x_5777_, 1, v___x_5695_);
v___x_5778_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5779_ = l_Bool_repr___redArg(v_failIfUnchanged_5687_);
v___x_5780_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5780_, 0, v___x_5778_);
lean_ctor_set(v___x_5780_, 1, v___x_5779_);
v___x_5781_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5781_, 0, v___x_5780_);
lean_ctor_set_uint8(v___x_5781_, sizeof(void*)*1, v___x_5701_);
v___x_5782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5782_, 0, v___x_5777_);
lean_ctor_set(v___x_5782_, 1, v___x_5781_);
v___x_5783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5783_, 0, v___x_5782_);
lean_ctor_set(v___x_5783_, 1, v___x_5704_);
v___x_5784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5784_, 0, v___x_5783_);
lean_ctor_set(v___x_5784_, 1, v___x_5706_);
v___x_5785_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5786_, 0, v___x_5784_);
lean_ctor_set(v___x_5786_, 1, v___x_5785_);
v___x_5787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5787_, 0, v___x_5786_);
lean_ctor_set(v___x_5787_, 1, v___x_5695_);
v___x_5788_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5789_ = l_Bool_repr___redArg(v_unfoldPartialApp_5688_);
v___x_5790_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5790_, 0, v___x_5788_);
lean_ctor_set(v___x_5790_, 1, v___x_5789_);
v___x_5791_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5791_, 0, v___x_5790_);
lean_ctor_set_uint8(v___x_5791_, sizeof(void*)*1, v___x_5701_);
v___x_5792_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5792_, 0, v___x_5787_);
lean_ctor_set(v___x_5792_, 1, v___x_5791_);
v___x_5793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5793_, 0, v___x_5792_);
lean_ctor_set(v___x_5793_, 1, v___x_5704_);
v___x_5794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5794_, 0, v___x_5793_);
lean_ctor_set(v___x_5794_, 1, v___x_5706_);
v___x_5795_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5796_, 0, v___x_5794_);
lean_ctor_set(v___x_5796_, 1, v___x_5795_);
v___x_5797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5797_, 0, v___x_5796_);
lean_ctor_set(v___x_5797_, 1, v___x_5695_);
v___x_5798_ = l_Bool_repr___redArg(v_zetaDelta_5689_);
v___x_5799_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5799_, 0, v___x_5730_);
lean_ctor_set(v___x_5799_, 1, v___x_5798_);
v___x_5800_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5800_, 0, v___x_5799_);
lean_ctor_set_uint8(v___x_5800_, sizeof(void*)*1, v___x_5701_);
v___x_5801_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5801_, 0, v___x_5797_);
lean_ctor_set(v___x_5801_, 1, v___x_5800_);
v___x_5802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5802_, 0, v___x_5801_);
lean_ctor_set(v___x_5802_, 1, v___x_5704_);
v___x_5803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5803_, 0, v___x_5802_);
lean_ctor_set(v___x_5803_, 1, v___x_5706_);
v___x_5804_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5805_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5805_, 0, v___x_5803_);
lean_ctor_set(v___x_5805_, 1, v___x_5804_);
v___x_5806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5806_, 0, v___x_5805_);
lean_ctor_set(v___x_5806_, 1, v___x_5695_);
v___x_5807_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5808_ = l_Bool_repr___redArg(v_index_5690_);
v___x_5809_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5809_, 0, v___x_5807_);
lean_ctor_set(v___x_5809_, 1, v___x_5808_);
v___x_5810_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5810_, 0, v___x_5809_);
lean_ctor_set_uint8(v___x_5810_, sizeof(void*)*1, v___x_5701_);
v___x_5811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5811_, 0, v___x_5806_);
lean_ctor_set(v___x_5811_, 1, v___x_5810_);
v___x_5812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5812_, 0, v___x_5811_);
lean_ctor_set(v___x_5812_, 1, v___x_5704_);
v___x_5813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5813_, 0, v___x_5812_);
lean_ctor_set(v___x_5813_, 1, v___x_5706_);
v___x_5814_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5815_, 0, v___x_5813_);
lean_ctor_set(v___x_5815_, 1, v___x_5814_);
v___x_5816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5816_, 0, v___x_5815_);
lean_ctor_set(v___x_5816_, 1, v___x_5695_);
v___x_5817_ = l_Bool_repr___redArg(v_zetaUnused_5691_);
v___x_5818_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5818_, 0, v___x_5768_);
lean_ctor_set(v___x_5818_, 1, v___x_5817_);
v___x_5819_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5819_, 0, v___x_5818_);
lean_ctor_set_uint8(v___x_5819_, sizeof(void*)*1, v___x_5701_);
v___x_5820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5820_, 0, v___x_5816_);
lean_ctor_set(v___x_5820_, 1, v___x_5819_);
v___x_5821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5821_, 0, v___x_5820_);
lean_ctor_set(v___x_5821_, 1, v___x_5704_);
v___x_5822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5822_, 0, v___x_5821_);
lean_ctor_set(v___x_5822_, 1, v___x_5706_);
v___x_5823_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5824_, 0, v___x_5822_);
lean_ctor_set(v___x_5824_, 1, v___x_5823_);
v___x_5825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5825_, 0, v___x_5824_);
lean_ctor_set(v___x_5825_, 1, v___x_5695_);
v___x_5826_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5827_ = l_Bool_repr___redArg(v_zetaHave_5692_);
v___x_5828_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5828_, 0, v___x_5826_);
lean_ctor_set(v___x_5828_, 1, v___x_5827_);
v___x_5829_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5829_, 0, v___x_5828_);
lean_ctor_set_uint8(v___x_5829_, sizeof(void*)*1, v___x_5701_);
v___x_5830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5830_, 0, v___x_5825_);
lean_ctor_set(v___x_5830_, 1, v___x_5829_);
v___x_5831_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5831_, 0, v___x_5830_);
lean_ctor_set(v___x_5831_, 1, v___x_5704_);
v___x_5832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5832_, 0, v___x_5831_);
lean_ctor_set(v___x_5832_, 1, v___x_5706_);
v___x_5833_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5834_, 0, v___x_5832_);
lean_ctor_set(v___x_5834_, 1, v___x_5833_);
v___x_5835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5835_, 0, v___x_5834_);
lean_ctor_set(v___x_5835_, 1, v___x_5695_);
v___x_5836_ = l_Bool_repr___redArg(v_locals_5693_);
v___x_5837_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5837_, 0, v___x_5758_);
lean_ctor_set(v___x_5837_, 1, v___x_5836_);
v___x_5838_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5838_, 0, v___x_5837_);
lean_ctor_set_uint8(v___x_5838_, sizeof(void*)*1, v___x_5701_);
v___x_5839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5839_, 0, v___x_5835_);
lean_ctor_set(v___x_5839_, 1, v___x_5838_);
v___x_5840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5840_, 0, v___x_5839_);
lean_ctor_set(v___x_5840_, 1, v___x_5704_);
v___x_5841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5841_, 0, v___x_5840_);
lean_ctor_set(v___x_5841_, 1, v___x_5706_);
v___x_5842_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5843_, 0, v___x_5841_);
lean_ctor_set(v___x_5843_, 1, v___x_5842_);
v___x_5844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5844_, 0, v___x_5843_);
lean_ctor_set(v___x_5844_, 1, v___x_5695_);
v___x_5845_ = l_Bool_repr___redArg(v_instances_5694_);
v___x_5846_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5846_, 0, v___x_5730_);
lean_ctor_set(v___x_5846_, 1, v___x_5845_);
v___x_5847_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5847_, 0, v___x_5846_);
lean_ctor_set_uint8(v___x_5847_, sizeof(void*)*1, v___x_5701_);
v___x_5848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5848_, 0, v___x_5844_);
lean_ctor_set(v___x_5848_, 1, v___x_5847_);
v___x_5849_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5850_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5851_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5851_, 0, v___x_5850_);
lean_ctor_set(v___x_5851_, 1, v___x_5848_);
v___x_5852_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5853_, 0, v___x_5851_);
lean_ctor_set(v___x_5853_, 1, v___x_5852_);
v___x_5854_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5854_, 0, v___x_5849_);
lean_ctor_set(v___x_5854_, 1, v___x_5853_);
v___x_5855_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5855_, 0, v___x_5854_);
lean_ctor_set_uint8(v___x_5855_, sizeof(void*)*1, v___x_5701_);
return v___x_5855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5856_){
_start:
{
lean_object* v_res_5857_; 
v_res_5857_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5856_);
lean_dec_ref(v_x_5856_);
return v_res_5857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5858_, lean_object* v_prec_5859_){
_start:
{
lean_object* v___x_5860_; 
v___x_5860_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5858_);
return v___x_5860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5861_, lean_object* v_prec_5862_){
_start:
{
lean_object* v_res_5863_; 
v_res_5863_ = l_Lean_Meta_instReprConfig_repr(v_x_5861_, v_prec_5862_);
lean_dec(v_prec_5862_);
lean_dec_ref(v_x_5861_);
return v_res_5863_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5871_, lean_object* v_x_5872_){
_start:
{
if (lean_obj_tag(v_x_5871_) == 0)
{
lean_object* v___x_5873_; 
v___x_5873_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5873_;
}
else
{
lean_object* v_val_5874_; lean_object* v___x_5876_; uint8_t v_isShared_5877_; uint8_t v_isSharedCheck_5885_; 
v_val_5874_ = lean_ctor_get(v_x_5871_, 0);
v_isSharedCheck_5885_ = !lean_is_exclusive(v_x_5871_);
if (v_isSharedCheck_5885_ == 0)
{
v___x_5876_ = v_x_5871_;
v_isShared_5877_ = v_isSharedCheck_5885_;
goto v_resetjp_5875_;
}
else
{
lean_inc(v_val_5874_);
lean_dec(v_x_5871_);
v___x_5876_ = lean_box(0);
v_isShared_5877_ = v_isSharedCheck_5885_;
goto v_resetjp_5875_;
}
v_resetjp_5875_:
{
lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5881_; 
v___x_5878_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5879_ = l_Nat_reprFast(v_val_5874_);
if (v_isShared_5877_ == 0)
{
lean_ctor_set_tag(v___x_5876_, 3);
lean_ctor_set(v___x_5876_, 0, v___x_5879_);
v___x_5881_ = v___x_5876_;
goto v_reusejp_5880_;
}
else
{
lean_object* v_reuseFailAlloc_5884_; 
v_reuseFailAlloc_5884_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5884_, 0, v___x_5879_);
v___x_5881_ = v_reuseFailAlloc_5884_;
goto v_reusejp_5880_;
}
v_reusejp_5880_:
{
lean_object* v___x_5882_; lean_object* v___x_5883_; 
v___x_5882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5882_, 0, v___x_5878_);
lean_ctor_set(v___x_5882_, 1, v___x_5881_);
v___x_5883_ = l_Repr_addAppParen(v___x_5882_, v_x_5872_);
return v___x_5883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5886_, lean_object* v_x_5887_){
_start:
{
lean_object* v_res_5888_; 
v_res_5888_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5886_, v_x_5887_);
lean_dec(v_x_5887_);
return v_res_5888_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5901_; lean_object* v___x_5902_; 
v___x_5901_ = lean_unsigned_to_nat(21u);
v___x_5902_ = lean_nat_to_int(v___x_5901_);
return v___x_5902_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5909_; lean_object* v___x_5910_; 
v___x_5909_ = lean_unsigned_to_nat(11u);
v___x_5910_ = lean_nat_to_int(v___x_5909_);
return v___x_5910_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5926_; lean_object* v___x_5927_; 
v___x_5926_ = lean_unsigned_to_nat(23u);
v___x_5927_ = lean_nat_to_int(v___x_5926_);
return v___x_5927_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5931_; lean_object* v___x_5932_; 
v___x_5931_ = lean_unsigned_to_nat(16u);
v___x_5932_ = lean_nat_to_int(v___x_5931_);
return v___x_5932_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5939_; lean_object* v___x_5940_; 
v___x_5939_ = lean_unsigned_to_nat(15u);
v___x_5940_ = lean_nat_to_int(v___x_5939_);
return v___x_5940_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5947_; lean_object* v___x_5948_; 
v___x_5947_ = lean_unsigned_to_nat(17u);
v___x_5948_ = lean_nat_to_int(v___x_5947_);
return v___x_5948_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5955_; lean_object* v___x_5956_; 
v___x_5955_ = lean_unsigned_to_nat(18u);
v___x_5956_ = lean_nat_to_int(v___x_5955_);
return v___x_5956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5957_){
_start:
{
lean_object* v_maxSteps_5958_; lean_object* v_maxDischargeDepth_5959_; uint8_t v_contextual_5960_; uint8_t v_memoize_5961_; uint8_t v_singlePass_5962_; uint8_t v_zeta_5963_; uint8_t v_beta_5964_; uint8_t v_eta_5965_; uint8_t v_etaStruct_5966_; uint8_t v_iota_5967_; uint8_t v_proj_5968_; uint8_t v_decide_5969_; uint8_t v_arith_5970_; uint8_t v_autoUnfold_5971_; uint8_t v_dsimp_5972_; uint8_t v_failIfUnchanged_5973_; uint8_t v_ground_5974_; uint8_t v_unfoldPartialApp_5975_; uint8_t v_zetaDelta_5976_; uint8_t v_index_5977_; uint8_t v_implicitDefEqProofs_5978_; uint8_t v_zetaUnused_5979_; uint8_t v_catchRuntime_5980_; uint8_t v_zetaHave_5981_; uint8_t v_letToHave_5982_; uint8_t v_congrConsts_5983_; uint8_t v_bitVecOfNat_5984_; uint8_t v_warnExponents_5985_; uint8_t v_suggestions_5986_; lean_object* v_maxSuggestions_5987_; uint8_t v_locals_5988_; uint8_t v_instances_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; uint8_t v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; lean_object* v___x_6235_; lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; lean_object* v___x_6239_; lean_object* v___x_6240_; lean_object* v___x_6241_; lean_object* v___x_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; lean_object* v___x_6247_; lean_object* v___x_6248_; lean_object* v___x_6249_; lean_object* v___x_6250_; lean_object* v___x_6251_; lean_object* v___x_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; lean_object* v___x_6256_; lean_object* v___x_6257_; lean_object* v___x_6258_; lean_object* v___x_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; lean_object* v___x_6266_; lean_object* v___x_6267_; lean_object* v___x_6268_; lean_object* v___x_6269_; lean_object* v___x_6270_; lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___x_6273_; lean_object* v___x_6274_; lean_object* v___x_6275_; lean_object* v___x_6276_; lean_object* v___x_6277_; lean_object* v___x_6278_; lean_object* v___x_6279_; lean_object* v___x_6280_; lean_object* v___x_6281_; lean_object* v___x_6282_; lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; 
v_maxSteps_5958_ = lean_ctor_get(v_x_5957_, 0);
lean_inc(v_maxSteps_5958_);
v_maxDischargeDepth_5959_ = lean_ctor_get(v_x_5957_, 1);
lean_inc(v_maxDischargeDepth_5959_);
v_contextual_5960_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3);
v_memoize_5961_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 1);
v_singlePass_5962_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 2);
v_zeta_5963_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 3);
v_beta_5964_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 4);
v_eta_5965_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 5);
v_etaStruct_5966_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 6);
v_iota_5967_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 7);
v_proj_5968_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 8);
v_decide_5969_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 9);
v_arith_5970_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 10);
v_autoUnfold_5971_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 11);
v_dsimp_5972_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5973_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 13);
v_ground_5974_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5975_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 15);
v_zetaDelta_5976_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 16);
v_index_5977_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5978_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 18);
v_zetaUnused_5979_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 19);
v_catchRuntime_5980_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 20);
v_zetaHave_5981_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 21);
v_letToHave_5982_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 22);
v_congrConsts_5983_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5984_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 24);
v_warnExponents_5985_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 25);
v_suggestions_5986_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 26);
v_maxSuggestions_5987_ = lean_ctor_get(v_x_5957_, 2);
lean_inc(v_maxSuggestions_5987_);
v_locals_5988_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 27);
v_instances_5989_ = lean_ctor_get_uint8(v_x_5957_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5957_);
v___x_5990_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5991_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5992_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5993_ = l_Nat_reprFast(v_maxSteps_5958_);
v___x_5994_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5994_, 0, v___x_5993_);
v___x_5995_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5995_, 0, v___x_5992_);
lean_ctor_set(v___x_5995_, 1, v___x_5994_);
v___x_5996_ = 0;
v___x_5997_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5997_, 0, v___x_5995_);
lean_ctor_set_uint8(v___x_5997_, sizeof(void*)*1, v___x_5996_);
v___x_5998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5998_, 0, v___x_5991_);
lean_ctor_set(v___x_5998_, 1, v___x_5997_);
v___x_5999_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_6000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6000_, 0, v___x_5998_);
lean_ctor_set(v___x_6000_, 1, v___x_5999_);
v___x_6001_ = lean_box(1);
v___x_6002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6002_, 0, v___x_6000_);
lean_ctor_set(v___x_6002_, 1, v___x_6001_);
v___x_6003_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_6004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6004_, 0, v___x_6002_);
lean_ctor_set(v___x_6004_, 1, v___x_6003_);
v___x_6005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6005_, 0, v___x_6004_);
lean_ctor_set(v___x_6005_, 1, v___x_5990_);
v___x_6006_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_6007_ = l_Nat_reprFast(v_maxDischargeDepth_5959_);
v___x_6008_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6008_, 0, v___x_6007_);
v___x_6009_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6009_, 0, v___x_6006_);
lean_ctor_set(v___x_6009_, 1, v___x_6008_);
v___x_6010_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6010_, 0, v___x_6009_);
lean_ctor_set_uint8(v___x_6010_, sizeof(void*)*1, v___x_5996_);
v___x_6011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6011_, 0, v___x_6005_);
lean_ctor_set(v___x_6011_, 1, v___x_6010_);
v___x_6012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6012_, 0, v___x_6011_);
lean_ctor_set(v___x_6012_, 1, v___x_5999_);
v___x_6013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6012_);
lean_ctor_set(v___x_6013_, 1, v___x_6001_);
v___x_6014_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_6015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6013_);
lean_ctor_set(v___x_6015_, 1, v___x_6014_);
v___x_6016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6015_);
lean_ctor_set(v___x_6016_, 1, v___x_5990_);
v___x_6017_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_6018_ = lean_unsigned_to_nat(0u);
v___x_6019_ = l_Bool_repr___redArg(v_contextual_5960_);
v___x_6020_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6017_);
lean_ctor_set(v___x_6020_, 1, v___x_6019_);
v___x_6021_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6021_, 0, v___x_6020_);
lean_ctor_set_uint8(v___x_6021_, sizeof(void*)*1, v___x_5996_);
v___x_6022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6016_);
lean_ctor_set(v___x_6022_, 1, v___x_6021_);
v___x_6023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6022_);
lean_ctor_set(v___x_6023_, 1, v___x_5999_);
v___x_6024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6024_, 0, v___x_6023_);
lean_ctor_set(v___x_6024_, 1, v___x_6001_);
v___x_6025_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_6026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6024_);
lean_ctor_set(v___x_6026_, 1, v___x_6025_);
v___x_6027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6026_);
lean_ctor_set(v___x_6027_, 1, v___x_5990_);
v___x_6028_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_6029_ = l_Bool_repr___redArg(v_memoize_5961_);
v___x_6030_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6030_, 0, v___x_6028_);
lean_ctor_set(v___x_6030_, 1, v___x_6029_);
v___x_6031_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6031_, 0, v___x_6030_);
lean_ctor_set_uint8(v___x_6031_, sizeof(void*)*1, v___x_5996_);
v___x_6032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6032_, 0, v___x_6027_);
lean_ctor_set(v___x_6032_, 1, v___x_6031_);
v___x_6033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6033_, 0, v___x_6032_);
lean_ctor_set(v___x_6033_, 1, v___x_5999_);
v___x_6034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6033_);
lean_ctor_set(v___x_6034_, 1, v___x_6001_);
v___x_6035_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_6036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6034_);
lean_ctor_set(v___x_6036_, 1, v___x_6035_);
v___x_6037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6037_, 0, v___x_6036_);
lean_ctor_set(v___x_6037_, 1, v___x_5990_);
v___x_6038_ = l_Bool_repr___redArg(v_singlePass_5962_);
v___x_6039_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6039_, 0, v___x_6017_);
lean_ctor_set(v___x_6039_, 1, v___x_6038_);
v___x_6040_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6040_, 0, v___x_6039_);
lean_ctor_set_uint8(v___x_6040_, sizeof(void*)*1, v___x_5996_);
v___x_6041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6037_);
lean_ctor_set(v___x_6041_, 1, v___x_6040_);
v___x_6042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6042_, 0, v___x_6041_);
lean_ctor_set(v___x_6042_, 1, v___x_5999_);
v___x_6043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6043_, 0, v___x_6042_);
lean_ctor_set(v___x_6043_, 1, v___x_6001_);
v___x_6044_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_6045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6045_, 0, v___x_6043_);
lean_ctor_set(v___x_6045_, 1, v___x_6044_);
v___x_6046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6046_, 0, v___x_6045_);
lean_ctor_set(v___x_6046_, 1, v___x_5990_);
v___x_6047_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_6048_ = l_Bool_repr___redArg(v_zeta_5963_);
v___x_6049_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6049_, 0, v___x_6047_);
lean_ctor_set(v___x_6049_, 1, v___x_6048_);
v___x_6050_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6050_, 0, v___x_6049_);
lean_ctor_set_uint8(v___x_6050_, sizeof(void*)*1, v___x_5996_);
v___x_6051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6051_, 0, v___x_6046_);
lean_ctor_set(v___x_6051_, 1, v___x_6050_);
v___x_6052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6052_, 0, v___x_6051_);
lean_ctor_set(v___x_6052_, 1, v___x_5999_);
v___x_6053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6053_, 0, v___x_6052_);
lean_ctor_set(v___x_6053_, 1, v___x_6001_);
v___x_6054_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_6055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6055_, 0, v___x_6053_);
lean_ctor_set(v___x_6055_, 1, v___x_6054_);
v___x_6056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6056_, 0, v___x_6055_);
lean_ctor_set(v___x_6056_, 1, v___x_5990_);
v___x_6057_ = l_Bool_repr___redArg(v_beta_5964_);
v___x_6058_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6058_, 0, v___x_6047_);
lean_ctor_set(v___x_6058_, 1, v___x_6057_);
v___x_6059_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6059_, 0, v___x_6058_);
lean_ctor_set_uint8(v___x_6059_, sizeof(void*)*1, v___x_5996_);
v___x_6060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6056_);
lean_ctor_set(v___x_6060_, 1, v___x_6059_);
v___x_6061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6060_);
lean_ctor_set(v___x_6061_, 1, v___x_5999_);
v___x_6062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6062_, 0, v___x_6061_);
lean_ctor_set(v___x_6062_, 1, v___x_6001_);
v___x_6063_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_6064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6064_, 0, v___x_6062_);
lean_ctor_set(v___x_6064_, 1, v___x_6063_);
v___x_6065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6064_);
lean_ctor_set(v___x_6065_, 1, v___x_5990_);
v___x_6066_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_6067_ = l_Bool_repr___redArg(v_eta_5965_);
v___x_6068_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6068_, 0, v___x_6066_);
lean_ctor_set(v___x_6068_, 1, v___x_6067_);
v___x_6069_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6069_, 0, v___x_6068_);
lean_ctor_set_uint8(v___x_6069_, sizeof(void*)*1, v___x_5996_);
v___x_6070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6065_);
lean_ctor_set(v___x_6070_, 1, v___x_6069_);
v___x_6071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6070_);
lean_ctor_set(v___x_6071_, 1, v___x_5999_);
v___x_6072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6071_);
lean_ctor_set(v___x_6072_, 1, v___x_6001_);
v___x_6073_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_6074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6074_, 0, v___x_6072_);
lean_ctor_set(v___x_6074_, 1, v___x_6073_);
v___x_6075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6075_, 0, v___x_6074_);
lean_ctor_set(v___x_6075_, 1, v___x_5990_);
v___x_6076_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_6077_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5966_, v___x_6018_);
v___x_6078_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6076_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6079_, 0, v___x_6078_);
lean_ctor_set_uint8(v___x_6079_, sizeof(void*)*1, v___x_5996_);
v___x_6080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6080_, 0, v___x_6075_);
lean_ctor_set(v___x_6080_, 1, v___x_6079_);
v___x_6081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6081_, 0, v___x_6080_);
lean_ctor_set(v___x_6081_, 1, v___x_5999_);
v___x_6082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6081_);
lean_ctor_set(v___x_6082_, 1, v___x_6001_);
v___x_6083_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_6084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6084_, 0, v___x_6082_);
lean_ctor_set(v___x_6084_, 1, v___x_6083_);
v___x_6085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6085_, 0, v___x_6084_);
lean_ctor_set(v___x_6085_, 1, v___x_5990_);
v___x_6086_ = l_Bool_repr___redArg(v_iota_5967_);
v___x_6087_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6087_, 0, v___x_6047_);
lean_ctor_set(v___x_6087_, 1, v___x_6086_);
v___x_6088_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6088_, 0, v___x_6087_);
lean_ctor_set_uint8(v___x_6088_, sizeof(void*)*1, v___x_5996_);
v___x_6089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6085_);
lean_ctor_set(v___x_6089_, 1, v___x_6088_);
v___x_6090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6090_, 0, v___x_6089_);
lean_ctor_set(v___x_6090_, 1, v___x_5999_);
v___x_6091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6090_);
lean_ctor_set(v___x_6091_, 1, v___x_6001_);
v___x_6092_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_6093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6091_);
lean_ctor_set(v___x_6093_, 1, v___x_6092_);
v___x_6094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___x_6093_);
lean_ctor_set(v___x_6094_, 1, v___x_5990_);
v___x_6095_ = l_Bool_repr___redArg(v_proj_5968_);
v___x_6096_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6047_);
lean_ctor_set(v___x_6096_, 1, v___x_6095_);
v___x_6097_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6097_, 0, v___x_6096_);
lean_ctor_set_uint8(v___x_6097_, sizeof(void*)*1, v___x_5996_);
v___x_6098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6094_);
lean_ctor_set(v___x_6098_, 1, v___x_6097_);
v___x_6099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6099_, 0, v___x_6098_);
lean_ctor_set(v___x_6099_, 1, v___x_5999_);
v___x_6100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6099_);
lean_ctor_set(v___x_6100_, 1, v___x_6001_);
v___x_6101_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_6102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6100_);
lean_ctor_set(v___x_6102_, 1, v___x_6101_);
v___x_6103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6102_);
lean_ctor_set(v___x_6103_, 1, v___x_5990_);
v___x_6104_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_6105_ = l_Bool_repr___redArg(v_decide_5969_);
v___x_6106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6106_, 0, v___x_6104_);
lean_ctor_set(v___x_6106_, 1, v___x_6105_);
v___x_6107_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6107_, 0, v___x_6106_);
lean_ctor_set_uint8(v___x_6107_, sizeof(void*)*1, v___x_5996_);
v___x_6108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6108_, 0, v___x_6103_);
lean_ctor_set(v___x_6108_, 1, v___x_6107_);
v___x_6109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6109_, 0, v___x_6108_);
lean_ctor_set(v___x_6109_, 1, v___x_5999_);
v___x_6110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6110_, 0, v___x_6109_);
lean_ctor_set(v___x_6110_, 1, v___x_6001_);
v___x_6111_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_6112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6112_, 0, v___x_6110_);
lean_ctor_set(v___x_6112_, 1, v___x_6111_);
v___x_6113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6112_);
lean_ctor_set(v___x_6113_, 1, v___x_5990_);
v___x_6114_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_6115_ = l_Bool_repr___redArg(v_arith_5970_);
v___x_6116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6114_);
lean_ctor_set(v___x_6116_, 1, v___x_6115_);
v___x_6117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6117_, 0, v___x_6116_);
lean_ctor_set_uint8(v___x_6117_, sizeof(void*)*1, v___x_5996_);
v___x_6118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6113_);
lean_ctor_set(v___x_6118_, 1, v___x_6117_);
v___x_6119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6119_, 0, v___x_6118_);
lean_ctor_set(v___x_6119_, 1, v___x_5999_);
v___x_6120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6119_);
lean_ctor_set(v___x_6120_, 1, v___x_6001_);
v___x_6121_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_6122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6122_, 0, v___x_6120_);
lean_ctor_set(v___x_6122_, 1, v___x_6121_);
v___x_6123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6123_, 0, v___x_6122_);
lean_ctor_set(v___x_6123_, 1, v___x_5990_);
v___x_6124_ = l_Bool_repr___redArg(v_autoUnfold_5971_);
v___x_6125_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6125_, 0, v___x_6017_);
lean_ctor_set(v___x_6125_, 1, v___x_6124_);
v___x_6126_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6126_, 0, v___x_6125_);
lean_ctor_set_uint8(v___x_6126_, sizeof(void*)*1, v___x_5996_);
v___x_6127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6127_, 0, v___x_6123_);
lean_ctor_set(v___x_6127_, 1, v___x_6126_);
v___x_6128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6128_, 0, v___x_6127_);
lean_ctor_set(v___x_6128_, 1, v___x_5999_);
v___x_6129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6128_);
lean_ctor_set(v___x_6129_, 1, v___x_6001_);
v___x_6130_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_6131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6131_, 0, v___x_6129_);
lean_ctor_set(v___x_6131_, 1, v___x_6130_);
v___x_6132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6131_);
lean_ctor_set(v___x_6132_, 1, v___x_5990_);
v___x_6133_ = l_Bool_repr___redArg(v_dsimp_5972_);
v___x_6134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6134_, 0, v___x_6114_);
lean_ctor_set(v___x_6134_, 1, v___x_6133_);
v___x_6135_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6135_, 0, v___x_6134_);
lean_ctor_set_uint8(v___x_6135_, sizeof(void*)*1, v___x_5996_);
v___x_6136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6136_, 0, v___x_6132_);
lean_ctor_set(v___x_6136_, 1, v___x_6135_);
v___x_6137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6137_, 0, v___x_6136_);
lean_ctor_set(v___x_6137_, 1, v___x_5999_);
v___x_6138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6138_, 0, v___x_6137_);
lean_ctor_set(v___x_6138_, 1, v___x_6001_);
v___x_6139_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_6140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6140_, 0, v___x_6138_);
lean_ctor_set(v___x_6140_, 1, v___x_6139_);
v___x_6141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6141_, 0, v___x_6140_);
lean_ctor_set(v___x_6141_, 1, v___x_5990_);
v___x_6142_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_6143_ = l_Bool_repr___redArg(v_failIfUnchanged_5973_);
v___x_6144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6142_);
lean_ctor_set(v___x_6144_, 1, v___x_6143_);
v___x_6145_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6145_, 0, v___x_6144_);
lean_ctor_set_uint8(v___x_6145_, sizeof(void*)*1, v___x_5996_);
v___x_6146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6146_, 0, v___x_6141_);
lean_ctor_set(v___x_6146_, 1, v___x_6145_);
v___x_6147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6147_, 0, v___x_6146_);
lean_ctor_set(v___x_6147_, 1, v___x_5999_);
v___x_6148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6147_);
lean_ctor_set(v___x_6148_, 1, v___x_6001_);
v___x_6149_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_6150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6150_, 0, v___x_6148_);
lean_ctor_set(v___x_6150_, 1, v___x_6149_);
v___x_6151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6151_, 0, v___x_6150_);
lean_ctor_set(v___x_6151_, 1, v___x_5990_);
v___x_6152_ = l_Bool_repr___redArg(v_ground_5974_);
v___x_6153_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6153_, 0, v___x_6104_);
lean_ctor_set(v___x_6153_, 1, v___x_6152_);
v___x_6154_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6154_, 0, v___x_6153_);
lean_ctor_set_uint8(v___x_6154_, sizeof(void*)*1, v___x_5996_);
v___x_6155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6155_, 0, v___x_6151_);
lean_ctor_set(v___x_6155_, 1, v___x_6154_);
v___x_6156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6156_, 0, v___x_6155_);
lean_ctor_set(v___x_6156_, 1, v___x_5999_);
v___x_6157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6157_, 0, v___x_6156_);
lean_ctor_set(v___x_6157_, 1, v___x_6001_);
v___x_6158_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_6159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6157_);
lean_ctor_set(v___x_6159_, 1, v___x_6158_);
v___x_6160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6160_, 0, v___x_6159_);
lean_ctor_set(v___x_6160_, 1, v___x_5990_);
v___x_6161_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_6162_ = l_Bool_repr___redArg(v_unfoldPartialApp_5975_);
v___x_6163_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6163_, 0, v___x_6161_);
lean_ctor_set(v___x_6163_, 1, v___x_6162_);
v___x_6164_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6164_, 0, v___x_6163_);
lean_ctor_set_uint8(v___x_6164_, sizeof(void*)*1, v___x_5996_);
v___x_6165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6165_, 0, v___x_6160_);
lean_ctor_set(v___x_6165_, 1, v___x_6164_);
v___x_6166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6166_, 0, v___x_6165_);
lean_ctor_set(v___x_6166_, 1, v___x_5999_);
v___x_6167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6167_, 0, v___x_6166_);
lean_ctor_set(v___x_6167_, 1, v___x_6001_);
v___x_6168_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6169_, 0, v___x_6167_);
lean_ctor_set(v___x_6169_, 1, v___x_6168_);
v___x_6170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6170_, 0, v___x_6169_);
lean_ctor_set(v___x_6170_, 1, v___x_5990_);
v___x_6171_ = l_Bool_repr___redArg(v_zetaDelta_5976_);
v___x_6172_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6172_, 0, v___x_6076_);
lean_ctor_set(v___x_6172_, 1, v___x_6171_);
v___x_6173_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6173_, 0, v___x_6172_);
lean_ctor_set_uint8(v___x_6173_, sizeof(void*)*1, v___x_5996_);
v___x_6174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6174_, 0, v___x_6170_);
lean_ctor_set(v___x_6174_, 1, v___x_6173_);
v___x_6175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6175_, 0, v___x_6174_);
lean_ctor_set(v___x_6175_, 1, v___x_5999_);
v___x_6176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6175_);
lean_ctor_set(v___x_6176_, 1, v___x_6001_);
v___x_6177_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6178_, 0, v___x_6176_);
lean_ctor_set(v___x_6178_, 1, v___x_6177_);
v___x_6179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6178_);
lean_ctor_set(v___x_6179_, 1, v___x_5990_);
v___x_6180_ = l_Bool_repr___redArg(v_index_5977_);
v___x_6181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6181_, 0, v___x_6114_);
lean_ctor_set(v___x_6181_, 1, v___x_6180_);
v___x_6182_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6182_, 0, v___x_6181_);
lean_ctor_set_uint8(v___x_6182_, sizeof(void*)*1, v___x_5996_);
v___x_6183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6183_, 0, v___x_6179_);
lean_ctor_set(v___x_6183_, 1, v___x_6182_);
v___x_6184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6184_, 0, v___x_6183_);
lean_ctor_set(v___x_6184_, 1, v___x_5999_);
v___x_6185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6185_, 0, v___x_6184_);
lean_ctor_set(v___x_6185_, 1, v___x_6001_);
v___x_6186_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6187_, 0, v___x_6185_);
lean_ctor_set(v___x_6187_, 1, v___x_6186_);
v___x_6188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6188_, 0, v___x_6187_);
lean_ctor_set(v___x_6188_, 1, v___x_5990_);
v___x_6189_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6190_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5978_);
v___x_6191_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6191_, 0, v___x_6189_);
lean_ctor_set(v___x_6191_, 1, v___x_6190_);
v___x_6192_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6192_, 0, v___x_6191_);
lean_ctor_set_uint8(v___x_6192_, sizeof(void*)*1, v___x_5996_);
v___x_6193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6193_, 0, v___x_6188_);
lean_ctor_set(v___x_6193_, 1, v___x_6192_);
v___x_6194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6194_, 0, v___x_6193_);
lean_ctor_set(v___x_6194_, 1, v___x_5999_);
v___x_6195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6195_, 0, v___x_6194_);
lean_ctor_set(v___x_6195_, 1, v___x_6001_);
v___x_6196_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6197_, 0, v___x_6195_);
lean_ctor_set(v___x_6197_, 1, v___x_6196_);
v___x_6198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6198_, 0, v___x_6197_);
lean_ctor_set(v___x_6198_, 1, v___x_5990_);
v___x_6199_ = l_Bool_repr___redArg(v_zetaUnused_5979_);
v___x_6200_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6200_, 0, v___x_6017_);
lean_ctor_set(v___x_6200_, 1, v___x_6199_);
v___x_6201_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6201_, 0, v___x_6200_);
lean_ctor_set_uint8(v___x_6201_, sizeof(void*)*1, v___x_5996_);
v___x_6202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6202_, 0, v___x_6198_);
lean_ctor_set(v___x_6202_, 1, v___x_6201_);
v___x_6203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6203_, 0, v___x_6202_);
lean_ctor_set(v___x_6203_, 1, v___x_5999_);
v___x_6204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6204_, 0, v___x_6203_);
lean_ctor_set(v___x_6204_, 1, v___x_6001_);
v___x_6205_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6206_, 0, v___x_6204_);
lean_ctor_set(v___x_6206_, 1, v___x_6205_);
v___x_6207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6207_, 0, v___x_6206_);
lean_ctor_set(v___x_6207_, 1, v___x_5990_);
v___x_6208_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6209_ = l_Bool_repr___redArg(v_catchRuntime_5980_);
v___x_6210_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6210_, 0, v___x_6208_);
lean_ctor_set(v___x_6210_, 1, v___x_6209_);
v___x_6211_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6211_, 0, v___x_6210_);
lean_ctor_set_uint8(v___x_6211_, sizeof(void*)*1, v___x_5996_);
v___x_6212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6212_, 0, v___x_6207_);
lean_ctor_set(v___x_6212_, 1, v___x_6211_);
v___x_6213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6213_, 0, v___x_6212_);
lean_ctor_set(v___x_6213_, 1, v___x_5999_);
v___x_6214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6214_, 0, v___x_6213_);
lean_ctor_set(v___x_6214_, 1, v___x_6001_);
v___x_6215_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6216_, 0, v___x_6214_);
lean_ctor_set(v___x_6216_, 1, v___x_6215_);
v___x_6217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6217_, 0, v___x_6216_);
lean_ctor_set(v___x_6217_, 1, v___x_5990_);
v___x_6218_ = l_Bool_repr___redArg(v_zetaHave_5981_);
v___x_6219_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6219_, 0, v___x_5992_);
lean_ctor_set(v___x_6219_, 1, v___x_6218_);
v___x_6220_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6220_, 0, v___x_6219_);
lean_ctor_set_uint8(v___x_6220_, sizeof(void*)*1, v___x_5996_);
v___x_6221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6221_, 0, v___x_6217_);
lean_ctor_set(v___x_6221_, 1, v___x_6220_);
v___x_6222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6222_, 0, v___x_6221_);
lean_ctor_set(v___x_6222_, 1, v___x_5999_);
v___x_6223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6223_, 0, v___x_6222_);
lean_ctor_set(v___x_6223_, 1, v___x_6001_);
v___x_6224_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6225_, 0, v___x_6223_);
lean_ctor_set(v___x_6225_, 1, v___x_6224_);
v___x_6226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6226_, 0, v___x_6225_);
lean_ctor_set(v___x_6226_, 1, v___x_5990_);
v___x_6227_ = l_Bool_repr___redArg(v_letToHave_5982_);
v___x_6228_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6228_, 0, v___x_6076_);
lean_ctor_set(v___x_6228_, 1, v___x_6227_);
v___x_6229_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6229_, 0, v___x_6228_);
lean_ctor_set_uint8(v___x_6229_, sizeof(void*)*1, v___x_5996_);
v___x_6230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6230_, 0, v___x_6226_);
lean_ctor_set(v___x_6230_, 1, v___x_6229_);
v___x_6231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6231_, 0, v___x_6230_);
lean_ctor_set(v___x_6231_, 1, v___x_5999_);
v___x_6232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6232_, 0, v___x_6231_);
lean_ctor_set(v___x_6232_, 1, v___x_6001_);
v___x_6233_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6234_, 0, v___x_6232_);
lean_ctor_set(v___x_6234_, 1, v___x_6233_);
v___x_6235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6235_, 0, v___x_6234_);
lean_ctor_set(v___x_6235_, 1, v___x_5990_);
v___x_6236_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6237_ = l_Bool_repr___redArg(v_congrConsts_5983_);
v___x_6238_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6238_, 0, v___x_6236_);
lean_ctor_set(v___x_6238_, 1, v___x_6237_);
v___x_6239_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6239_, 0, v___x_6238_);
lean_ctor_set_uint8(v___x_6239_, sizeof(void*)*1, v___x_5996_);
v___x_6240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6240_, 0, v___x_6235_);
lean_ctor_set(v___x_6240_, 1, v___x_6239_);
v___x_6241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6241_, 0, v___x_6240_);
lean_ctor_set(v___x_6241_, 1, v___x_5999_);
v___x_6242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6242_, 0, v___x_6241_);
lean_ctor_set(v___x_6242_, 1, v___x_6001_);
v___x_6243_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6244_, 0, v___x_6242_);
lean_ctor_set(v___x_6244_, 1, v___x_6243_);
v___x_6245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6245_, 0, v___x_6244_);
lean_ctor_set(v___x_6245_, 1, v___x_5990_);
v___x_6246_ = l_Bool_repr___redArg(v_bitVecOfNat_5984_);
v___x_6247_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6247_, 0, v___x_6236_);
lean_ctor_set(v___x_6247_, 1, v___x_6246_);
v___x_6248_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6248_, 0, v___x_6247_);
lean_ctor_set_uint8(v___x_6248_, sizeof(void*)*1, v___x_5996_);
v___x_6249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6249_, 0, v___x_6245_);
lean_ctor_set(v___x_6249_, 1, v___x_6248_);
v___x_6250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6250_, 0, v___x_6249_);
lean_ctor_set(v___x_6250_, 1, v___x_5999_);
v___x_6251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6251_, 0, v___x_6250_);
lean_ctor_set(v___x_6251_, 1, v___x_6001_);
v___x_6252_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6253_, 0, v___x_6251_);
lean_ctor_set(v___x_6253_, 1, v___x_6252_);
v___x_6254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6254_, 0, v___x_6253_);
lean_ctor_set(v___x_6254_, 1, v___x_5990_);
v___x_6255_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6256_ = l_Bool_repr___redArg(v_warnExponents_5985_);
v___x_6257_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6257_, 0, v___x_6255_);
lean_ctor_set(v___x_6257_, 1, v___x_6256_);
v___x_6258_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6258_, 0, v___x_6257_);
lean_ctor_set_uint8(v___x_6258_, sizeof(void*)*1, v___x_5996_);
v___x_6259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6259_, 0, v___x_6254_);
lean_ctor_set(v___x_6259_, 1, v___x_6258_);
v___x_6260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6260_, 0, v___x_6259_);
lean_ctor_set(v___x_6260_, 1, v___x_5999_);
v___x_6261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6261_, 0, v___x_6260_);
lean_ctor_set(v___x_6261_, 1, v___x_6001_);
v___x_6262_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6263_, 0, v___x_6261_);
lean_ctor_set(v___x_6263_, 1, v___x_6262_);
v___x_6264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6264_, 0, v___x_6263_);
lean_ctor_set(v___x_6264_, 1, v___x_5990_);
v___x_6265_ = l_Bool_repr___redArg(v_suggestions_5986_);
v___x_6266_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6266_, 0, v___x_6236_);
lean_ctor_set(v___x_6266_, 1, v___x_6265_);
v___x_6267_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6267_, 0, v___x_6266_);
lean_ctor_set_uint8(v___x_6267_, sizeof(void*)*1, v___x_5996_);
v___x_6268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6268_, 0, v___x_6264_);
lean_ctor_set(v___x_6268_, 1, v___x_6267_);
v___x_6269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6269_, 0, v___x_6268_);
lean_ctor_set(v___x_6269_, 1, v___x_5999_);
v___x_6270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6270_, 0, v___x_6269_);
lean_ctor_set(v___x_6270_, 1, v___x_6001_);
v___x_6271_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6272_, 0, v___x_6270_);
lean_ctor_set(v___x_6272_, 1, v___x_6271_);
v___x_6273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6273_, 0, v___x_6272_);
lean_ctor_set(v___x_6273_, 1, v___x_5990_);
v___x_6274_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6275_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5987_, v___x_6018_);
v___x_6276_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6276_, 0, v___x_6274_);
lean_ctor_set(v___x_6276_, 1, v___x_6275_);
v___x_6277_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6277_, 0, v___x_6276_);
lean_ctor_set_uint8(v___x_6277_, sizeof(void*)*1, v___x_5996_);
v___x_6278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6278_, 0, v___x_6273_);
lean_ctor_set(v___x_6278_, 1, v___x_6277_);
v___x_6279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6279_, 0, v___x_6278_);
lean_ctor_set(v___x_6279_, 1, v___x_5999_);
v___x_6280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6280_, 0, v___x_6279_);
lean_ctor_set(v___x_6280_, 1, v___x_6001_);
v___x_6281_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6282_, 0, v___x_6280_);
lean_ctor_set(v___x_6282_, 1, v___x_6281_);
v___x_6283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6283_, 0, v___x_6282_);
lean_ctor_set(v___x_6283_, 1, v___x_5990_);
v___x_6284_ = l_Bool_repr___redArg(v_locals_5988_);
v___x_6285_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6285_, 0, v___x_6104_);
lean_ctor_set(v___x_6285_, 1, v___x_6284_);
v___x_6286_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6286_, 0, v___x_6285_);
lean_ctor_set_uint8(v___x_6286_, sizeof(void*)*1, v___x_5996_);
v___x_6287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6287_, 0, v___x_6283_);
lean_ctor_set(v___x_6287_, 1, v___x_6286_);
v___x_6288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6288_, 0, v___x_6287_);
lean_ctor_set(v___x_6288_, 1, v___x_5999_);
v___x_6289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6289_, 0, v___x_6288_);
lean_ctor_set(v___x_6289_, 1, v___x_6001_);
v___x_6290_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6291_, 0, v___x_6289_);
lean_ctor_set(v___x_6291_, 1, v___x_6290_);
v___x_6292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6292_, 0, v___x_6291_);
lean_ctor_set(v___x_6292_, 1, v___x_5990_);
v___x_6293_ = l_Bool_repr___redArg(v_instances_5989_);
v___x_6294_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6294_, 0, v___x_6076_);
lean_ctor_set(v___x_6294_, 1, v___x_6293_);
v___x_6295_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6295_, 0, v___x_6294_);
lean_ctor_set_uint8(v___x_6295_, sizeof(void*)*1, v___x_5996_);
v___x_6296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6296_, 0, v___x_6292_);
lean_ctor_set(v___x_6296_, 1, v___x_6295_);
v___x_6297_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6298_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6299_, 0, v___x_6298_);
lean_ctor_set(v___x_6299_, 1, v___x_6296_);
v___x_6300_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6301_, 0, v___x_6299_);
lean_ctor_set(v___x_6301_, 1, v___x_6300_);
v___x_6302_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6302_, 0, v___x_6297_);
lean_ctor_set(v___x_6302_, 1, v___x_6301_);
v___x_6303_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6303_, 0, v___x_6302_);
lean_ctor_set_uint8(v___x_6303_, sizeof(void*)*1, v___x_5996_);
return v___x_6303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6304_, lean_object* v_prec_6305_){
_start:
{
lean_object* v___x_6306_; 
v___x_6306_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6304_);
return v___x_6306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6307_, lean_object* v_prec_6308_){
_start:
{
lean_object* v_res_6309_; 
v_res_6309_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6307_, v_prec_6308_);
lean_dec(v_prec_6308_);
return v_res_6309_;
}
}
uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6312_, lean_object* v_x_6313_){
_start:
{
if (lean_obj_tag(v_x_6313_) == 0)
{
uint8_t v___x_6314_; 
v___x_6314_ = 0;
return v___x_6314_;
}
else
{
lean_object* v_head_6315_; lean_object* v_tail_6316_; uint8_t v___x_6317_; 
v_head_6315_ = lean_ctor_get(v_x_6313_, 0);
v_tail_6316_ = lean_ctor_get(v_x_6313_, 1);
v___x_6317_ = lean_nat_dec_eq(v_a_6312_, v_head_6315_);
if (v___x_6317_ == 0)
{
v_x_6313_ = v_tail_6316_;
goto _start;
}
else
{
return v___x_6317_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_6312_ = stack[0].m_obj;
lean_object* v_x_6313_ = stack[1].m_obj;
uint8_t v_res_6319_;
v_res_6319_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6312_, v_x_6313_);
stack->m_num = v_res_6319_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6320_, lean_object* v_x_6321_){
_start:
{
uint8_t v_res_6322_; lean_object* v_r_6323_; 
v_res_6322_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6320_, v_x_6321_);
lean_dec(v_x_6321_);
lean_dec(v_a_6320_);
v_r_6323_ = lean_box(v_res_6322_);
return v_r_6323_;
}
}
uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6324_, lean_object* v_x_6325_){
_start:
{
switch(lean_obj_tag(v_x_6324_))
{
case 0:
{
uint8_t v___x_6326_; 
v___x_6326_ = 1;
return v___x_6326_;
}
case 1:
{
lean_object* v_idxs_6327_; uint8_t v___x_6328_; 
v_idxs_6327_ = lean_ctor_get(v_x_6324_, 0);
v___x_6328_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6325_, v_idxs_6327_);
return v___x_6328_;
}
default: 
{
lean_object* v_idxs_6329_; uint8_t v___x_6330_; 
v_idxs_6329_ = lean_ctor_get(v_x_6324_, 0);
v___x_6330_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6325_, v_idxs_6329_);
if (v___x_6330_ == 0)
{
uint8_t v___x_6331_; 
v___x_6331_ = 1;
return v___x_6331_;
}
else
{
uint8_t v___x_6332_; 
v___x_6332_ = 0;
return v___x_6332_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Occurrences_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_6324_ = stack[0].m_obj;
lean_object* v_x_6325_ = stack[1].m_obj;
uint8_t v_res_6333_;
v_res_6333_ = l_Lean_Meta_Occurrences_contains(v_x_6324_, v_x_6325_);
stack->m_num = v_res_6333_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6334_, lean_object* v_x_6335_){
_start:
{
uint8_t v_res_6336_; lean_object* v_r_6337_; 
v_res_6336_ = l_Lean_Meta_Occurrences_contains(v_x_6334_, v_x_6335_);
lean_dec(v_x_6335_);
lean_dec(v_x_6334_);
v_r_6337_ = lean_box(v_res_6336_);
return v_r_6337_;
}
}
uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6338_){
_start:
{
if (lean_obj_tag(v_x_6338_) == 0)
{
uint8_t v___x_6339_; 
v___x_6339_ = 1;
return v___x_6339_;
}
else
{
uint8_t v___x_6340_; 
v___x_6340_ = 0;
return v___x_6340_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Occurrences_isAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_6338_ = stack[0].m_obj;
uint8_t v_res_6341_;
v_res_6341_ = l_Lean_Meta_Occurrences_isAll(v_x_6338_);
stack->m_num = v_res_6341_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6342_){
_start:
{
uint8_t v_res_6343_; lean_object* v_r_6344_; 
v_res_6343_ = l_Lean_Meta_Occurrences_isAll(v_x_6342_);
lean_dec(v_x_6342_);
v_r_6344_ = lean_box(v_res_6343_);
return v_r_6344_;
}
}
lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___impl(uint8_t v_x_6345_){
_start:
{
lean_object* v___x_6346_; lean_object* v___x_6347_; 
v___x_6346_ = lean_box(v_x_6345_);
v___x_6347_ = lean_obj_tag_nat(v___x_6346_);
lean_dec(v___x_6346_);
return v___x_6347_;
}
}
LEAN_EXPORT void l_Lean_Meta_ApplyNewGoals_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_6345_ = stack[0].m_num;
lean_object* v_res_6348_;
v_res_6348_ = l_Lean_Meta_ApplyNewGoals_ctorIdx___impl(v_x_6345_);
stack->m_obj
 = v_res_6348_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___impl___boxed(lean_object* v_x_6349_){
_start:
{
uint8_t v_x_4__boxed_6350_; lean_object* v_res_6351_; 
v_x_4__boxed_6350_ = lean_unbox(v_x_6349_);
v_res_6351_ = l_Lean_Meta_ApplyNewGoals_ctorIdx___impl(v_x_4__boxed_6350_);
return v_res_6351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6352_){
_start:
{
lean_inc(v_k_6352_);
return v_k_6352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6353_){
_start:
{
lean_object* v_res_6354_; 
v_res_6354_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6353_);
lean_dec(v_k_6353_);
return v_res_6354_;
}
}
lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6355_, lean_object* v_ctorIdx_6356_, uint8_t v_t_6357_, lean_object* v_h_6358_, lean_object* v_k_6359_){
_start:
{
lean_inc(v_k_6359_);
return v_k_6359_;
}
}
LEAN_EXPORT void l_Lean_Meta_ApplyNewGoals_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_6356_ = stack[1].m_obj;
uint8_t v_t_6357_ = stack[2].m_num;
lean_object* v_k_6359_ = stack[4].m_obj;
lean_object* v_res_6360_;
v_res_6360_ = l_Lean_Meta_ApplyNewGoals_ctorElim(lean_box(0), v_ctorIdx_6356_, v_t_6357_, lean_box(0), v_k_6359_);
stack->m_obj
 = v_res_6360_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6361_, lean_object* v_ctorIdx_6362_, lean_object* v_t_6363_, lean_object* v_h_6364_, lean_object* v_k_6365_){
_start:
{
uint8_t v_t_boxed_6366_; lean_object* v_res_6367_; 
v_t_boxed_6366_ = lean_unbox(v_t_6363_);
v_res_6367_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6361_, v_ctorIdx_6362_, v_t_boxed_6366_, v_h_6364_, v_k_6365_);
lean_dec(v_k_6365_);
lean_dec(v_ctorIdx_6362_);
return v_res_6367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6368_){
_start:
{
lean_inc(v_nonDependentFirst_6368_);
return v_nonDependentFirst_6368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6369_){
_start:
{
lean_object* v_res_6370_; 
v_res_6370_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6369_);
lean_dec(v_nonDependentFirst_6369_);
return v_res_6370_;
}
}
lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6371_, uint8_t v_t_6372_, lean_object* v_h_6373_, lean_object* v_nonDependentFirst_6374_){
_start:
{
lean_inc(v_nonDependentFirst_6374_);
return v_nonDependentFirst_6374_;
}
}
LEAN_EXPORT void l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_6372_ = stack[1].m_num;
lean_object* v_nonDependentFirst_6374_ = stack[3].m_obj;
lean_object* v_res_6375_;
v_res_6375_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_box(0), v_t_6372_, lean_box(0), v_nonDependentFirst_6374_);
stack->m_obj
 = v_res_6375_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6376_, lean_object* v_t_6377_, lean_object* v_h_6378_, lean_object* v_nonDependentFirst_6379_){
_start:
{
uint8_t v_t_boxed_6380_; lean_object* v_res_6381_; 
v_t_boxed_6380_ = lean_unbox(v_t_6377_);
v_res_6381_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6376_, v_t_boxed_6380_, v_h_6378_, v_nonDependentFirst_6379_);
lean_dec(v_nonDependentFirst_6379_);
return v_res_6381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6382_){
_start:
{
lean_inc(v_nonDependentOnly_6382_);
return v_nonDependentOnly_6382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6383_){
_start:
{
lean_object* v_res_6384_; 
v_res_6384_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6383_);
lean_dec(v_nonDependentOnly_6383_);
return v_res_6384_;
}
}
lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6385_, uint8_t v_t_6386_, lean_object* v_h_6387_, lean_object* v_nonDependentOnly_6388_){
_start:
{
lean_inc(v_nonDependentOnly_6388_);
return v_nonDependentOnly_6388_;
}
}
LEAN_EXPORT void l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_6386_ = stack[1].m_num;
lean_object* v_nonDependentOnly_6388_ = stack[3].m_obj;
lean_object* v_res_6389_;
v_res_6389_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_box(0), v_t_6386_, lean_box(0), v_nonDependentOnly_6388_);
stack->m_obj
 = v_res_6389_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6390_, lean_object* v_t_6391_, lean_object* v_h_6392_, lean_object* v_nonDependentOnly_6393_){
_start:
{
uint8_t v_t_boxed_6394_; lean_object* v_res_6395_; 
v_t_boxed_6394_ = lean_unbox(v_t_6391_);
v_res_6395_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6390_, v_t_boxed_6394_, v_h_6392_, v_nonDependentOnly_6393_);
lean_dec(v_nonDependentOnly_6393_);
return v_res_6395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6396_){
_start:
{
lean_inc(v_all_6396_);
return v_all_6396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6397_){
_start:
{
lean_object* v_res_6398_; 
v_res_6398_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6397_);
lean_dec(v_all_6397_);
return v_res_6398_;
}
}
lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6399_, uint8_t v_t_6400_, lean_object* v_h_6401_, lean_object* v_all_6402_){
_start:
{
lean_inc(v_all_6402_);
return v_all_6402_;
}
}
LEAN_EXPORT void l_Lean_Meta_ApplyNewGoals_all_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_6400_ = stack[1].m_num;
lean_object* v_all_6402_ = stack[3].m_obj;
lean_object* v_res_6403_;
v_res_6403_ = l_Lean_Meta_ApplyNewGoals_all_elim(lean_box(0), v_t_6400_, lean_box(0), v_all_6402_);
stack->m_obj
 = v_res_6403_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6404_, lean_object* v_t_6405_, lean_object* v_h_6406_, lean_object* v_all_6407_){
_start:
{
uint8_t v_t_boxed_6408_; lean_object* v_res_6409_; 
v_t_boxed_6408_ = lean_unbox(v_t_6405_);
v_res_6409_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6404_, v_t_boxed_6408_, v_h_6406_, v_all_6407_);
lean_dec(v_all_6407_);
return v_res_6409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6423_){
_start:
{
lean_object* v___x_6424_; uint8_t v___x_6425_; 
v___x_6424_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6423_);
v___x_6425_ = l_Lean_Syntax_isOfKind(v_c_6423_, v___x_6424_);
if (v___x_6425_ == 0)
{
lean_object* v___x_6426_; uint8_t v___x_6427_; 
v___x_6426_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6423_);
v___x_6427_ = l_Lean_Syntax_isOfKind(v_c_6423_, v___x_6426_);
if (v___x_6427_ == 0)
{
lean_object* v___x_6428_; uint8_t v___x_6429_; 
v___x_6428_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6423_);
v___x_6429_ = l_Lean_Syntax_isOfKind(v_c_6423_, v___x_6428_);
if (v___x_6429_ == 0)
{
lean_object* v___x_6430_; 
lean_dec(v_c_6423_);
v___x_6430_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6430_;
}
else
{
lean_object* v___x_6431_; lean_object* v___x_6432_; lean_object* v___x_6433_; 
v___x_6431_ = lean_unsigned_to_nat(1u);
v___x_6432_ = lean_mk_empty_array_with_capacity(v___x_6431_);
v___x_6433_ = lean_array_push(v___x_6432_, v_c_6423_);
return v___x_6433_;
}
}
else
{
lean_object* v___x_6434_; lean_object* v___x_6435_; lean_object* v___x_6436_; 
v___x_6434_ = lean_unsigned_to_nat(0u);
v___x_6435_ = l_Lean_Syntax_getArg(v_c_6423_, v___x_6434_);
lean_dec(v_c_6423_);
v___x_6436_ = l_Lean_Syntax_getArgs(v___x_6435_);
lean_dec(v___x_6435_);
return v___x_6436_;
}
}
else
{
lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___x_6439_; lean_object* v___x_6440_; uint8_t v___x_6441_; 
v___x_6437_ = l_Lean_Syntax_getArgs(v_c_6423_);
lean_dec(v_c_6423_);
v___x_6438_ = lean_unsigned_to_nat(0u);
v___x_6439_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6440_ = lean_array_get_size(v___x_6437_);
v___x_6441_ = lean_nat_dec_lt(v___x_6438_, v___x_6440_);
if (v___x_6441_ == 0)
{
lean_dec_ref(v___x_6437_);
return v___x_6439_;
}
else
{
size_t v___x_6442_; size_t v___x_6443_; lean_object* v___x_6444_; 
v___x_6442_ = ((size_t)0ULL);
v___x_6443_ = lean_usize_of_nat(v___x_6440_);
v___x_6444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6437_, v___x_6442_, v___x_6443_, v___x_6439_);
lean_dec_ref(v___x_6437_);
return v___x_6444_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6445_, size_t v_i_6446_, size_t v_stop_6447_, lean_object* v_b_6448_){
_start:
{
uint8_t v___x_6449_; 
v___x_6449_ = lean_usize_dec_eq(v_i_6446_, v_stop_6447_);
if (v___x_6449_ == 0)
{
lean_object* v___x_6450_; lean_object* v___x_6451_; lean_object* v___x_6452_; size_t v___x_6453_; size_t v___x_6454_; 
v___x_6450_ = lean_array_uget_borrowed(v_as_6445_, v_i_6446_);
lean_inc(v___x_6450_);
v___x_6451_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6450_);
v___x_6452_ = l_Array_append___redArg(v_b_6448_, v___x_6451_);
lean_dec_ref(v___x_6451_);
v___x_6453_ = ((size_t)1ULL);
v___x_6454_ = lean_usize_add(v_i_6446_, v___x_6453_);
v_i_6446_ = v___x_6454_;
v_b_6448_ = v___x_6452_;
goto _start;
}
else
{
return v_b_6448_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_6445_ = stack[0].m_obj;
size_t v_i_6446_ = stack[1].m_num;
size_t v_stop_6447_ = stack[2].m_num;
lean_object* v_b_6448_ = stack[3].m_obj;
lean_object* v_res_6456_;
v_res_6456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6445_, v_i_6446_, v_stop_6447_, v_b_6448_);
stack->m_obj
 = v_res_6456_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6457_, lean_object* v_i_6458_, lean_object* v_stop_6459_, lean_object* v_b_6460_){
_start:
{
size_t v_i_boxed_6461_; size_t v_stop_boxed_6462_; lean_object* v_res_6463_; 
v_i_boxed_6461_ = lean_unbox_usize(v_i_6458_);
lean_dec(v_i_6458_);
v_stop_boxed_6462_ = lean_unbox_usize(v_stop_6459_);
lean_dec(v_stop_6459_);
v_res_6463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6457_, v_i_boxed_6461_, v_stop_boxed_6462_, v_b_6460_);
lean_dec_ref(v_as_6457_);
return v_res_6463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6464_){
_start:
{
lean_object* v___x_6465_; lean_object* v___x_6466_; lean_object* v___x_6467_; lean_object* v___x_6468_; lean_object* v___x_6469_; 
v___x_6465_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6466_ = lean_box(2);
v___x_6467_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6468_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6468_, 0, v___x_6466_);
lean_ctor_set(v___x_6468_, 1, v___x_6467_);
lean_ctor_set(v___x_6468_, 2, v_items_6464_);
v___x_6469_ = l_Lean_Syntax_node1(v___x_6466_, v___x_6465_, v___x_6468_);
return v___x_6469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6470_, lean_object* v_cfg_x27_6471_){
_start:
{
lean_object* v___x_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; lean_object* v___x_6475_; 
v___x_6472_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6470_);
v___x_6473_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6471_);
v___x_6474_ = l_Array_append___redArg(v___x_6472_, v___x_6473_);
lean_dec_ref(v___x_6473_);
v___x_6475_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6474_);
return v___x_6475_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_version_major = _init_l_Lean_version_major();
lean_mark_persistent(l_Lean_version_major);
l_Lean_version_minor = _init_l_Lean_version_minor();
lean_mark_persistent(l_Lean_version_minor);
l_Lean_version_patch = _init_l_Lean_version_patch();
lean_mark_persistent(l_Lean_version_patch);
l_Lean_githash = _init_l_Lean_githash();
lean_mark_persistent(l_Lean_githash);
l_Lean_version_isRelease = _init_l_Lean_version_isRelease();
l_Lean_version_specialDesc = _init_l_Lean_version_specialDesc();
lean_mark_persistent(l_Lean_version_specialDesc);
l_Lean_versionStringCore = _init_l_Lean_versionStringCore();
lean_mark_persistent(l_Lean_versionStringCore);
l_Lean_versionString = _init_l_Lean_versionString();
lean_mark_persistent(l_Lean_versionString);
l_Lean_toolchain = _init_l_Lean_toolchain();
lean_mark_persistent(l_Lean_toolchain);
l_Lean_idBeginEscape = _init_l_Lean_idBeginEscape();
l_Lean_idEndEscape = _init_l_Lean_idEndEscape();
l_Lean_Syntax_decodeQuotedChar___boxed__const__1 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__1);
l_Lean_Syntax_decodeQuotedChar___boxed__const__2 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__2);
l_Lean_Syntax_decodeQuotedChar___boxed__const__3 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__3);
l_Lean_Syntax_decodeQuotedChar___boxed__const__4 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__4);
l_Lean_Syntax_decodeQuotedChar___boxed__const__5 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__5);
l_Lean_Syntax_decodeQuotedChar___boxed__const__6 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__6);
l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1 = _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1);
l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2 = _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2);
l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1 = _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Meta_Defs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Meta_Defs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Meta_Defs(builtin);
}
#ifdef __cplusplus
}
#endif
