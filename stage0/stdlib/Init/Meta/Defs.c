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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Macro_expandMacro_x3f(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Name_hasNum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_hasNum___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_evalPrec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_evalPrec___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_evalPrec___closed__0 = (const lean_object*)&l_Lean_evalPrec___closed__0_value;
static const lean_string_object l_Lean_evalPrec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected precedence"};
static const lean_object* l_Lean_evalPrec___closed__1 = (const lean_object*)&l_Lean_evalPrec___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMajor___boxed(lean_object* v_u_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lean_version_get_major(v_u_2_);
return v_res_3_;
}
}
static lean_object* _init_l_Lean_version_major___closed__0(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_box(0);
v___x_5_ = lean_version_get_major(v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_version_major(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_obj_once(&l_Lean_version_major___closed__0, &l_Lean_version_major___closed__0_once, _init_l_Lean_version_major___closed__0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMinor___boxed(lean_object* v_u_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lean_version_get_minor(v_u_8_);
return v_res_9_;
}
}
static lean_object* _init_l_Lean_version_minor___closed__0(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_box(0);
v___x_11_ = lean_version_get_minor(v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_version_minor(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_version_minor___closed__0, &l_Lean_version_minor___closed__0_once, _init_l_Lean_version_minor___closed__0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getPatch___boxed(lean_object* v_u_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lean_version_get_patch(v_u_14_);
return v_res_15_;
}
}
static lean_object* _init_l_Lean_version_patch___closed__0(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_box(0);
v___x_17_ = lean_version_get_patch(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_version_patch(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_obj_once(&l_Lean_version_patch___closed__0, &l_Lean_version_patch___closed__0_once, _init_l_Lean_version_patch___closed__0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_getGithash___boxed(lean_object* v_u_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lean_get_githash(v_u_20_);
return v_res_21_;
}
}
static lean_object* _init_l_Lean_githash___closed__0(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_box(0);
v___x_23_ = lean_get_githash(v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_githash(void){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_obj_once(&l_Lean_githash___closed__0, &l_Lean_githash___closed__0_once, _init_l_Lean_githash___closed__0);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_version_getIsRelease___boxed(lean_object* v_u_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = lean_version_get_is_release(v_u_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
static uint8_t _init_l_Lean_version_isRelease___closed__0(void){
_start:
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = lean_box(0);
v___x_30_ = lean_version_get_is_release(v___x_29_);
return v___x_30_;
}
}
static uint8_t _init_l_Lean_version_isRelease(void){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_uint8_once(&l_Lean_version_isRelease___closed__0, &l_Lean_version_isRelease___closed__0_once, _init_l_Lean_version_isRelease___closed__0);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_version_getSpecialDesc___boxed(lean_object* v_u_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lean_version_get_special_desc(v_u_33_);
return v_res_34_;
}
}
static lean_object* _init_l_Lean_version_specialDesc___closed__0(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_box(0);
v___x_36_ = lean_version_get_special_desc(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_version_specialDesc(void){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_obj_once(&l_Lean_version_specialDesc___closed__0, &l_Lean_version_specialDesc___closed__0_once, _init_l_Lean_version_specialDesc___closed__0);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__0(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = l_Lean_version_major;
v___x_39_ = l_Nat_reprFast(v___x_38_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__2(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_42_ = lean_obj_once(&l_Lean_versionStringCore___closed__0, &l_Lean_versionStringCore___closed__0_once, _init_l_Lean_versionStringCore___closed__0);
v___x_43_ = lean_string_append(v___x_42_, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__3(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = l_Lean_version_minor;
v___x_45_ = l_Nat_reprFast(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__4(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&l_Lean_versionStringCore___closed__3, &l_Lean_versionStringCore___closed__3_once, _init_l_Lean_versionStringCore___closed__3);
v___x_47_ = lean_obj_once(&l_Lean_versionStringCore___closed__2, &l_Lean_versionStringCore___closed__2_once, _init_l_Lean_versionStringCore___closed__2);
v___x_48_ = lean_string_append(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__5(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_50_ = lean_obj_once(&l_Lean_versionStringCore___closed__4, &l_Lean_versionStringCore___closed__4_once, _init_l_Lean_versionStringCore___closed__4);
v___x_51_ = lean_string_append(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__6(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = l_Lean_version_patch;
v___x_53_ = l_Nat_reprFast(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__7(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Lean_versionStringCore___closed__6, &l_Lean_versionStringCore___closed__6_once, _init_l_Lean_versionStringCore___closed__6);
v___x_55_ = lean_obj_once(&l_Lean_versionStringCore___closed__5, &l_Lean_versionStringCore___closed__5_once, _init_l_Lean_versionStringCore___closed__5);
v___x_56_ = lean_string_append(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_versionStringCore(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_obj_once(&l_Lean_versionStringCore___closed__7, &l_Lean_versionStringCore___closed__7_once, _init_l_Lean_versionStringCore___closed__7);
return v___x_57_;
}
}
static uint8_t _init_l_Lean_versionString___closed__1(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_59_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_60_ = l_Lean_version_specialDesc;
v___x_61_ = lean_string_dec_eq(v___x_60_, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_versionString___closed__3(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = ((lean_object*)(l_Lean_versionString___closed__2));
v___x_64_ = l_Lean_versionStringCore;
v___x_65_ = lean_string_append(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_versionString___closed__4(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = l_Lean_version_specialDesc;
v___x_67_ = lean_obj_once(&l_Lean_versionString___closed__3, &l_Lean_versionString___closed__3_once, _init_l_Lean_versionString___closed__3);
v___x_68_ = lean_string_append(v___x_67_, v___x_66_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_versionString___closed__6(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = ((lean_object*)(l_Lean_versionString___closed__5));
v___x_71_ = l_Lean_versionStringCore;
v___x_72_ = lean_string_append(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_versionString___closed__7(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = l_Lean_githash;
v___x_74_ = lean_obj_once(&l_Lean_versionString___closed__6, &l_Lean_versionString___closed__6_once, _init_l_Lean_versionString___closed__6);
v___x_75_ = lean_string_append(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_versionString(void){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = lean_uint8_once(&l_Lean_versionString___closed__1, &l_Lean_versionString___closed__1_once, _init_l_Lean_versionString___closed__1);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_versionString___closed__4, &l_Lean_versionString___closed__4_once, _init_l_Lean_versionString___closed__4);
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = l_Lean_version_isRelease;
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Lean_versionString___closed__7, &l_Lean_versionString___closed__7_once, _init_l_Lean_versionString___closed__7);
return v___x_79_;
}
else
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_versionStringCore;
return v___x_80_;
}
}
}
}
static lean_object* _init_l_Lean_toolchain___closed__1(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_85_ = ((lean_object*)(l_Lean_origin___closed__0));
v___x_86_ = lean_string_append(v___x_85_, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__2(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = l_Lean_version_specialDesc;
v___x_88_ = lean_obj_once(&l_Lean_toolchain___closed__1, &l_Lean_toolchain___closed__1_once, _init_l_Lean_toolchain___closed__1);
v___x_89_ = lean_string_append(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__4(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = ((lean_object*)(l_Lean_toolchain___closed__3));
v___x_92_ = ((lean_object*)(l_Lean_origin___closed__0));
v___x_93_ = lean_string_append(v___x_92_, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__5(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = l_Lean_versionStringCore;
v___x_95_ = lean_obj_once(&l_Lean_toolchain___closed__4, &l_Lean_toolchain___closed__4_once, _init_l_Lean_toolchain___closed__4);
v___x_96_ = lean_string_append(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__6(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = ((lean_object*)(l_Lean_versionString___closed__2));
v___x_98_ = lean_obj_once(&l_Lean_toolchain___closed__5, &l_Lean_toolchain___closed__5_once, _init_l_Lean_toolchain___closed__5);
v___x_99_ = lean_string_append(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__7(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = l_Lean_version_specialDesc;
v___x_101_ = lean_obj_once(&l_Lean_toolchain___closed__6, &l_Lean_toolchain___closed__6_once, _init_l_Lean_toolchain___closed__6);
v___x_102_ = lean_string_append(v___x_101_, v___x_100_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_toolchain(void){
_start:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_104_ = lean_uint8_once(&l_Lean_versionString___closed__1, &l_Lean_versionString___closed__1_once, _init_l_Lean_versionString___closed__1);
if (v___x_104_ == 0)
{
uint8_t v___x_105_; 
v___x_105_ = l_Lean_version_isRelease;
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_toolchain___closed__2, &l_Lean_toolchain___closed__2_once, _init_l_Lean_toolchain___closed__2);
return v___x_106_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_toolchain___closed__7, &l_Lean_toolchain___closed__7_once, _init_l_Lean_toolchain___closed__7);
return v___x_107_;
}
}
else
{
uint8_t v___x_108_; 
v___x_108_ = l_Lean_version_isRelease;
if (v___x_108_ == 0)
{
return v___x_103_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_toolchain___closed__5, &l_Lean_toolchain___closed__5_once, _init_l_Lean_toolchain___closed__5);
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_isStage0___boxed(lean_object* v_u_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = lean_internal_is_stage0(v_u_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_hasLLVMBackend___boxed(lean_object* v_u_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = lean_internal_has_llvm_backend(v_u_115_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT uint8_t l_Lean_isGreek(uint32_t v_c_118_){
_start:
{
uint32_t v___x_119_; uint8_t v___x_120_; 
v___x_119_ = 913;
v___x_120_ = lean_uint32_dec_le(v___x_119_, v_c_118_);
if (v___x_120_ == 0)
{
return v___x_120_;
}
else
{
uint32_t v___x_121_; uint8_t v___x_122_; 
v___x_121_ = 989;
v___x_122_ = lean_uint32_dec_le(v_c_118_, v___x_121_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isGreek___boxed(lean_object* v_c_123_){
_start:
{
uint32_t v_c_boxed_124_; uint8_t v_res_125_; lean_object* v_r_126_; 
v_c_boxed_124_ = lean_unbox_uint32(v_c_123_);
lean_dec(v_c_123_);
v_res_125_ = l_Lean_isGreek(v_c_boxed_124_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint8_t l_Lean_isLetterLike(uint32_t v_c_127_){
_start:
{
uint32_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = 945;
v___x_172_ = lean_uint32_dec_le(v___x_171_, v_c_127_);
if (v___x_172_ == 0)
{
goto v___jp_162_;
}
else
{
uint32_t v___x_173_; uint8_t v___x_174_; 
v___x_173_ = 969;
v___x_174_ = lean_uint32_dec_le(v_c_127_, v___x_173_);
if (v___x_174_ == 0)
{
goto v___jp_162_;
}
else
{
uint32_t v___x_175_; uint8_t v___x_176_; 
v___x_175_ = 955;
v___x_176_ = lean_uint32_dec_eq(v_c_127_, v___x_175_);
if (v___x_176_ == 0)
{
return v___x_174_;
}
else
{
goto v___jp_162_;
}
}
}
v___jp_128_:
{
uint32_t v___x_129_; uint8_t v___x_130_; 
v___x_129_ = 256;
v___x_130_ = lean_uint32_dec_le(v___x_129_, v_c_127_);
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
uint32_t v___x_131_; uint8_t v___x_132_; 
v___x_131_ = 383;
v___x_132_ = lean_uint32_dec_le(v_c_127_, v___x_131_);
return v___x_132_;
}
}
v___jp_133_:
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 192;
v___x_135_ = lean_uint32_dec_le(v___x_134_, v_c_127_);
if (v___x_135_ == 0)
{
goto v___jp_128_;
}
else
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 255;
v___x_137_ = lean_uint32_dec_le(v_c_127_, v___x_136_);
if (v___x_137_ == 0)
{
goto v___jp_128_;
}
else
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 215;
v___x_139_ = lean_uint32_dec_eq(v_c_127_, v___x_138_);
if (v___x_139_ == 0)
{
uint32_t v___x_140_; uint8_t v___x_141_; 
v___x_140_ = 247;
v___x_141_ = lean_uint32_dec_eq(v_c_127_, v___x_140_);
if (v___x_141_ == 0)
{
return v___x_137_;
}
else
{
goto v___jp_128_;
}
}
else
{
goto v___jp_128_;
}
}
}
}
v___jp_142_:
{
uint32_t v___x_143_; uint8_t v___x_144_; 
v___x_143_ = 119964;
v___x_144_ = lean_uint32_dec_le(v___x_143_, v_c_127_);
if (v___x_144_ == 0)
{
goto v___jp_133_;
}
else
{
uint32_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = 120223;
v___x_146_ = lean_uint32_dec_le(v_c_127_, v___x_145_);
if (v___x_146_ == 0)
{
goto v___jp_133_;
}
else
{
return v___x_146_;
}
}
}
v___jp_147_:
{
uint32_t v___x_148_; uint8_t v___x_149_; 
v___x_148_ = 8448;
v___x_149_ = lean_uint32_dec_le(v___x_148_, v_c_127_);
if (v___x_149_ == 0)
{
goto v___jp_142_;
}
else
{
uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_150_ = 8527;
v___x_151_ = lean_uint32_dec_le(v_c_127_, v___x_150_);
if (v___x_151_ == 0)
{
goto v___jp_142_;
}
else
{
return v___x_151_;
}
}
}
v___jp_152_:
{
uint32_t v___x_153_; uint8_t v___x_154_; 
v___x_153_ = 7936;
v___x_154_ = lean_uint32_dec_le(v___x_153_, v_c_127_);
if (v___x_154_ == 0)
{
goto v___jp_147_;
}
else
{
uint32_t v___x_155_; uint8_t v___x_156_; 
v___x_155_ = 8190;
v___x_156_ = lean_uint32_dec_le(v_c_127_, v___x_155_);
if (v___x_156_ == 0)
{
goto v___jp_147_;
}
else
{
return v___x_156_;
}
}
}
v___jp_157_:
{
uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_158_ = 970;
v___x_159_ = lean_uint32_dec_le(v___x_158_, v_c_127_);
if (v___x_159_ == 0)
{
goto v___jp_152_;
}
else
{
uint32_t v___x_160_; uint8_t v___x_161_; 
v___x_160_ = 1019;
v___x_161_ = lean_uint32_dec_le(v_c_127_, v___x_160_);
if (v___x_161_ == 0)
{
goto v___jp_152_;
}
else
{
return v___x_161_;
}
}
}
v___jp_162_:
{
uint32_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 913;
v___x_164_ = lean_uint32_dec_le(v___x_163_, v_c_127_);
if (v___x_164_ == 0)
{
goto v___jp_157_;
}
else
{
uint32_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 937;
v___x_166_ = lean_uint32_dec_le(v_c_127_, v___x_165_);
if (v___x_166_ == 0)
{
goto v___jp_157_;
}
else
{
uint32_t v___x_167_; uint8_t v___x_168_; 
v___x_167_ = 928;
v___x_168_ = lean_uint32_dec_eq(v_c_127_, v___x_167_);
if (v___x_168_ == 0)
{
uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_169_ = 931;
v___x_170_ = lean_uint32_dec_eq(v_c_127_, v___x_169_);
if (v___x_170_ == 0)
{
return v___x_166_;
}
else
{
goto v___jp_157_;
}
}
else
{
goto v___jp_157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLetterLike___boxed(lean_object* v_c_177_){
_start:
{
uint32_t v_c_boxed_178_; uint8_t v_res_179_; lean_object* v_r_180_; 
v_c_boxed_178_ = lean_unbox_uint32(v_c_177_);
lean_dec(v_c_177_);
v_res_179_ = l_Lean_isLetterLike(v_c_boxed_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNumericSubscript(uint32_t v_c_181_){
_start:
{
uint32_t v___x_182_; uint8_t v___x_183_; 
v___x_182_ = 8320;
v___x_183_ = lean_uint32_dec_le(v___x_182_, v_c_181_);
if (v___x_183_ == 0)
{
return v___x_183_;
}
else
{
uint32_t v___x_184_; uint8_t v___x_185_; 
v___x_184_ = 8329;
v___x_185_ = lean_uint32_dec_le(v_c_181_, v___x_184_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNumericSubscript___boxed(lean_object* v_c_186_){
_start:
{
uint32_t v_c_boxed_187_; uint8_t v_res_188_; lean_object* v_r_189_; 
v_c_boxed_187_ = lean_unbox_uint32(v_c_186_);
lean_dec(v_c_186_);
v_res_188_ = l_Lean_isNumericSubscript(v_c_boxed_187_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
LEAN_EXPORT uint8_t l_Lean_isSubScriptAlnum(uint32_t v_c_190_){
_start:
{
uint32_t v___x_204_; uint8_t v___x_205_; 
v___x_204_ = 8320;
v___x_205_ = lean_uint32_dec_le(v___x_204_, v_c_190_);
if (v___x_205_ == 0)
{
goto v___jp_199_;
}
else
{
uint32_t v___x_206_; uint8_t v___x_207_; 
v___x_206_ = 8329;
v___x_207_ = lean_uint32_dec_le(v_c_190_, v___x_206_);
if (v___x_207_ == 0)
{
goto v___jp_199_;
}
else
{
return v___x_207_;
}
}
v___jp_191_:
{
uint32_t v___x_192_; uint8_t v___x_193_; 
v___x_192_ = 11388;
v___x_193_ = lean_uint32_dec_eq(v_c_190_, v___x_192_);
return v___x_193_;
}
v___jp_194_:
{
uint32_t v___x_195_; uint8_t v___x_196_; 
v___x_195_ = 7522;
v___x_196_ = lean_uint32_dec_le(v___x_195_, v_c_190_);
if (v___x_196_ == 0)
{
goto v___jp_191_;
}
else
{
uint32_t v___x_197_; uint8_t v___x_198_; 
v___x_197_ = 7530;
v___x_198_ = lean_uint32_dec_le(v_c_190_, v___x_197_);
if (v___x_198_ == 0)
{
goto v___jp_191_;
}
else
{
return v___x_198_;
}
}
}
v___jp_199_:
{
uint32_t v___x_200_; uint8_t v___x_201_; 
v___x_200_ = 8336;
v___x_201_ = lean_uint32_dec_le(v___x_200_, v_c_190_);
if (v___x_201_ == 0)
{
goto v___jp_194_;
}
else
{
uint32_t v___x_202_; uint8_t v___x_203_; 
v___x_202_ = 8348;
v___x_203_ = lean_uint32_dec_le(v_c_190_, v___x_202_);
if (v___x_203_ == 0)
{
goto v___jp_194_;
}
else
{
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object* v_c_208_){
_start:
{
uint32_t v_c_boxed_209_; uint8_t v_res_210_; lean_object* v_r_211_; 
v_c_boxed_209_ = lean_unbox_uint32(v_c_208_);
lean_dec(v_c_208_);
v_res_210_ = l_Lean_isSubScriptAlnum(v_c_boxed_209_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirst(uint32_t v_c_212_){
_start:
{
uint32_t v___x_222_; uint8_t v___x_223_; 
v___x_222_ = 65;
v___x_223_ = lean_uint32_dec_le(v___x_222_, v_c_212_);
if (v___x_223_ == 0)
{
goto v___jp_217_;
}
else
{
uint32_t v___x_224_; uint8_t v___x_225_; 
v___x_224_ = 90;
v___x_225_ = lean_uint32_dec_le(v_c_212_, v___x_224_);
if (v___x_225_ == 0)
{
goto v___jp_217_;
}
else
{
return v___x_225_;
}
}
v___jp_213_:
{
uint32_t v___x_214_; uint8_t v___x_215_; 
v___x_214_ = 95;
v___x_215_ = lean_uint32_dec_eq(v_c_212_, v___x_214_);
if (v___x_215_ == 0)
{
uint8_t v___x_216_; 
v___x_216_ = l_Lean_isLetterLike(v_c_212_);
return v___x_216_;
}
else
{
return v___x_215_;
}
}
v___jp_217_:
{
uint32_t v___x_218_; uint8_t v___x_219_; 
v___x_218_ = 97;
v___x_219_ = lean_uint32_dec_le(v___x_218_, v_c_212_);
if (v___x_219_ == 0)
{
goto v___jp_213_;
}
else
{
uint32_t v___x_220_; uint8_t v___x_221_; 
v___x_220_ = 122;
v___x_221_ = lean_uint32_dec_le(v_c_212_, v___x_220_);
if (v___x_221_ == 0)
{
goto v___jp_213_;
}
else
{
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirst___boxed(lean_object* v_c_226_){
_start:
{
uint32_t v_c_boxed_227_; uint8_t v_res_228_; lean_object* v_r_229_; 
v_c_boxed_227_ = lean_unbox_uint32(v_c_226_);
lean_dec(v_c_226_);
v_res_228_ = l_Lean_isIdFirst(v_c_boxed_227_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t v_c_230_){
_start:
{
uint8_t v___x_236_; uint8_t v___x_237_; 
v___x_236_ = 97;
v___x_237_ = lean_uint8_dec_le(v___x_236_, v_c_230_);
if (v___x_237_ == 0)
{
goto v___jp_231_;
}
else
{
uint8_t v___x_238_; uint8_t v___x_239_; 
v___x_238_ = 122;
v___x_239_ = lean_uint8_dec_le(v_c_230_, v___x_238_);
if (v___x_239_ == 0)
{
goto v___jp_231_;
}
else
{
return v___x_239_;
}
}
v___jp_231_:
{
uint8_t v___x_232_; uint8_t v___x_233_; 
v___x_232_ = 65;
v___x_233_ = lean_uint8_dec_le(v___x_232_, v_c_230_);
if (v___x_233_ == 0)
{
return v___x_233_;
}
else
{
uint8_t v___x_234_; uint8_t v___x_235_; 
v___x_234_ = 90;
v___x_235_ = lean_uint8_dec_le(v_c_230_, v___x_234_);
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object* v_c_240_){
_start:
{
uint8_t v_c_boxed_241_; uint8_t v_res_242_; lean_object* v_r_243_; 
v_c_boxed_241_ = lean_unbox(v_c_240_);
v_res_242_ = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(v_c_boxed_241_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirstAscii(uint8_t v_c_244_){
_start:
{
uint8_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = 97;
v___x_254_ = lean_uint8_dec_le(v___x_253_, v_c_244_);
if (v___x_254_ == 0)
{
goto v___jp_248_;
}
else
{
uint8_t v___x_255_; uint8_t v___x_256_; 
v___x_255_ = 122;
v___x_256_ = lean_uint8_dec_le(v_c_244_, v___x_255_);
if (v___x_256_ == 0)
{
goto v___jp_248_;
}
else
{
return v___x_256_;
}
}
v___jp_245_:
{
uint8_t v___x_246_; uint8_t v___x_247_; 
v___x_246_ = 95;
v___x_247_ = lean_uint8_dec_eq(v_c_244_, v___x_246_);
return v___x_247_;
}
v___jp_248_:
{
uint8_t v___x_249_; uint8_t v___x_250_; 
v___x_249_ = 65;
v___x_250_ = lean_uint8_dec_le(v___x_249_, v_c_244_);
if (v___x_250_ == 0)
{
goto v___jp_245_;
}
else
{
uint8_t v___x_251_; uint8_t v___x_252_; 
v___x_251_ = 90;
v___x_252_ = lean_uint8_dec_le(v_c_244_, v___x_251_);
if (v___x_252_ == 0)
{
goto v___jp_245_;
}
else
{
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object* v_c_257_){
_start:
{
uint8_t v_c_boxed_258_; uint8_t v_res_259_; lean_object* v_r_260_; 
v_c_boxed_258_ = lean_unbox(v_c_257_);
v_res_259_ = l_Lean_isIdFirstAscii(v_c_boxed_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t v_c_261_){
_start:
{
uint8_t v___x_272_; uint8_t v___x_273_; 
v___x_272_ = 97;
v___x_273_ = lean_uint8_dec_le(v___x_272_, v_c_261_);
if (v___x_273_ == 0)
{
goto v___jp_267_;
}
else
{
uint8_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = 122;
v___x_275_ = lean_uint8_dec_le(v_c_261_, v___x_274_);
if (v___x_275_ == 0)
{
goto v___jp_267_;
}
else
{
return v___x_275_;
}
}
v___jp_262_:
{
uint8_t v___x_263_; uint8_t v___x_264_; 
v___x_263_ = 48;
v___x_264_ = lean_uint8_dec_le(v___x_263_, v_c_261_);
if (v___x_264_ == 0)
{
return v___x_264_;
}
else
{
uint8_t v___x_265_; uint8_t v___x_266_; 
v___x_265_ = 57;
v___x_266_ = lean_uint8_dec_le(v_c_261_, v___x_265_);
return v___x_266_;
}
}
v___jp_267_:
{
uint8_t v___x_268_; uint8_t v___x_269_; 
v___x_268_ = 65;
v___x_269_ = lean_uint8_dec_le(v___x_268_, v_c_261_);
if (v___x_269_ == 0)
{
goto v___jp_262_;
}
else
{
uint8_t v___x_270_; uint8_t v___x_271_; 
v___x_270_ = 90;
v___x_271_ = lean_uint8_dec_le(v_c_261_, v___x_270_);
if (v___x_271_ == 0)
{
goto v___jp_262_;
}
else
{
return v___x_271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object* v_c_276_){
_start:
{
uint8_t v_c_boxed_277_; uint8_t v_res_278_; lean_object* v_r_279_; 
v_c_boxed_277_ = lean_unbox(v_c_276_);
v_res_278_ = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(v_c_boxed_277_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRest(uint32_t v_c_280_){
_start:
{
uint32_t v___x_302_; uint8_t v___x_303_; 
v___x_302_ = 65;
v___x_303_ = lean_uint32_dec_le(v___x_302_, v_c_280_);
if (v___x_303_ == 0)
{
goto v___jp_297_;
}
else
{
uint32_t v___x_304_; uint8_t v___x_305_; 
v___x_304_ = 90;
v___x_305_ = lean_uint32_dec_le(v_c_280_, v___x_304_);
if (v___x_305_ == 0)
{
goto v___jp_297_;
}
else
{
return v___x_305_;
}
}
v___jp_281_:
{
uint32_t v___x_282_; uint8_t v___x_283_; 
v___x_282_ = 95;
v___x_283_ = lean_uint32_dec_eq(v_c_280_, v___x_282_);
if (v___x_283_ == 0)
{
uint32_t v___x_284_; uint8_t v___x_285_; 
v___x_284_ = 39;
v___x_285_ = lean_uint32_dec_eq(v_c_280_, v___x_284_);
if (v___x_285_ == 0)
{
uint32_t v___x_286_; uint8_t v___x_287_; 
v___x_286_ = 33;
v___x_287_ = lean_uint32_dec_eq(v_c_280_, v___x_286_);
if (v___x_287_ == 0)
{
uint32_t v___x_288_; uint8_t v___x_289_; 
v___x_288_ = 63;
v___x_289_ = lean_uint32_dec_eq(v_c_280_, v___x_288_);
if (v___x_289_ == 0)
{
uint8_t v___x_290_; 
v___x_290_ = l_Lean_isLetterLike(v_c_280_);
if (v___x_290_ == 0)
{
uint8_t v___x_291_; 
v___x_291_ = l_Lean_isSubScriptAlnum(v_c_280_);
return v___x_291_;
}
else
{
return v___x_290_;
}
}
else
{
return v___x_289_;
}
}
else
{
return v___x_287_;
}
}
else
{
return v___x_285_;
}
}
else
{
return v___x_283_;
}
}
v___jp_292_:
{
uint32_t v___x_293_; uint8_t v___x_294_; 
v___x_293_ = 48;
v___x_294_ = lean_uint32_dec_le(v___x_293_, v_c_280_);
if (v___x_294_ == 0)
{
goto v___jp_281_;
}
else
{
uint32_t v___x_295_; uint8_t v___x_296_; 
v___x_295_ = 57;
v___x_296_ = lean_uint32_dec_le(v_c_280_, v___x_295_);
if (v___x_296_ == 0)
{
goto v___jp_281_;
}
else
{
return v___x_296_;
}
}
}
v___jp_297_:
{
uint32_t v___x_298_; uint8_t v___x_299_; 
v___x_298_ = 97;
v___x_299_ = lean_uint32_dec_le(v___x_298_, v_c_280_);
if (v___x_299_ == 0)
{
goto v___jp_292_;
}
else
{
uint32_t v___x_300_; uint8_t v___x_301_; 
v___x_300_ = 122;
v___x_301_ = lean_uint32_dec_le(v_c_280_, v___x_300_);
if (v___x_301_ == 0)
{
goto v___jp_292_;
}
else
{
return v___x_301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object* v_c_306_){
_start:
{
uint32_t v_c_boxed_307_; uint8_t v_res_308_; lean_object* v_r_309_; 
v_c_boxed_307_ = lean_unbox_uint32(v_c_306_);
lean_dec(v_c_306_);
v_res_308_ = l_Lean_isIdRest(v_c_boxed_307_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRestAscii(uint8_t v_c_310_){
_start:
{
uint8_t v___x_330_; uint8_t v___x_331_; 
v___x_330_ = 97;
v___x_331_ = lean_uint8_dec_le(v___x_330_, v_c_310_);
if (v___x_331_ == 0)
{
goto v___jp_325_;
}
else
{
uint8_t v___x_332_; uint8_t v___x_333_; 
v___x_332_ = 122;
v___x_333_ = lean_uint8_dec_le(v_c_310_, v___x_332_);
if (v___x_333_ == 0)
{
goto v___jp_325_;
}
else
{
return v___x_333_;
}
}
v___jp_311_:
{
uint8_t v___x_312_; uint8_t v___x_313_; 
v___x_312_ = 95;
v___x_313_ = lean_uint8_dec_eq(v_c_310_, v___x_312_);
if (v___x_313_ == 0)
{
uint8_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = 39;
v___x_315_ = lean_uint8_dec_eq(v_c_310_, v___x_314_);
if (v___x_315_ == 0)
{
uint8_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 33;
v___x_317_ = lean_uint8_dec_eq(v_c_310_, v___x_316_);
if (v___x_317_ == 0)
{
uint8_t v___x_318_; uint8_t v___x_319_; 
v___x_318_ = 63;
v___x_319_ = lean_uint8_dec_eq(v_c_310_, v___x_318_);
return v___x_319_;
}
else
{
return v___x_317_;
}
}
else
{
return v___x_315_;
}
}
else
{
return v___x_313_;
}
}
v___jp_320_:
{
uint8_t v___x_321_; uint8_t v___x_322_; 
v___x_321_ = 48;
v___x_322_ = lean_uint8_dec_le(v___x_321_, v_c_310_);
if (v___x_322_ == 0)
{
goto v___jp_311_;
}
else
{
uint8_t v___x_323_; uint8_t v___x_324_; 
v___x_323_ = 57;
v___x_324_ = lean_uint8_dec_le(v_c_310_, v___x_323_);
if (v___x_324_ == 0)
{
goto v___jp_311_;
}
else
{
return v___x_324_;
}
}
}
v___jp_325_:
{
uint8_t v___x_326_; uint8_t v___x_327_; 
v___x_326_ = 65;
v___x_327_ = lean_uint8_dec_le(v___x_326_, v_c_310_);
if (v___x_327_ == 0)
{
goto v___jp_320_;
}
else
{
uint8_t v___x_328_; uint8_t v___x_329_; 
v___x_328_ = 90;
v___x_329_ = lean_uint8_dec_le(v_c_310_, v___x_328_);
if (v___x_329_ == 0)
{
goto v___jp_320_;
}
else
{
return v___x_329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRestAscii___boxed(lean_object* v_c_334_){
_start:
{
uint8_t v_c_boxed_335_; uint8_t v_res_336_; lean_object* v_r_337_; 
v_c_boxed_335_ = lean_unbox(v_c_334_);
v_res_336_ = l_Lean_isIdRestAscii(v_c_boxed_335_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
static uint32_t _init_l_Lean_idBeginEscape(void){
_start:
{
uint32_t v___x_338_; 
v___x_338_ = 171;
return v___x_338_;
}
}
static uint32_t _init_l_Lean_idEndEscape(void){
_start:
{
uint32_t v___x_339_; 
v___x_339_ = 187;
return v___x_339_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdBeginEscape(uint32_t v_c_340_){
_start:
{
uint32_t v___x_341_; uint8_t v___x_342_; 
v___x_341_ = 171;
v___x_342_ = lean_uint32_dec_eq(v_c_340_, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdBeginEscape___boxed(lean_object* v_c_343_){
_start:
{
uint32_t v_c_boxed_344_; uint8_t v_res_345_; lean_object* v_r_346_; 
v_c_boxed_344_ = lean_unbox_uint32(v_c_343_);
lean_dec(v_c_343_);
v_res_345_ = l_Lean_isIdBeginEscape(v_c_boxed_344_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdEndEscape(uint32_t v_c_347_){
_start:
{
uint32_t v___x_348_; uint8_t v___x_349_; 
v___x_348_ = 187;
v___x_349_ = lean_uint32_dec_eq(v_c_347_, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdEndEscape___boxed(lean_object* v_c_350_){
_start:
{
uint32_t v_c_boxed_351_; uint8_t v_res_352_; lean_object* v_r_353_; 
v_c_boxed_351_ = lean_unbox_uint32(v_c_350_);
lean_dec(v_c_350_);
v_res_352_ = l_Lean_isIdEndEscape(v_c_boxed_351_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot(lean_object* v_x_354_){
_start:
{
if (lean_obj_tag(v_x_354_) == 0)
{
return v_x_354_;
}
else
{
lean_object* v_pre_355_; 
v_pre_355_ = lean_ctor_get(v_x_354_, 0);
if (lean_obj_tag(v_pre_355_) == 0)
{
lean_inc(v_x_354_);
return v_x_354_;
}
else
{
v_x_354_ = v_pre_355_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot___boxed(lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Name_getRoot(v_x_357_);
lean_dec(v_x_357_);
return v_res_358_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInaccessibleUserName(lean_object* v_x_360_){
_start:
{
switch(lean_obj_tag(v_x_360_))
{
case 1:
{
lean_object* v_str_361_; uint32_t v___x_362_; uint8_t v___x_363_; 
v_str_361_ = lean_ctor_get(v_x_360_, 1);
lean_inc_ref_n(v_str_361_, 2);
lean_dec_ref_known(v_x_360_, 2);
v___x_362_ = 10013;
v___x_363_ = lean_string_contains(v_str_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_Name_isInaccessibleUserName___closed__0));
v___x_365_ = lean_string_dec_eq(v_str_361_, v___x_364_);
lean_dec_ref(v_str_361_);
return v___x_365_;
}
else
{
lean_dec_ref(v_str_361_);
return v___x_363_;
}
}
case 2:
{
lean_object* v_pre_366_; 
v_pre_366_ = lean_ctor_get(v_x_360_, 0);
lean_inc(v_pre_366_);
lean_dec_ref_known(v_x_360_, 2);
v_x_360_ = v_pre_366_;
goto _start;
}
default: 
{
uint8_t v___x_368_; 
lean_dec(v_x_360_);
v___x_368_ = 0;
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInaccessibleUserName___boxed(lean_object* v_x_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_Lean_Name_isInaccessibleUserName(v_x_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(lean_object* v_s_372_, lean_object* v_i_373_){
_start:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_string_utf8_byte_size(v_s_372_);
v___x_379_ = lean_nat_dec_lt(v_i_373_, v___x_378_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; 
lean_dec(v_i_373_);
v___x_380_ = 1;
return v___x_380_;
}
else
{
uint8_t v_c_381_; uint8_t v___x_401_; uint8_t v___x_402_; 
lean_inc(v_i_373_);
v_c_381_ = lean_string_get_byte_fast(v_s_372_, v_i_373_);
v___x_401_ = 97;
v___x_402_ = lean_uint8_dec_le(v___x_401_, v_c_381_);
if (v___x_402_ == 0)
{
goto v___jp_396_;
}
else
{
uint8_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 122;
v___x_404_ = lean_uint8_dec_le(v_c_381_, v___x_403_);
if (v___x_404_ == 0)
{
goto v___jp_396_;
}
else
{
goto v___jp_374_;
}
}
v___jp_382_:
{
uint8_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = 95;
v___x_384_ = lean_uint8_dec_eq(v_c_381_, v___x_383_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 39;
v___x_386_ = lean_uint8_dec_eq(v_c_381_, v___x_385_);
if (v___x_386_ == 0)
{
uint8_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 33;
v___x_388_ = lean_uint8_dec_eq(v_c_381_, v___x_387_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 63;
v___x_390_ = lean_uint8_dec_eq(v_c_381_, v___x_389_);
if (v___x_390_ == 0)
{
lean_dec(v_i_373_);
return v___x_390_;
}
else
{
goto v___jp_374_;
}
}
else
{
goto v___jp_374_;
}
}
else
{
goto v___jp_374_;
}
}
else
{
goto v___jp_374_;
}
}
v___jp_391_:
{
uint8_t v___x_392_; uint8_t v___x_393_; 
v___x_392_ = 48;
v___x_393_ = lean_uint8_dec_le(v___x_392_, v_c_381_);
if (v___x_393_ == 0)
{
goto v___jp_382_;
}
else
{
uint8_t v___x_394_; uint8_t v___x_395_; 
v___x_394_ = 57;
v___x_395_ = lean_uint8_dec_le(v_c_381_, v___x_394_);
if (v___x_395_ == 0)
{
goto v___jp_382_;
}
else
{
goto v___jp_374_;
}
}
}
v___jp_396_:
{
uint8_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 65;
v___x_398_ = lean_uint8_dec_le(v___x_397_, v_c_381_);
if (v___x_398_ == 0)
{
goto v___jp_391_;
}
else
{
uint8_t v___x_399_; uint8_t v___x_400_; 
v___x_399_ = 90;
v___x_400_ = lean_uint8_dec_le(v_c_381_, v___x_399_);
if (v___x_400_ == 0)
{
goto v___jp_391_;
}
else
{
goto v___jp_374_;
}
}
}
}
v___jp_374_:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_add(v_i_373_, v___x_375_);
lean_dec(v_i_373_);
v_i_373_ = v___x_376_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object* v_s_405_, lean_object* v_i_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_405_, v_i_406_);
lean_dec_ref(v_s_405_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object* v_s_409_){
_start:
{
lean_object* v___x_413_; uint8_t v_c_414_; uint8_t v___x_423_; uint8_t v___x_424_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v_c_414_ = lean_string_get_byte_fast(v_s_409_, v___x_413_);
v___x_423_ = 97;
v___x_424_ = lean_uint8_dec_le(v___x_423_, v_c_414_);
if (v___x_424_ == 0)
{
goto v___jp_418_;
}
else
{
uint8_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 122;
v___x_426_ = lean_uint8_dec_le(v_c_414_, v___x_425_);
if (v___x_426_ == 0)
{
goto v___jp_418_;
}
else
{
goto v___jp_410_;
}
}
v___jp_410_:
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_409_, v___x_411_);
return v___x_412_;
}
v___jp_415_:
{
uint8_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = 95;
v___x_417_ = lean_uint8_dec_eq(v_c_414_, v___x_416_);
if (v___x_417_ == 0)
{
return v___x_417_;
}
else
{
goto v___jp_410_;
}
}
v___jp_418_:
{
uint8_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 65;
v___x_420_ = lean_uint8_dec_le(v___x_419_, v_c_414_);
if (v___x_420_ == 0)
{
goto v___jp_415_;
}
else
{
uint8_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 90;
v___x_422_ = lean_uint8_dec_le(v_c_414_, v___x_421_);
if (v___x_422_ == 0)
{
goto v___jp_415_;
}
else
{
goto v___jp_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object* v_s_427_){
_start:
{
uint8_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_427_);
lean_dec_ref(v_s_427_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(lean_object* v_s_430_, lean_object* v_h_431_){
_start:
{
lean_object* v___x_435_; uint8_t v_c_436_; uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_435_ = lean_unsigned_to_nat(0u);
v_c_436_ = lean_string_get_byte_fast(v_s_430_, v___x_435_);
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
v___x_434_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_430_, v___x_433_);
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
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object* v_s_449_, lean_object* v_h_450_){
_start:
{
uint8_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(v_s_449_, v_h_450_);
lean_dec_ref(v_s_449_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(lean_object* v_s_454_){
_start:
{
uint32_t v___y_464_; uint32_t v___y_469_; lean_object* v___x_484_; uint8_t v_c_485_; uint8_t v___x_494_; uint8_t v___x_495_; 
v___x_484_ = lean_unsigned_to_nat(0u);
v_c_485_ = lean_string_get_byte_fast(v_s_454_, v___x_484_);
v___x_494_ = 97;
v___x_495_ = lean_uint8_dec_le(v___x_494_, v_c_485_);
if (v___x_495_ == 0)
{
goto v___jp_489_;
}
else
{
uint8_t v___x_496_; uint8_t v___x_497_; 
v___x_496_ = 122;
v___x_497_ = lean_uint8_dec_le(v_c_485_, v___x_496_);
if (v___x_497_ == 0)
{
goto v___jp_489_;
}
else
{
goto v___jp_481_;
}
}
v___jp_455_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_string_utf8_byte_size(v_s_454_);
v___x_458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_458_, 0, v_s_454_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_457_);
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_substring_drop(v___x_458_, v___x_459_);
v___x_461_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_462_ = lean_substring_all(v___x_460_, v___x_461_);
return v___x_462_;
}
v___jp_463_:
{
uint32_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = 95;
v___x_466_ = lean_uint32_dec_eq(v___y_464_, v___x_465_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; 
v___x_467_ = l_Lean_isLetterLike(v___y_464_);
if (v___x_467_ == 0)
{
lean_dec_ref(v_s_454_);
return v___x_467_;
}
else
{
goto v___jp_455_;
}
}
else
{
goto v___jp_455_;
}
}
v___jp_468_:
{
uint32_t v___x_470_; uint8_t v___x_471_; 
v___x_470_ = 97;
v___x_471_ = lean_uint32_dec_le(v___x_470_, v___y_469_);
if (v___x_471_ == 0)
{
v___y_464_ = v___y_469_;
goto v___jp_463_;
}
else
{
uint32_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = 122;
v___x_473_ = lean_uint32_dec_le(v___y_469_, v___x_472_);
if (v___x_473_ == 0)
{
v___y_464_ = v___y_469_;
goto v___jp_463_;
}
else
{
goto v___jp_455_;
}
}
}
v___jp_474_:
{
lean_object* v___x_475_; uint32_t v___x_476_; uint32_t v___x_477_; uint8_t v___x_478_; 
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_string_utf8_get(v_s_454_, v___x_475_);
v___x_477_ = 65;
v___x_478_ = lean_uint32_dec_le(v___x_477_, v___x_476_);
if (v___x_478_ == 0)
{
v___y_469_ = v___x_476_;
goto v___jp_468_;
}
else
{
uint32_t v___x_479_; uint8_t v___x_480_; 
v___x_479_ = 90;
v___x_480_ = lean_uint32_dec_le(v___x_476_, v___x_479_);
if (v___x_480_ == 0)
{
v___y_469_ = v___x_476_;
goto v___jp_468_;
}
else
{
goto v___jp_455_;
}
}
}
v___jp_481_:
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_454_, v___x_482_);
if (v___x_483_ == 0)
{
goto v___jp_474_;
}
else
{
lean_dec_ref(v_s_454_);
return v___x_483_;
}
}
v___jp_486_:
{
uint8_t v___x_487_; uint8_t v___x_488_; 
v___x_487_ = 95;
v___x_488_ = lean_uint8_dec_eq(v_c_485_, v___x_487_);
if (v___x_488_ == 0)
{
goto v___jp_474_;
}
else
{
goto v___jp_481_;
}
}
v___jp_489_:
{
uint8_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = 65;
v___x_491_ = lean_uint8_dec_le(v___x_490_, v_c_485_);
if (v___x_491_ == 0)
{
goto v___jp_486_;
}
else
{
uint8_t v___x_492_; uint8_t v___x_493_; 
v___x_492_ = 90;
v___x_493_ = lean_uint8_dec_le(v_c_485_, v___x_492_);
if (v___x_493_ == 0)
{
goto v___jp_486_;
}
else
{
goto v___jp_481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_498_){
_start:
{
uint8_t v_res_499_; lean_object* v_r_500_; 
v_res_499_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(v_s_498_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(lean_object* v_s_501_, lean_object* v_h_502_){
_start:
{
uint32_t v___y_512_; uint32_t v___y_517_; lean_object* v___x_532_; uint8_t v_c_533_; uint8_t v___x_542_; uint8_t v___x_543_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v_c_533_ = lean_string_get_byte_fast(v_s_501_, v___x_532_);
v___x_542_ = 97;
v___x_543_ = lean_uint8_dec_le(v___x_542_, v_c_533_);
if (v___x_543_ == 0)
{
goto v___jp_537_;
}
else
{
uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = 122;
v___x_545_ = lean_uint8_dec_le(v_c_533_, v___x_544_);
if (v___x_545_ == 0)
{
goto v___jp_537_;
}
else
{
goto v___jp_529_;
}
}
v___jp_503_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = lean_string_utf8_byte_size(v_s_501_);
v___x_506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_506_, 0, v_s_501_);
lean_ctor_set(v___x_506_, 1, v___x_504_);
lean_ctor_set(v___x_506_, 2, v___x_505_);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_substring_drop(v___x_506_, v___x_507_);
v___x_509_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_510_ = lean_substring_all(v___x_508_, v___x_509_);
return v___x_510_;
}
v___jp_511_:
{
uint32_t v___x_513_; uint8_t v___x_514_; 
v___x_513_ = 95;
v___x_514_ = lean_uint32_dec_eq(v___y_512_, v___x_513_);
if (v___x_514_ == 0)
{
uint8_t v___x_515_; 
v___x_515_ = l_Lean_isLetterLike(v___y_512_);
if (v___x_515_ == 0)
{
lean_dec_ref(v_s_501_);
return v___x_515_;
}
else
{
goto v___jp_503_;
}
}
else
{
goto v___jp_503_;
}
}
v___jp_516_:
{
uint32_t v___x_518_; uint8_t v___x_519_; 
v___x_518_ = 97;
v___x_519_ = lean_uint32_dec_le(v___x_518_, v___y_517_);
if (v___x_519_ == 0)
{
v___y_512_ = v___y_517_;
goto v___jp_511_;
}
else
{
uint32_t v___x_520_; uint8_t v___x_521_; 
v___x_520_ = 122;
v___x_521_ = lean_uint32_dec_le(v___y_517_, v___x_520_);
if (v___x_521_ == 0)
{
v___y_512_ = v___y_517_;
goto v___jp_511_;
}
else
{
goto v___jp_503_;
}
}
}
v___jp_522_:
{
lean_object* v___x_523_; uint32_t v___x_524_; uint32_t v___x_525_; uint8_t v___x_526_; 
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = lean_string_utf8_get(v_s_501_, v___x_523_);
v___x_525_ = 65;
v___x_526_ = lean_uint32_dec_le(v___x_525_, v___x_524_);
if (v___x_526_ == 0)
{
v___y_517_ = v___x_524_;
goto v___jp_516_;
}
else
{
uint32_t v___x_527_; uint8_t v___x_528_; 
v___x_527_ = 90;
v___x_528_ = lean_uint32_dec_le(v___x_524_, v___x_527_);
if (v___x_528_ == 0)
{
v___y_517_ = v___x_524_;
goto v___jp_516_;
}
else
{
goto v___jp_503_;
}
}
}
v___jp_529_:
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_501_, v___x_530_);
if (v___x_531_ == 0)
{
goto v___jp_522_;
}
else
{
lean_dec_ref(v_s_501_);
return v___x_531_;
}
}
v___jp_534_:
{
uint8_t v___x_535_; uint8_t v___x_536_; 
v___x_535_ = 95;
v___x_536_ = lean_uint8_dec_eq(v_c_533_, v___x_535_);
if (v___x_536_ == 0)
{
goto v___jp_522_;
}
else
{
goto v___jp_529_;
}
}
v___jp_537_:
{
uint8_t v___x_538_; uint8_t v___x_539_; 
v___x_538_ = 65;
v___x_539_ = lean_uint8_dec_le(v___x_538_, v_c_533_);
if (v___x_539_ == 0)
{
goto v___jp_534_;
}
else
{
uint8_t v___x_540_; uint8_t v___x_541_; 
v___x_540_ = 90;
v___x_541_ = lean_uint8_dec_le(v_c_533_, v___x_540_);
if (v___x_541_ == 0)
{
goto v___jp_534_;
}
else
{
goto v___jp_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_546_, lean_object* v_h_547_){
_start:
{
uint8_t v_res_548_; lean_object* v_r_549_; 
v_res_548_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(v_s_546_, v_h_547_);
v_r_549_ = lean_box(v_res_548_);
return v_r_549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape(lean_object* v_s_552_){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_553_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_554_ = lean_string_append(v___x_553_, v_s_552_);
v___x_555_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_556_ = lean_string_append(v___x_554_, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___boxed(lean_object* v_s_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Init_Meta_Defs_0__Lean_Name_escape(v_s_557_);
lean_dec_ref(v_s_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(lean_object* v_s_560_, uint8_t v_force_561_){
_start:
{
uint32_t v___y_581_; uint32_t v___y_586_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_602_ = lean_unsigned_to_nat(0u);
v___x_603_ = lean_string_utf8_byte_size(v_s_560_);
v___x_604_ = lean_nat_dec_lt(v___x_602_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_605_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_606_ = lean_string_append(v___x_605_, v_s_560_);
lean_dec_ref(v_s_560_);
v___x_607_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_608_ = lean_string_append(v___x_606_, v___x_607_);
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
else
{
if (v_force_561_ == 0)
{
uint8_t v_c_610_; uint8_t v___x_619_; uint8_t v___x_620_; 
v_c_610_ = lean_string_get_byte_fast(v_s_560_, v___x_602_);
v___x_619_ = 97;
v___x_620_ = lean_uint8_dec_le(v___x_619_, v_c_610_);
if (v___x_620_ == 0)
{
goto v___jp_614_;
}
else
{
uint8_t v___x_621_; uint8_t v___x_622_; 
v___x_621_ = 122;
v___x_622_ = lean_uint8_dec_le(v_c_610_, v___x_621_);
if (v___x_622_ == 0)
{
goto v___jp_614_;
}
else
{
goto v___jp_598_;
}
}
v___jp_611_:
{
uint8_t v___x_612_; uint8_t v___x_613_; 
v___x_612_ = 95;
v___x_613_ = lean_uint8_dec_eq(v_c_610_, v___x_612_);
if (v___x_613_ == 0)
{
goto v___jp_591_;
}
else
{
goto v___jp_598_;
}
}
v___jp_614_:
{
uint8_t v___x_615_; uint8_t v___x_616_; 
v___x_615_ = 65;
v___x_616_ = lean_uint8_dec_le(v___x_615_, v_c_610_);
if (v___x_616_ == 0)
{
goto v___jp_611_;
}
else
{
uint8_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = 90;
v___x_618_ = lean_uint8_dec_le(v_c_610_, v___x_617_);
if (v___x_618_ == 0)
{
goto v___jp_611_;
}
else
{
goto v___jp_598_;
}
}
}
}
else
{
goto v___jp_562_;
}
}
v___jp_562_:
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0));
lean_inc_ref(v_s_560_);
v___x_564_ = lean_string_any(v_s_560_, v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_565_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_566_ = lean_string_append(v___x_565_, v_s_560_);
lean_dec_ref(v_s_560_);
v___x_567_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_568_ = lean_string_append(v___x_566_, v___x_567_);
v___x_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
else
{
lean_object* v___x_570_; 
lean_dec_ref(v_s_560_);
v___x_570_ = lean_box(0);
return v___x_570_;
}
}
v___jp_571_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = lean_string_utf8_byte_size(v_s_560_);
lean_inc_ref(v_s_560_);
v___x_574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_574_, 0, v_s_560_);
lean_ctor_set(v___x_574_, 1, v___x_572_);
lean_ctor_set(v___x_574_, 2, v___x_573_);
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = lean_substring_drop(v___x_574_, v___x_575_);
v___x_577_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_578_ = lean_substring_all(v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
goto v___jp_562_;
}
else
{
lean_object* v___x_579_; 
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v_s_560_);
return v___x_579_;
}
}
v___jp_580_:
{
uint32_t v___x_582_; uint8_t v___x_583_; 
v___x_582_ = 95;
v___x_583_ = lean_uint32_dec_eq(v___y_581_, v___x_582_);
if (v___x_583_ == 0)
{
uint8_t v___x_584_; 
v___x_584_ = l_Lean_isLetterLike(v___y_581_);
if (v___x_584_ == 0)
{
goto v___jp_562_;
}
else
{
goto v___jp_571_;
}
}
else
{
goto v___jp_571_;
}
}
v___jp_585_:
{
uint32_t v___x_587_; uint8_t v___x_588_; 
v___x_587_ = 97;
v___x_588_ = lean_uint32_dec_le(v___x_587_, v___y_586_);
if (v___x_588_ == 0)
{
v___y_581_ = v___y_586_;
goto v___jp_580_;
}
else
{
uint32_t v___x_589_; uint8_t v___x_590_; 
v___x_589_ = 122;
v___x_590_ = lean_uint32_dec_le(v___y_586_, v___x_589_);
if (v___x_590_ == 0)
{
v___y_581_ = v___y_586_;
goto v___jp_580_;
}
else
{
goto v___jp_571_;
}
}
}
v___jp_591_:
{
lean_object* v___x_592_; uint32_t v___x_593_; uint32_t v___x_594_; uint8_t v___x_595_; 
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_string_utf8_get(v_s_560_, v___x_592_);
v___x_594_ = 65;
v___x_595_ = lean_uint32_dec_le(v___x_594_, v___x_593_);
if (v___x_595_ == 0)
{
v___y_586_ = v___x_593_;
goto v___jp_585_;
}
else
{
uint32_t v___x_596_; uint8_t v___x_597_; 
v___x_596_ = 90;
v___x_597_ = lean_uint32_dec_le(v___x_593_, v___x_596_);
if (v___x_597_ == 0)
{
v___y_586_ = v___x_593_;
goto v___jp_585_;
}
else
{
goto v___jp_571_;
}
}
}
v___jp_598_:
{
lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_560_, v___x_599_);
if (v___x_600_ == 0)
{
goto v___jp_591_;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_s_560_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object* v_s_623_, lean_object* v_force_624_){
_start:
{
uint8_t v_force_boxed_625_; lean_object* v_res_626_; 
v_force_boxed_625_ = lean_unbox(v_force_624_);
v_res_626_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(v_s_623_, v_force_boxed_625_);
return v_res_626_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t v___y_627_){
_start:
{
uint32_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = 187;
v___x_629_ = lean_uint32_dec_eq(v___y_627_, v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object* v___y_630_){
_start:
{
uint32_t v___y_271__boxed_631_; uint8_t v_res_632_; lean_object* v_r_633_; 
v___y_271__boxed_631_ = lean_unbox_uint32(v___y_630_);
lean_dec(v___y_630_);
v_res_632_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(v___y_271__boxed_631_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t v___y_634_){
_start:
{
uint32_t v___x_656_; uint8_t v___x_657_; 
v___x_656_ = 65;
v___x_657_ = lean_uint32_dec_le(v___x_656_, v___y_634_);
if (v___x_657_ == 0)
{
goto v___jp_651_;
}
else
{
uint32_t v___x_658_; uint8_t v___x_659_; 
v___x_658_ = 90;
v___x_659_ = lean_uint32_dec_le(v___y_634_, v___x_658_);
if (v___x_659_ == 0)
{
goto v___jp_651_;
}
else
{
return v___x_659_;
}
}
v___jp_635_:
{
uint32_t v___x_636_; uint8_t v___x_637_; 
v___x_636_ = 95;
v___x_637_ = lean_uint32_dec_eq(v___y_634_, v___x_636_);
if (v___x_637_ == 0)
{
uint32_t v___x_638_; uint8_t v___x_639_; 
v___x_638_ = 39;
v___x_639_ = lean_uint32_dec_eq(v___y_634_, v___x_638_);
if (v___x_639_ == 0)
{
uint32_t v___x_640_; uint8_t v___x_641_; 
v___x_640_ = 33;
v___x_641_ = lean_uint32_dec_eq(v___y_634_, v___x_640_);
if (v___x_641_ == 0)
{
uint32_t v___x_642_; uint8_t v___x_643_; 
v___x_642_ = 63;
v___x_643_ = lean_uint32_dec_eq(v___y_634_, v___x_642_);
if (v___x_643_ == 0)
{
uint8_t v___x_644_; 
v___x_644_ = l_Lean_isLetterLike(v___y_634_);
if (v___x_644_ == 0)
{
uint8_t v___x_645_; 
v___x_645_ = l_Lean_isSubScriptAlnum(v___y_634_);
return v___x_645_;
}
else
{
return v___x_644_;
}
}
else
{
return v___x_643_;
}
}
else
{
return v___x_641_;
}
}
else
{
return v___x_639_;
}
}
else
{
return v___x_637_;
}
}
v___jp_646_:
{
uint32_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = 48;
v___x_648_ = lean_uint32_dec_le(v___x_647_, v___y_634_);
if (v___x_648_ == 0)
{
goto v___jp_635_;
}
else
{
uint32_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = 57;
v___x_650_ = lean_uint32_dec_le(v___y_634_, v___x_649_);
if (v___x_650_ == 0)
{
goto v___jp_635_;
}
else
{
return v___x_650_;
}
}
}
v___jp_651_:
{
uint32_t v___x_652_; uint8_t v___x_653_; 
v___x_652_ = 97;
v___x_653_ = lean_uint32_dec_le(v___x_652_, v___y_634_);
if (v___x_653_ == 0)
{
goto v___jp_646_;
}
else
{
uint32_t v___x_654_; uint8_t v___x_655_; 
v___x_654_ = 122;
v___x_655_ = lean_uint32_dec_le(v___y_634_, v___x_654_);
if (v___x_655_ == 0)
{
goto v___jp_646_;
}
else
{
return v___x_655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object* v___y_660_){
_start:
{
uint32_t v___y_278__boxed_661_; uint8_t v_res_662_; lean_object* v_r_663_; 
v___y_278__boxed_661_ = lean_unbox_uint32(v___y_660_);
lean_dec(v___y_660_);
v_res_662_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(v___y_278__boxed_661_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t v_escape_666_, lean_object* v_s_667_, uint8_t v_force_668_){
_start:
{
if (v_escape_666_ == 0)
{
return v_s_667_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = lean_string_utf8_byte_size(v_s_667_);
v___x_671_ = lean_nat_dec_lt(v___x_669_, v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_672_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_673_ = lean_string_append(v___x_672_, v_s_667_);
lean_dec_ref(v_s_667_);
v___x_674_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_675_ = lean_string_append(v___x_673_, v___x_674_);
return v___x_675_;
}
else
{
lean_object* v___f_676_; 
v___f_676_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
if (v_force_668_ == 0)
{
lean_object* v___f_683_; uint32_t v___y_690_; uint32_t v___y_695_; uint8_t v_c_709_; uint8_t v___x_718_; uint8_t v___x_719_; 
v___f_683_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_709_ = lean_string_get_byte_fast(v_s_667_, v___x_669_);
v___x_718_ = 97;
v___x_719_ = lean_uint8_dec_le(v___x_718_, v_c_709_);
if (v___x_719_ == 0)
{
goto v___jp_713_;
}
else
{
uint8_t v___x_720_; uint8_t v___x_721_; 
v___x_720_ = 122;
v___x_721_ = lean_uint8_dec_le(v_c_709_, v___x_720_);
if (v___x_721_ == 0)
{
goto v___jp_713_;
}
else
{
goto v___jp_706_;
}
}
v___jp_684_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
lean_inc_ref(v_s_667_);
v___x_685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_685_, 0, v_s_667_);
lean_ctor_set(v___x_685_, 1, v___x_669_);
lean_ctor_set(v___x_685_, 2, v___x_670_);
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = lean_substring_drop(v___x_685_, v___x_686_);
v___x_688_ = lean_substring_all(v___x_687_, v___f_683_);
if (v___x_688_ == 0)
{
goto v___jp_677_;
}
else
{
return v_s_667_;
}
}
v___jp_689_:
{
uint32_t v___x_691_; uint8_t v___x_692_; 
v___x_691_ = 95;
v___x_692_ = lean_uint32_dec_eq(v___y_690_, v___x_691_);
if (v___x_692_ == 0)
{
uint8_t v___x_693_; 
v___x_693_ = l_Lean_isLetterLike(v___y_690_);
if (v___x_693_ == 0)
{
goto v___jp_677_;
}
else
{
goto v___jp_684_;
}
}
else
{
goto v___jp_684_;
}
}
v___jp_694_:
{
uint32_t v___x_696_; uint8_t v___x_697_; 
v___x_696_ = 97;
v___x_697_ = lean_uint32_dec_le(v___x_696_, v___y_695_);
if (v___x_697_ == 0)
{
v___y_690_ = v___y_695_;
goto v___jp_689_;
}
else
{
uint32_t v___x_698_; uint8_t v___x_699_; 
v___x_698_ = 122;
v___x_699_ = lean_uint32_dec_le(v___y_695_, v___x_698_);
if (v___x_699_ == 0)
{
v___y_690_ = v___y_695_;
goto v___jp_689_;
}
else
{
goto v___jp_684_;
}
}
}
v___jp_700_:
{
uint32_t v___x_701_; uint32_t v___x_702_; uint8_t v___x_703_; 
v___x_701_ = lean_string_utf8_get(v_s_667_, v___x_669_);
v___x_702_ = 65;
v___x_703_ = lean_uint32_dec_le(v___x_702_, v___x_701_);
if (v___x_703_ == 0)
{
v___y_695_ = v___x_701_;
goto v___jp_694_;
}
else
{
uint32_t v___x_704_; uint8_t v___x_705_; 
v___x_704_ = 90;
v___x_705_ = lean_uint32_dec_le(v___x_701_, v___x_704_);
if (v___x_705_ == 0)
{
v___y_695_ = v___x_701_;
goto v___jp_694_;
}
else
{
goto v___jp_684_;
}
}
}
v___jp_706_:
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_667_, v___x_707_);
if (v___x_708_ == 0)
{
goto v___jp_700_;
}
else
{
return v_s_667_;
}
}
v___jp_710_:
{
uint8_t v___x_711_; uint8_t v___x_712_; 
v___x_711_ = 95;
v___x_712_ = lean_uint8_dec_eq(v_c_709_, v___x_711_);
if (v___x_712_ == 0)
{
goto v___jp_700_;
}
else
{
goto v___jp_706_;
}
}
v___jp_713_:
{
uint8_t v___x_714_; uint8_t v___x_715_; 
v___x_714_ = 65;
v___x_715_ = lean_uint8_dec_le(v___x_714_, v_c_709_);
if (v___x_715_ == 0)
{
goto v___jp_710_;
}
else
{
uint8_t v___x_716_; uint8_t v___x_717_; 
v___x_716_ = 90;
v___x_717_ = lean_uint8_dec_le(v_c_709_, v___x_716_);
if (v___x_717_ == 0)
{
goto v___jp_710_;
}
else
{
goto v___jp_706_;
}
}
}
}
else
{
goto v___jp_677_;
}
v___jp_677_:
{
uint8_t v___x_678_; 
lean_inc_ref(v_s_667_);
v___x_678_ = lean_string_any(v_s_667_, v___f_676_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_679_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_680_ = lean_string_append(v___x_679_, v_s_667_);
lean_dec_ref(v_s_667_);
v___x_681_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_682_ = lean_string_append(v___x_680_, v___x_681_);
return v___x_682_;
}
else
{
return v_s_667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_722_, lean_object* v_s_723_, lean_object* v_force_724_){
_start:
{
uint8_t v_escape_boxed_725_; uint8_t v_force_boxed_726_; lean_object* v_res_727_; 
v_escape_boxed_725_ = lean_unbox(v_escape_722_);
v_force_boxed_726_ = lean_unbox(v_force_724_);
v_res_727_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_boxed_725_, v_s_723_, v_force_boxed_726_);
return v_res_727_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object* v_x_728_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = 0;
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed(lean_object* v_x_730_){
_start:
{
uint8_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(v_x_730_);
lean_dec_ref(v_x_730_);
v_r_732_ = lean_box(v_res_731_);
return v_r_732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object* v_sep_735_, uint8_t v_escape_736_, lean_object* v_n_737_, lean_object* v_isToken_738_){
_start:
{
switch(lean_obj_tag(v_n_737_))
{
case 0:
{
lean_object* v___x_739_; 
lean_dec_ref(v_isToken_738_);
v___x_739_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_739_;
}
case 1:
{
lean_object* v_pre_740_; 
v_pre_740_ = lean_ctor_get(v_n_737_, 0);
if (lean_obj_tag(v_pre_740_) == 0)
{
lean_object* v_str_741_; lean_object* v___x_742_; uint8_t v___x_743_; lean_object* v___x_744_; 
v_str_741_ = lean_ctor_get(v_n_737_, 1);
lean_inc_ref_n(v_str_741_, 2);
lean_dec_ref_known(v_n_737_, 2);
v___x_742_ = lean_apply_1(v_isToken_738_, v_str_741_);
v___x_743_ = lean_unbox(v___x_742_);
v___x_744_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_736_, v_str_741_, v___x_743_);
return v___x_744_;
}
else
{
lean_object* v_str_745_; lean_object* v_r_746_; lean_object* v___x_747_; uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v_r_x27_750_; 
lean_inc(v_pre_740_);
v_str_745_ = lean_ctor_get(v_n_737_, 1);
lean_inc_ref_n(v_str_745_, 2);
lean_dec_ref_known(v_n_737_, 2);
lean_inc_ref(v_isToken_738_);
v_r_746_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_735_, v_escape_736_, v_pre_740_, v_isToken_738_);
v___x_747_ = lean_string_append(v_r_746_, v_sep_735_);
v___x_748_ = 0;
v___x_749_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_736_, v_str_745_, v___x_748_);
lean_inc_ref(v___x_747_);
v_r_x27_750_ = lean_string_append(v___x_747_, v___x_749_);
lean_dec_ref(v___x_749_);
if (v_escape_736_ == 0)
{
lean_dec_ref(v___x_747_);
lean_dec_ref(v_str_745_);
lean_dec_ref(v_isToken_738_);
return v_r_x27_750_;
}
else
{
lean_object* v___x_751_; uint8_t v___x_752_; 
lean_inc_ref(v_r_x27_750_);
v___x_751_ = lean_apply_1(v_isToken_738_, v_r_x27_750_);
v___x_752_ = lean_unbox(v___x_751_);
if (v___x_752_ == 0)
{
lean_dec_ref(v___x_747_);
lean_dec_ref(v_str_745_);
return v_r_x27_750_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref(v_r_x27_750_);
v___x_753_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_736_, v_str_745_, v_escape_736_);
v___x_754_ = lean_string_append(v___x_747_, v___x_753_);
lean_dec_ref(v___x_753_);
return v___x_754_;
}
}
}
}
default: 
{
lean_object* v_pre_755_; 
lean_dec_ref(v_isToken_738_);
v_pre_755_ = lean_ctor_get(v_n_737_, 0);
if (lean_obj_tag(v_pre_755_) == 0)
{
lean_object* v_i_756_; lean_object* v___x_757_; 
v_i_756_ = lean_ctor_get(v_n_737_, 1);
lean_inc(v_i_756_);
lean_dec_ref_known(v_n_737_, 2);
v___x_757_ = l_Nat_reprFast(v_i_756_);
return v___x_757_;
}
else
{
lean_object* v_i_758_; lean_object* v___f_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
lean_inc(v_pre_755_);
v_i_758_ = lean_ctor_get(v_n_737_, 1);
lean_inc(v_i_758_);
lean_dec_ref_known(v_n_737_, 2);
v___f_759_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1));
v___x_760_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_735_, v_escape_736_, v_pre_755_, v___f_759_);
v___x_761_ = lean_string_append(v___x_760_, v_sep_735_);
v___x_762_ = l_Nat_reprFast(v_i_758_);
v___x_763_ = lean_string_append(v___x_761_, v___x_762_);
lean_dec_ref(v___x_762_);
return v___x_763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object* v_sep_764_, lean_object* v_escape_765_, lean_object* v_n_766_, lean_object* v_isToken_767_){
_start:
{
uint8_t v_escape_boxed_768_; lean_object* v_res_769_; 
v_escape_boxed_768_ = lean_unbox(v_escape_765_);
v_res_769_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_764_, v_escape_boxed_768_, v_n_766_, v_isToken_767_);
lean_dec_ref(v_sep_764_);
return v_res_769_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object* v_n_775_){
_start:
{
lean_object* v___x_776_; uint8_t v___x_777_; uint8_t v___x_778_; 
v___x_776_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_777_ = lean_name_eq(v_n_775_, v___x_776_);
v___x_778_ = 1;
if (v___x_777_ == 0)
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Name_getRoot(v_n_775_);
if (lean_obj_tag(v___x_779_) == 1)
{
lean_object* v_str_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v_str_780_ = lean_ctor_get(v___x_779_, 1);
lean_inc_ref_n(v_str_780_, 2);
lean_dec_ref_known(v___x_779_, 2);
v___x_781_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_782_ = lean_string_isprefixof(v___x_781_, v_str_780_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3));
v___x_784_ = lean_string_isprefixof(v___x_783_, v_str_780_);
return v___x_784_;
}
else
{
lean_dec_ref(v_str_780_);
return v___x_778_;
}
}
else
{
lean_dec(v___x_779_);
return v___x_777_;
}
}
else
{
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_785_);
lean_dec(v_n_785_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object* v_n_788_, uint8_t v_escape_789_, lean_object* v_isToken_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_789_ == 0)
{
lean_object* v___x_792_; 
v___x_792_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_791_, v_escape_789_, v_n_788_, v_isToken_790_);
return v___x_792_;
}
else
{
uint8_t v___x_793_; 
lean_inc(v_n_788_);
v___x_793_ = l_Lean_Name_isInaccessibleUserName(v_n_788_);
if (v___x_793_ == 0)
{
uint8_t v___x_794_; 
v___x_794_ = l_Lean_Name_hasMacroScopes(v_n_788_);
if (v___x_794_ == 0)
{
uint8_t v___x_795_; 
v___x_795_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_788_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
v___x_796_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_791_, v_escape_789_, v_n_788_, v_isToken_790_);
return v___x_796_;
}
else
{
lean_object* v___x_797_; 
v___x_797_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_791_, v___x_794_, v_n_788_, v_isToken_790_);
return v___x_797_;
}
}
else
{
lean_object* v___x_798_; 
v___x_798_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_791_, v___x_793_, v_n_788_, v_isToken_790_);
return v___x_798_;
}
}
else
{
uint8_t v___x_799_; lean_object* v___x_800_; 
v___x_799_ = 0;
v___x_800_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_791_, v___x_799_, v_n_788_, v_isToken_790_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object* v_n_801_, lean_object* v_escape_802_, lean_object* v_isToken_803_){
_start:
{
uint8_t v_escape_boxed_804_; lean_object* v_res_805_; 
v_escape_boxed_804_ = lean_unbox(v_escape_802_);
v_res_805_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(v_n_801_, v_escape_boxed_804_, v_isToken_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object* v_sep_806_, uint8_t v_escape_807_, lean_object* v_n_808_){
_start:
{
switch(lean_obj_tag(v_n_808_))
{
case 0:
{
lean_object* v___x_809_; 
v___x_809_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_809_;
}
case 1:
{
lean_object* v_pre_810_; 
v_pre_810_ = lean_ctor_get(v_n_808_, 0);
if (lean_obj_tag(v_pre_810_) == 0)
{
lean_object* v_str_811_; uint8_t v___x_812_; lean_object* v___x_813_; 
v_str_811_ = lean_ctor_get(v_n_808_, 1);
lean_inc_ref(v_str_811_);
lean_dec_ref_known(v_n_808_, 2);
v___x_812_ = 0;
v___x_813_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_807_, v_str_811_, v___x_812_);
return v___x_813_;
}
else
{
lean_object* v_str_814_; lean_object* v_r_815_; lean_object* v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v_r_x27_819_; 
lean_inc(v_pre_810_);
v_str_814_ = lean_ctor_get(v_n_808_, 1);
lean_inc_ref(v_str_814_);
lean_dec_ref_known(v_n_808_, 2);
v_r_815_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_806_, v_escape_807_, v_pre_810_);
v___x_816_ = lean_string_append(v_r_815_, v_sep_806_);
v___x_817_ = 0;
v___x_818_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_807_, v_str_814_, v___x_817_);
v_r_x27_819_ = lean_string_append(v___x_816_, v___x_818_);
lean_dec_ref(v___x_818_);
return v_r_x27_819_;
}
}
default: 
{
lean_object* v_pre_820_; 
v_pre_820_ = lean_ctor_get(v_n_808_, 0);
if (lean_obj_tag(v_pre_820_) == 0)
{
lean_object* v_i_821_; lean_object* v___x_822_; 
v_i_821_ = lean_ctor_get(v_n_808_, 1);
lean_inc(v_i_821_);
lean_dec_ref_known(v_n_808_, 2);
v___x_822_ = l_Nat_reprFast(v_i_821_);
return v___x_822_;
}
else
{
lean_object* v_i_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
lean_inc(v_pre_820_);
v_i_823_ = lean_ctor_get(v_n_808_, 1);
lean_inc(v_i_823_);
lean_dec_ref_known(v_n_808_, 2);
v___x_824_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_806_, v_escape_807_, v_pre_820_);
v___x_825_ = lean_string_append(v___x_824_, v_sep_806_);
v___x_826_ = l_Nat_reprFast(v_i_823_);
v___x_827_ = lean_string_append(v___x_825_, v___x_826_);
lean_dec_ref(v___x_826_);
return v___x_827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object* v_sep_828_, lean_object* v_escape_829_, lean_object* v_n_830_){
_start:
{
uint8_t v_escape_boxed_831_; lean_object* v_res_832_; 
v_escape_boxed_831_ = lean_unbox(v_escape_829_);
v_res_832_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_828_, v_escape_boxed_831_, v_n_830_);
lean_dec_ref(v_sep_828_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object* v_n_833_, uint8_t v_escape_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_834_ == 0)
{
lean_object* v___x_836_; 
v___x_836_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_835_, v_escape_834_, v_n_833_);
return v___x_836_;
}
else
{
uint8_t v___x_837_; 
lean_inc(v_n_833_);
v___x_837_ = l_Lean_Name_isInaccessibleUserName(v_n_833_);
if (v___x_837_ == 0)
{
uint8_t v___x_838_; 
v___x_838_ = l_Lean_Name_hasMacroScopes(v_n_833_);
if (v___x_838_ == 0)
{
uint8_t v___x_839_; 
v___x_839_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_833_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
v___x_840_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_835_, v_escape_834_, v_n_833_);
return v___x_840_;
}
else
{
lean_object* v___x_841_; 
v___x_841_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_835_, v___x_838_, v_n_833_);
return v___x_841_;
}
}
else
{
lean_object* v___x_842_; 
v___x_842_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_835_, v___x_837_, v_n_833_);
return v___x_842_;
}
}
else
{
uint8_t v___x_843_; lean_object* v___x_844_; 
v___x_843_ = 0;
v___x_844_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_835_, v___x_843_, v_n_833_);
return v___x_844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object* v_n_845_, lean_object* v_escape_846_){
_start:
{
uint8_t v_escape_boxed_847_; lean_object* v_res_848_; 
v_escape_boxed_847_ = lean_unbox(v_escape_846_);
v_res_848_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_845_, v_escape_boxed_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object* v_n_849_, uint8_t v_escape_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_849_, v_escape_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object* v_n_852_, lean_object* v_escape_853_){
_start:
{
uint8_t v_escape_boxed_854_; lean_object* v_res_855_; 
v_escape_boxed_854_ = lean_unbox(v_escape_853_);
v_res_855_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(v_n_852_, v_escape_boxed_854_);
return v_res_855_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_hasNum(lean_object* v_x_856_){
_start:
{
switch(lean_obj_tag(v_x_856_))
{
case 0:
{
uint8_t v___x_857_; 
v___x_857_ = 0;
return v___x_857_;
}
case 1:
{
lean_object* v_pre_858_; 
v_pre_858_ = lean_ctor_get(v_x_856_, 0);
v_x_856_ = v_pre_858_;
goto _start;
}
default: 
{
uint8_t v___x_860_; 
v___x_860_ = 1;
return v___x_860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_hasNum___boxed(lean_object* v_x_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l_Lean_Name_hasNum(v_x_861_);
lean_dec(v_x_861_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object* v_n_879_, lean_object* v_prec_880_){
_start:
{
switch(lean_obj_tag(v_n_879_))
{
case 0:
{
lean_object* v___x_881_; 
v___x_881_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__1));
return v___x_881_;
}
case 1:
{
lean_object* v_pre_882_; lean_object* v_str_883_; uint8_t v___x_884_; 
v_pre_882_ = lean_ctor_get(v_n_879_, 0);
v_str_883_ = lean_ctor_get(v_n_879_, 1);
v___x_884_ = l_Lean_Name_hasNum(v_pre_882_);
if (v___x_884_ == 0)
{
uint8_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_885_ = 1;
v___x_886_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__3));
v___x_887_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_879_, v___x_885_);
v___x_888_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
v___x_889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_886_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
return v___x_889_;
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_inc_ref(v_str_883_);
lean_inc(v_pre_882_);
lean_dec_ref_known(v_n_879_, 2);
v___x_890_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__5));
v___x_891_ = lean_unsigned_to_nat(1024u);
v___x_892_ = l_Lean_Name_reprPrec(v_pre_882_, v___x_891_);
v___x_893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_890_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = l_String_quote(v_str_883_);
v___x_897_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_895_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l_Repr_addAppParen(v___x_898_, v_prec_880_);
return v___x_899_;
}
}
default: 
{
lean_object* v_pre_900_; lean_object* v_i_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_pre_900_ = lean_ctor_get(v_n_879_, 0);
lean_inc(v_pre_900_);
v_i_901_ = lean_ctor_get(v_n_879_, 1);
lean_inc(v_i_901_);
lean_dec_ref_known(v_n_879_, 2);
v___x_902_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__9));
v___x_903_ = lean_unsigned_to_nat(1024u);
v___x_904_ = l_Lean_Name_reprPrec(v_pre_900_, v___x_903_);
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_902_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_Nat_reprFast(v_i_901_);
v___x_909_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_907_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l_Repr_addAppParen(v___x_910_, v_prec_880_);
return v___x_911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object* v_n_912_, lean_object* v_prec_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Name_reprPrec(v_n_912_, v_prec_913_);
lean_dec(v_prec_913_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object* v_x_917_){
_start:
{
if (lean_obj_tag(v_x_917_) == 1)
{
lean_object* v_pre_918_; lean_object* v_str_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_pre_918_ = lean_ctor_get(v_x_917_, 0);
lean_inc(v_pre_918_);
v_str_919_ = lean_ctor_get(v_x_917_, 1);
lean_inc_ref(v_str_919_);
lean_dec_ref_known(v_x_917_, 2);
v___x_920_ = lean_string_capitalize(v_str_919_);
v___x_921_ = l_Lean_Name_str___override(v_pre_918_, v___x_920_);
return v___x_921_;
}
else
{
return v_x_917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object* v_x_922_, lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
switch(lean_obj_tag(v_x_922_))
{
case 0:
{
if (lean_obj_tag(v_x_923_) == 0)
{
lean_inc(v_x_924_);
return v_x_924_;
}
else
{
return v_x_922_;
}
}
case 1:
{
lean_object* v_pre_925_; lean_object* v_str_926_; uint8_t v___x_927_; 
v_pre_925_ = lean_ctor_get(v_x_922_, 0);
lean_inc(v_pre_925_);
v_str_926_ = lean_ctor_get(v_x_922_, 1);
lean_inc_ref(v_str_926_);
v___x_927_ = lean_name_eq(v_x_922_, v_x_923_);
lean_dec_ref_known(v_x_922_, 2);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = l_Lean_Name_replacePrefix(v_pre_925_, v_x_923_, v_x_924_);
v___x_929_ = l_Lean_Name_str___override(v___x_928_, v_str_926_);
return v___x_929_;
}
else
{
lean_dec_ref(v_str_926_);
lean_dec(v_pre_925_);
lean_inc(v_x_924_);
return v_x_924_;
}
}
default: 
{
lean_object* v_pre_930_; lean_object* v_i_931_; uint8_t v___x_932_; 
v_pre_930_ = lean_ctor_get(v_x_922_, 0);
lean_inc(v_pre_930_);
v_i_931_ = lean_ctor_get(v_x_922_, 1);
lean_inc(v_i_931_);
v___x_932_ = lean_name_eq(v_x_922_, v_x_923_);
lean_dec_ref_known(v_x_922_, 2);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = l_Lean_Name_replacePrefix(v_pre_930_, v_x_923_, v_x_924_);
v___x_934_ = l_Lean_Name_num___override(v___x_933_, v_i_931_);
return v___x_934_;
}
else
{
lean_dec(v_i_931_);
lean_dec(v_pre_930_);
lean_inc(v_x_924_);
return v_x_924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object* v_x_935_, lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Name_replacePrefix(v_x_935_, v_x_936_, v_x_937_);
lean_dec(v_x_937_);
lean_dec(v_x_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
switch(lean_obj_tag(v_x_940_))
{
case 0:
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v_x_939_);
return v___x_941_;
}
case 1:
{
if (lean_obj_tag(v_x_939_) == 1)
{
lean_object* v_pre_942_; lean_object* v_str_943_; lean_object* v_pre_944_; lean_object* v_str_945_; uint8_t v___x_946_; 
v_pre_942_ = lean_ctor_get(v_x_940_, 0);
v_str_943_ = lean_ctor_get(v_x_940_, 1);
v_pre_944_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_pre_944_);
v_str_945_ = lean_ctor_get(v_x_939_, 1);
lean_inc_ref(v_str_945_);
lean_dec_ref_known(v_x_939_, 2);
v___x_946_ = lean_string_dec_eq(v_str_945_, v_str_943_);
lean_dec_ref(v_str_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
lean_dec(v_pre_944_);
v___x_947_ = lean_box(0);
return v___x_947_;
}
else
{
v_x_939_ = v_pre_944_;
v_x_940_ = v_pre_942_;
goto _start;
}
}
else
{
lean_object* v___x_949_; 
lean_dec(v_x_939_);
v___x_949_ = lean_box(0);
return v___x_949_;
}
}
default: 
{
if (lean_obj_tag(v_x_939_) == 2)
{
lean_object* v_pre_950_; lean_object* v_i_951_; lean_object* v_pre_952_; lean_object* v_i_953_; uint8_t v___x_954_; 
v_pre_950_ = lean_ctor_get(v_x_940_, 0);
v_i_951_ = lean_ctor_get(v_x_940_, 1);
v_pre_952_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_pre_952_);
v_i_953_ = lean_ctor_get(v_x_939_, 1);
lean_inc(v_i_953_);
lean_dec_ref_known(v_x_939_, 2);
v___x_954_ = lean_nat_dec_eq(v_i_953_, v_i_951_);
lean_dec(v_i_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
lean_dec(v_pre_952_);
v___x_955_ = lean_box(0);
return v___x_955_;
}
else
{
v_x_939_ = v_pre_952_;
v_x_940_ = v_pre_950_;
goto _start;
}
}
else
{
lean_object* v___x_957_; 
lean_dec(v_x_939_);
v___x_957_ = lean_box(0);
return v___x_957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Name_eraseSuffix_x3f(v_x_958_, v_x_959_);
lean_dec(v_x_959_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object* v_n_961_, lean_object* v_f_962_){
_start:
{
uint8_t v___x_963_; 
v___x_963_ = l_Lean_Name_hasMacroScopes(v_n_961_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
v___x_964_ = lean_apply_1(v_f_962_, v_n_961_);
return v___x_964_;
}
else
{
lean_object* v_view_965_; lean_object* v_name_966_; lean_object* v_imported_967_; lean_object* v_ctx_968_; lean_object* v_scopes_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_978_; 
v_view_965_ = l_Lean_extractMacroScopes(v_n_961_);
v_name_966_ = lean_ctor_get(v_view_965_, 0);
v_imported_967_ = lean_ctor_get(v_view_965_, 1);
v_ctx_968_ = lean_ctor_get(v_view_965_, 2);
v_scopes_969_ = lean_ctor_get(v_view_965_, 3);
v_isSharedCheck_978_ = !lean_is_exclusive(v_view_965_);
if (v_isSharedCheck_978_ == 0)
{
v___x_971_ = v_view_965_;
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_scopes_969_);
lean_inc(v_ctx_968_);
lean_inc(v_imported_967_);
lean_inc(v_name_966_);
lean_dec(v_view_965_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = lean_apply_1(v_f_962_, v_name_966_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_973_);
v___x_975_ = v___x_971_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_imported_967_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_ctx_968_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v_scopes_969_);
v___x_975_ = v_reuseFailAlloc_977_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_MacroScopesView_review(v___x_975_);
return v___x_976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object* v_suffix_979_, lean_object* v_x_980_){
_start:
{
if (lean_obj_tag(v_x_980_) == 1)
{
lean_object* v_pre_981_; lean_object* v_str_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_pre_981_ = lean_ctor_get(v_x_980_, 0);
lean_inc(v_pre_981_);
v_str_982_ = lean_ctor_get(v_x_980_, 1);
lean_inc_ref(v_str_982_);
lean_dec_ref_known(v_x_980_, 2);
v___x_983_ = lean_string_append(v_str_982_, v_suffix_979_);
lean_dec_ref(v_suffix_979_);
v___x_984_ = l_Lean_Name_str___override(v_pre_981_, v___x_983_);
return v___x_984_;
}
else
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Name_str___override(v_x_980_, v_suffix_979_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_after(lean_object* v_n_986_, lean_object* v_suffix_987_){
_start:
{
uint8_t v___x_988_; 
v___x_988_ = l_Lean_Name_hasMacroScopes(v_n_986_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Name_appendAfter___lam__0(v_suffix_987_, v_n_986_);
return v___x_989_;
}
else
{
lean_object* v_view_990_; lean_object* v_name_991_; lean_object* v_imported_992_; lean_object* v_ctx_993_; lean_object* v_scopes_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1003_; 
v_view_990_ = l_Lean_extractMacroScopes(v_n_986_);
v_name_991_ = lean_ctor_get(v_view_990_, 0);
v_imported_992_ = lean_ctor_get(v_view_990_, 1);
v_ctx_993_ = lean_ctor_get(v_view_990_, 2);
v_scopes_994_ = lean_ctor_get(v_view_990_, 3);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_view_990_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_996_ = v_view_990_;
v_isShared_997_ = v_isSharedCheck_1003_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_scopes_994_);
lean_inc(v_ctx_993_);
lean_inc(v_imported_992_);
lean_inc(v_name_991_);
lean_dec(v_view_990_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1003_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_998_ = l_Lean_Name_appendAfter___lam__0(v_suffix_987_, v_name_991_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_imported_992_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_ctx_993_);
lean_ctor_set(v_reuseFailAlloc_1002_, 3, v_scopes_994_);
v___x_1000_ = v_reuseFailAlloc_1002_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_MacroScopesView_review(v___x_1000_);
return v___x_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object* v_idx_1004_, lean_object* v_x_1005_){
_start:
{
if (lean_obj_tag(v_x_1005_) == 1)
{
lean_object* v_pre_1006_; lean_object* v_str_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_pre_1006_ = lean_ctor_get(v_x_1005_, 0);
lean_inc(v_pre_1006_);
v_str_1007_ = lean_ctor_get(v_x_1005_, 1);
lean_inc_ref(v_str_1007_);
lean_dec_ref_known(v_x_1005_, 2);
v___x_1008_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1009_ = lean_string_append(v_str_1007_, v___x_1008_);
v___x_1010_ = l_Nat_reprFast(v_idx_1004_);
v___x_1011_ = lean_string_append(v___x_1009_, v___x_1010_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = l_Lean_Name_str___override(v_pre_1006_, v___x_1011_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1013_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1014_ = l_Nat_reprFast(v_idx_1004_);
v___x_1015_ = lean_string_append(v___x_1013_, v___x_1014_);
lean_dec_ref(v___x_1014_);
v___x_1016_ = l_Lean_Name_str___override(v_x_1005_, v___x_1015_);
return v___x_1016_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object* v_n_1017_, lean_object* v_idx_1018_){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = l_Lean_Name_hasMacroScopes(v_n_1017_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1018_, v_n_1017_);
return v___x_1020_;
}
else
{
lean_object* v_view_1021_; lean_object* v_name_1022_; lean_object* v_imported_1023_; lean_object* v_ctx_1024_; lean_object* v_scopes_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1034_; 
v_view_1021_ = l_Lean_extractMacroScopes(v_n_1017_);
v_name_1022_ = lean_ctor_get(v_view_1021_, 0);
v_imported_1023_ = lean_ctor_get(v_view_1021_, 1);
v_ctx_1024_ = lean_ctor_get(v_view_1021_, 2);
v_scopes_1025_ = lean_ctor_get(v_view_1021_, 3);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_view_1021_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1027_ = v_view_1021_;
v_isShared_1028_ = v_isSharedCheck_1034_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_scopes_1025_);
lean_inc(v_ctx_1024_);
lean_inc(v_imported_1023_);
lean_inc(v_name_1022_);
lean_dec(v_view_1021_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1034_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1018_, v_name_1022_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1029_);
v___x_1031_ = v___x_1027_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_imported_1023_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v_ctx_1024_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v_scopes_1025_);
v___x_1031_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_MacroScopesView_review(v___x_1031_);
return v___x_1032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object* v_pre_1035_, lean_object* v_x_1036_){
_start:
{
switch(lean_obj_tag(v_x_1036_))
{
case 0:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_Name_str___override(v_x_1036_, v_pre_1035_);
return v___x_1037_;
}
case 1:
{
lean_object* v_pre_1038_; lean_object* v_str_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_pre_1038_ = lean_ctor_get(v_x_1036_, 0);
lean_inc(v_pre_1038_);
v_str_1039_ = lean_ctor_get(v_x_1036_, 1);
lean_inc_ref(v_str_1039_);
lean_dec_ref_known(v_x_1036_, 2);
v___x_1040_ = lean_string_append(v_pre_1035_, v_str_1039_);
lean_dec_ref(v_str_1039_);
v___x_1041_ = l_Lean_Name_str___override(v_pre_1038_, v___x_1040_);
return v___x_1041_;
}
default: 
{
lean_object* v_pre_1042_; lean_object* v_i_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v_pre_1042_ = lean_ctor_get(v_x_1036_, 0);
lean_inc(v_pre_1042_);
v_i_1043_ = lean_ctor_get(v_x_1036_, 1);
lean_inc(v_i_1043_);
lean_dec_ref_known(v_x_1036_, 2);
v___x_1044_ = l_Lean_Name_str___override(v_pre_1042_, v_pre_1035_);
v___x_1045_ = l_Lean_Name_num___override(v___x_1044_, v_i_1043_);
return v___x_1045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore(lean_object* v_n_1046_, lean_object* v_pre_1047_){
_start:
{
uint8_t v___x_1048_; 
v___x_1048_ = l_Lean_Name_hasMacroScopes(v_n_1046_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_Name_appendBefore___lam__0(v_pre_1047_, v_n_1046_);
return v___x_1049_;
}
else
{
lean_object* v_view_1050_; lean_object* v_name_1051_; lean_object* v_imported_1052_; lean_object* v_ctx_1053_; lean_object* v_scopes_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1063_; 
v_view_1050_ = l_Lean_extractMacroScopes(v_n_1046_);
v_name_1051_ = lean_ctor_get(v_view_1050_, 0);
v_imported_1052_ = lean_ctor_get(v_view_1050_, 1);
v_ctx_1053_ = lean_ctor_get(v_view_1050_, 2);
v_scopes_1054_ = lean_ctor_get(v_view_1050_, 3);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_view_1050_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1056_ = v_view_1050_;
v_isShared_1057_ = v_isSharedCheck_1063_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_scopes_1054_);
lean_inc(v_ctx_1053_);
lean_inc(v_imported_1052_);
lean_inc(v_name_1051_);
lean_dec(v_view_1050_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1063_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1058_ = l_Lean_Name_appendBefore___lam__0(v_pre_1047_, v_name_1051_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1058_);
v___x_1060_ = v___x_1056_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_imported_1052_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v_ctx_1053_);
lean_ctor_set(v_reuseFailAlloc_1062_, 3, v_scopes_1054_);
v___x_1060_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_MacroScopesView_review(v___x_1060_);
return v___x_1061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object* v_x_1064_, lean_object* v_x_1065_, lean_object* v_h__1_1066_, lean_object* v_h__2_1067_, lean_object* v_h__3_1068_, lean_object* v_h__4_1069_){
_start:
{
switch(lean_obj_tag(v_x_1064_))
{
case 0:
{
lean_dec(v_h__3_1068_);
lean_dec(v_h__2_1067_);
if (lean_obj_tag(v_x_1065_) == 0)
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_dec(v_h__4_1069_);
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_apply_1(v_h__1_1066_, v___x_1070_);
return v___x_1071_;
}
else
{
lean_object* v___x_1072_; 
lean_dec(v_h__1_1066_);
v___x_1072_ = lean_apply_5(v_h__4_1069_, v_x_1064_, v_x_1065_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1072_;
}
}
case 1:
{
lean_dec(v_h__3_1068_);
lean_dec(v_h__1_1066_);
if (lean_obj_tag(v_x_1065_) == 1)
{
lean_object* v_pre_1073_; lean_object* v_str_1074_; lean_object* v_pre_1075_; lean_object* v_str_1076_; lean_object* v___x_1077_; 
lean_dec(v_h__4_1069_);
v_pre_1073_ = lean_ctor_get(v_x_1064_, 0);
lean_inc(v_pre_1073_);
v_str_1074_ = lean_ctor_get(v_x_1064_, 1);
lean_inc_ref(v_str_1074_);
lean_dec_ref_known(v_x_1064_, 2);
v_pre_1075_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_pre_1075_);
v_str_1076_ = lean_ctor_get(v_x_1065_, 1);
lean_inc_ref(v_str_1076_);
lean_dec_ref_known(v_x_1065_, 2);
v___x_1077_ = lean_apply_4(v_h__2_1067_, v_pre_1073_, v_str_1074_, v_pre_1075_, v_str_1076_);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; 
lean_dec(v_h__2_1067_);
v___x_1078_ = lean_apply_5(v_h__4_1069_, v_x_1064_, v_x_1065_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1078_;
}
}
default: 
{
lean_dec(v_h__2_1067_);
lean_dec(v_h__1_1066_);
if (lean_obj_tag(v_x_1065_) == 2)
{
lean_object* v_pre_1079_; lean_object* v_i_1080_; lean_object* v_pre_1081_; lean_object* v_i_1082_; lean_object* v___x_1083_; 
lean_dec(v_h__4_1069_);
v_pre_1079_ = lean_ctor_get(v_x_1064_, 0);
lean_inc(v_pre_1079_);
v_i_1080_ = lean_ctor_get(v_x_1064_, 1);
lean_inc(v_i_1080_);
lean_dec_ref_known(v_x_1064_, 2);
v_pre_1081_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_pre_1081_);
v_i_1082_ = lean_ctor_get(v_x_1065_, 1);
lean_inc(v_i_1082_);
lean_dec_ref_known(v_x_1065_, 2);
v___x_1083_ = lean_apply_4(v_h__3_1068_, v_pre_1079_, v_i_1080_, v_pre_1081_, v_i_1082_);
return v___x_1083_;
}
else
{
lean_object* v___x_1084_; 
lean_dec(v_h__3_1068_);
v___x_1084_ = lean_apply_5(v_h__4_1069_, v_x_1064_, v_x_1065_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object* v_motive_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_, lean_object* v_h__1_1088_, lean_object* v_h__2_1089_, lean_object* v_h__3_1090_, lean_object* v_h__4_1091_){
_start:
{
switch(lean_obj_tag(v_x_1086_))
{
case 0:
{
lean_dec(v_h__3_1090_);
lean_dec(v_h__2_1089_);
if (lean_obj_tag(v_x_1087_) == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_dec(v_h__4_1091_);
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_apply_1(v_h__1_1088_, v___x_1092_);
return v___x_1093_;
}
else
{
lean_object* v___x_1094_; 
lean_dec(v_h__1_1088_);
v___x_1094_ = lean_apply_5(v_h__4_1091_, v_x_1086_, v_x_1087_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1094_;
}
}
case 1:
{
lean_dec(v_h__3_1090_);
lean_dec(v_h__1_1088_);
if (lean_obj_tag(v_x_1087_) == 1)
{
lean_object* v_pre_1095_; lean_object* v_str_1096_; lean_object* v_pre_1097_; lean_object* v_str_1098_; lean_object* v___x_1099_; 
lean_dec(v_h__4_1091_);
v_pre_1095_ = lean_ctor_get(v_x_1086_, 0);
lean_inc(v_pre_1095_);
v_str_1096_ = lean_ctor_get(v_x_1086_, 1);
lean_inc_ref(v_str_1096_);
lean_dec_ref_known(v_x_1086_, 2);
v_pre_1097_ = lean_ctor_get(v_x_1087_, 0);
lean_inc(v_pre_1097_);
v_str_1098_ = lean_ctor_get(v_x_1087_, 1);
lean_inc_ref(v_str_1098_);
lean_dec_ref_known(v_x_1087_, 2);
v___x_1099_ = lean_apply_4(v_h__2_1089_, v_pre_1095_, v_str_1096_, v_pre_1097_, v_str_1098_);
return v___x_1099_;
}
else
{
lean_object* v___x_1100_; 
lean_dec(v_h__2_1089_);
v___x_1100_ = lean_apply_5(v_h__4_1091_, v_x_1086_, v_x_1087_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1100_;
}
}
default: 
{
lean_dec(v_h__2_1089_);
lean_dec(v_h__1_1088_);
if (lean_obj_tag(v_x_1087_) == 2)
{
lean_object* v_pre_1101_; lean_object* v_i_1102_; lean_object* v_pre_1103_; lean_object* v_i_1104_; lean_object* v___x_1105_; 
lean_dec(v_h__4_1091_);
v_pre_1101_ = lean_ctor_get(v_x_1086_, 0);
lean_inc(v_pre_1101_);
v_i_1102_ = lean_ctor_get(v_x_1086_, 1);
lean_inc(v_i_1102_);
lean_dec_ref_known(v_x_1086_, 2);
v_pre_1103_ = lean_ctor_get(v_x_1087_, 0);
lean_inc(v_pre_1103_);
v_i_1104_ = lean_ctor_get(v_x_1087_, 1);
lean_inc(v_i_1104_);
lean_dec_ref_known(v_x_1087_, 2);
v___x_1105_ = lean_apply_4(v_h__3_1090_, v_pre_1101_, v_i_1102_, v_pre_1103_, v_i_1104_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; 
lean_dec(v_h__3_1090_);
v___x_1106_ = lean_apply_5(v_h__4_1091_, v_x_1086_, v_x_1087_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1106_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Name_instDecidableEq(lean_object* v_a_1107_, lean_object* v_b_1108_){
_start:
{
uint8_t v___x_1109_; 
v___x_1109_ = lean_name_eq(v_a_1107_, v_b_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object* v_a_1110_, lean_object* v_b_1111_){
_start:
{
uint8_t v_res_1112_; lean_object* v_r_1113_; 
v_res_1112_ = l_Lean_Name_instDecidableEq(v_a_1110_, v_b_1111_);
lean_dec(v_b_1111_);
lean_dec(v_a_1110_);
v_r_1113_ = lean_box(v_res_1112_);
return v_r_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object* v_g_1114_){
_start:
{
lean_object* v_namePrefix_1115_; lean_object* v_idx_1116_; lean_object* v___x_1117_; 
v_namePrefix_1115_ = lean_ctor_get(v_g_1114_, 0);
lean_inc(v_namePrefix_1115_);
v_idx_1116_ = lean_ctor_get(v_g_1114_, 1);
lean_inc(v_idx_1116_);
lean_dec_ref(v_g_1114_);
v___x_1117_ = l_Lean_Name_num___override(v_namePrefix_1115_, v_idx_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object* v_g_1118_){
_start:
{
lean_object* v_namePrefix_1119_; lean_object* v_idx_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1129_; 
v_namePrefix_1119_ = lean_ctor_get(v_g_1118_, 0);
v_idx_1120_ = lean_ctor_get(v_g_1118_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_g_1118_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1122_ = v_g_1118_;
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_idx_1120_);
lean_inc(v_namePrefix_1119_);
lean_dec(v_g_1118_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1124_ = lean_unsigned_to_nat(1u);
v___x_1125_ = lean_nat_add(v_idx_1120_, v___x_1124_);
lean_dec(v_idx_1120_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 1, v___x_1125_);
v___x_1127_ = v___x_1122_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_namePrefix_1119_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object* v_g_1130_){
_start:
{
lean_object* v_namePrefix_1131_; lean_object* v_idx_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1144_; 
v_namePrefix_1131_ = lean_ctor_get(v_g_1130_, 0);
v_idx_1132_ = lean_ctor_get(v_g_1130_, 1);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_g_1130_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1134_ = v_g_1130_;
v_isShared_1135_ = v_isSharedCheck_1144_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_idx_1132_);
lean_inc(v_namePrefix_1131_);
lean_dec(v_g_1130_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1144_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_inc(v_idx_1132_);
lean_inc(v_namePrefix_1131_);
v___x_1136_ = l_Lean_Name_num___override(v_namePrefix_1131_, v_idx_1132_);
v___x_1137_ = lean_unsigned_to_nat(1u);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v___x_1137_);
lean_ctor_set(v___x_1134_, 0, v___x_1136_);
v___x_1139_ = v___x_1134_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_nat_add(v_idx_1132_, v___x_1137_);
lean_dec(v_idx_1132_);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v_namePrefix_1131_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1139_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
return v___x_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object* v_toPure_1145_, lean_object* v_r_1146_, lean_object* v_____r_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_apply_2(v_toPure_1145_, lean_box(0), v_r_1146_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object* v_toPure_1149_, lean_object* v_setNGen_1150_, lean_object* v_toBind_1151_, lean_object* v_ngen_1152_){
_start:
{
lean_object* v_namePrefix_1153_; lean_object* v_idx_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1167_; 
v_namePrefix_1153_ = lean_ctor_get(v_ngen_1152_, 0);
v_idx_1154_ = lean_ctor_get(v_ngen_1152_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_ngen_1152_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1156_ = v_ngen_1152_;
v_isShared_1157_ = v_isSharedCheck_1167_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_idx_1154_);
lean_inc(v_namePrefix_1153_);
lean_dec(v_ngen_1152_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1167_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v_r_1158_; lean_object* v___f_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
lean_inc(v_idx_1154_);
lean_inc(v_namePrefix_1153_);
v_r_1158_ = l_Lean_Name_num___override(v_namePrefix_1153_, v_idx_1154_);
v___f_1159_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1159_, 0, v_toPure_1149_);
lean_closure_set(v___f_1159_, 1, v_r_1158_);
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_nat_add(v_idx_1154_, v___x_1160_);
lean_dec(v_idx_1154_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 1, v___x_1161_);
v___x_1163_ = v___x_1156_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_namePrefix_1153_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_apply_1(v_setNGen_1150_, v___x_1163_);
v___x_1165_ = lean_apply_4(v_toBind_1151_, lean_box(0), lean_box(0), v___x_1164_, v___f_1159_);
return v___x_1165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object* v_inst_1168_, lean_object* v_inst_1169_){
_start:
{
lean_object* v_toApplicative_1170_; lean_object* v_toBind_1171_; lean_object* v_getNGen_1172_; lean_object* v_setNGen_1173_; lean_object* v_toPure_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; 
v_toApplicative_1170_ = lean_ctor_get(v_inst_1168_, 0);
lean_inc_ref(v_toApplicative_1170_);
v_toBind_1171_ = lean_ctor_get(v_inst_1168_, 1);
lean_inc_n(v_toBind_1171_, 2);
lean_dec_ref(v_inst_1168_);
v_getNGen_1172_ = lean_ctor_get(v_inst_1169_, 0);
lean_inc(v_getNGen_1172_);
v_setNGen_1173_ = lean_ctor_get(v_inst_1169_, 1);
lean_inc(v_setNGen_1173_);
lean_dec_ref(v_inst_1169_);
v_toPure_1174_ = lean_ctor_get(v_toApplicative_1170_, 1);
lean_inc(v_toPure_1174_);
lean_dec_ref(v_toApplicative_1170_);
v___f_1175_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1175_, 0, v_toPure_1174_);
lean_closure_set(v___f_1175_, 1, v_setNGen_1173_);
lean_closure_set(v___f_1175_, 2, v_toBind_1171_);
v___x_1176_ = lean_apply_4(v_toBind_1171_, lean_box(0), lean_box(0), v_getNGen_1172_, v___f_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object* v_m_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_mkFreshId___redArg(v_inst_1178_, v_inst_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object* v_setNGen_1181_, lean_object* v_inst_1182_, lean_object* v_ngen_1183_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_apply_1(v_setNGen_1181_, v_ngen_1183_);
v___x_1185_ = lean_apply_2(v_inst_1182_, lean_box(0), v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object* v_inst_1186_, lean_object* v_inst_1187_){
_start:
{
lean_object* v_getNGen_1188_; lean_object* v_setNGen_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1198_; 
v_getNGen_1188_ = lean_ctor_get(v_inst_1187_, 0);
v_setNGen_1189_ = lean_ctor_get(v_inst_1187_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_inst_1187_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1191_ = v_inst_1187_;
v_isShared_1192_ = v_isSharedCheck_1198_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_setNGen_1189_);
lean_inc(v_getNGen_1188_);
lean_dec(v_inst_1187_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1198_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___f_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
lean_inc(v_inst_1186_);
v___f_1193_ = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1193_, 0, v_setNGen_1189_);
lean_closure_set(v___f_1193_, 1, v_inst_1186_);
v___x_1194_ = lean_apply_2(v_inst_1186_, lean_box(0), v_getNGen_1188_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 1, v___f_1193_);
lean_ctor_set(v___x_1191_, 0, v___x_1194_);
v___x_1196_ = v___x_1191_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___f_1193_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object* v_m_1199_, lean_object* v_n_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_monadNameGeneratorLift___redArg(v_inst_1201_, v_inst_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1204_, lean_object* v_x_1205_, lean_object* v_x_1206_){
_start:
{
if (lean_obj_tag(v_x_1206_) == 0)
{
lean_dec(v_x_1204_);
return v_x_1205_;
}
else
{
lean_object* v_head_1207_; lean_object* v_tail_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1219_; 
v_head_1207_ = lean_ctor_get(v_x_1206_, 0);
v_tail_1208_ = lean_ctor_get(v_x_1206_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_x_1206_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1210_ = v_x_1206_;
v_isShared_1211_ = v_isSharedCheck_1219_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_tail_1208_);
lean_inc(v_head_1207_);
lean_dec(v_x_1206_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1219_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
lean_inc(v_x_1204_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set_tag(v___x_1210_, 5);
lean_ctor_set(v___x_1210_, 1, v_x_1204_);
lean_ctor_set(v___x_1210_, 0, v_x_1205_);
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_x_1205_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_x_1204_);
v___x_1213_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = l_String_quote(v_head_1207_);
v___x_1215_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1213_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v_x_1205_ = v___x_1216_;
v_x_1206_ = v_tail_1208_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object* v_x_1220_, lean_object* v_x_1221_, lean_object* v_x_1222_){
_start:
{
if (lean_obj_tag(v_x_1222_) == 0)
{
lean_dec(v_x_1220_);
return v_x_1221_;
}
else
{
lean_object* v_head_1223_; lean_object* v_tail_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1235_; 
v_head_1223_ = lean_ctor_get(v_x_1222_, 0);
v_tail_1224_ = lean_ctor_get(v_x_1222_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_x_1222_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1226_ = v_x_1222_;
v_isShared_1227_ = v_isSharedCheck_1235_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_tail_1224_);
lean_inc(v_head_1223_);
lean_dec(v_x_1222_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1235_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
lean_inc(v_x_1220_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set_tag(v___x_1226_, 5);
lean_ctor_set(v___x_1226_, 1, v_x_1220_);
lean_ctor_set(v___x_1226_, 0, v_x_1221_);
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_x_1221_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_x_1220_);
v___x_1229_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1230_ = l_String_quote(v_head_1223_);
v___x_1231_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
v___x_1232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1229_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(v_x_1220_, v___x_1232_, v_tail_1224_);
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = l_String_quote(v___y_1236_);
v___x_1238_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object* v_x_1239_, lean_object* v_x_1240_){
_start:
{
if (lean_obj_tag(v_x_1239_) == 0)
{
lean_object* v___x_1241_; 
lean_dec(v_x_1240_);
v___x_1241_ = lean_box(0);
return v___x_1241_;
}
else
{
lean_object* v_tail_1242_; 
v_tail_1242_ = lean_ctor_get(v_x_1239_, 1);
if (lean_obj_tag(v_tail_1242_) == 0)
{
lean_object* v_head_1243_; lean_object* v___x_1244_; 
lean_dec(v_x_1240_);
v_head_1243_ = lean_ctor_get(v_x_1239_, 0);
lean_inc(v_head_1243_);
lean_dec_ref_known(v_x_1239_, 2);
v___x_1244_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1243_);
return v___x_1244_;
}
else
{
lean_object* v_head_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_inc(v_tail_1242_);
v_head_1245_ = lean_ctor_get(v_x_1239_, 0);
lean_inc(v_head_1245_);
lean_dec_ref_known(v_x_1239_, 2);
v___x_1246_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1245_);
v___x_1247_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(v_x_1240_, v___x_1246_, v_tail_1242_);
return v___x_1247_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2));
v___x_1260_ = lean_string_length(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7);
v___x_1262_ = lean_nat_to_int(v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object* v_a_1267_){
_start:
{
if (lean_obj_tag(v_a_1267_) == 0)
{
lean_object* v___x_1268_; 
v___x_1268_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1269_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1270_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(v_a_1267_, v___x_1269_);
v___x_1271_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1272_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set(v___x_1273_, 1, v___x_1270_);
v___x_1274_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1271_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = l_Std_Format_fill(v___x_1276_);
return v___x_1277_;
}
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_unsigned_to_nat(2u);
v___x_1285_ = lean_nat_to_int(v___x_1284_);
return v___x_1285_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_unsigned_to_nat(1u);
v___x_1287_ = lean_nat_to_int(v___x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object* v_x_1294_, lean_object* v_prec_1295_){
_start:
{
if (lean_obj_tag(v_x_1294_) == 0)
{
lean_object* v_ns_1296_; lean_object* v___y_1298_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_ns_1296_ = lean_ctor_get(v_x_1294_, 0);
lean_inc(v_ns_1296_);
lean_dec_ref_known(v_x_1294_, 1);
v___x_1307_ = lean_unsigned_to_nat(1024u);
v___x_1308_ = lean_nat_dec_le(v___x_1307_, v_prec_1295_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1298_ = v___x_1309_;
goto v___jp_1297_;
}
else
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1298_ = v___x_1310_;
goto v___jp_1297_;
}
v___jp_1297_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1299_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__2));
v___x_1300_ = lean_unsigned_to_nat(1024u);
v___x_1301_ = l_Lean_Name_reprPrec(v_ns_1296_, v___x_1300_);
v___x_1302_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1299_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
lean_inc(v___y_1298_);
v___x_1303_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___y_1298_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = 0;
v___x_1305_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1305_, 0, v___x_1303_);
lean_ctor_set_uint8(v___x_1305_, sizeof(void*)*1, v___x_1304_);
v___x_1306_ = l_Repr_addAppParen(v___x_1305_, v_prec_1295_);
return v___x_1306_;
}
}
else
{
lean_object* v_n_1311_; lean_object* v_fields_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1336_; 
v_n_1311_ = lean_ctor_get(v_x_1294_, 0);
v_fields_1312_ = lean_ctor_get(v_x_1294_, 1);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_x_1294_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1314_ = v_x_1294_;
v_isShared_1315_ = v_isSharedCheck_1336_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_fields_1312_);
lean_inc(v_n_1311_);
lean_dec(v_x_1294_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1336_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___y_1317_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = lean_unsigned_to_nat(1024u);
v___x_1333_ = lean_nat_dec_le(v___x_1332_, v_prec_1295_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1317_ = v___x_1334_;
goto v___jp_1316_;
}
else
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1317_ = v___x_1335_;
goto v___jp_1316_;
}
v___jp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1318_ = lean_box(1);
v___x_1319_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__7));
v___x_1320_ = lean_unsigned_to_nat(1024u);
v___x_1321_ = l_Lean_Name_reprPrec(v_n_1311_, v___x_1320_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set_tag(v___x_1314_, 5);
lean_ctor_set(v___x_1314_, 1, v___x_1321_);
lean_ctor_set(v___x_1314_, 0, v___x_1319_);
v___x_1323_ = v___x_1314_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v___x_1318_);
v___x_1325_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_fields_1312_);
v___x_1326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
lean_inc(v___y_1317_);
v___x_1327_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___y_1317_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = 0;
v___x_1329_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1329_, 0, v___x_1327_);
lean_ctor_set_uint8(v___x_1329_, sizeof(void*)*1, v___x_1328_);
v___x_1330_ = l_Repr_addAppParen(v___x_1329_, v_prec_1295_);
return v___x_1330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object* v_x_1337_, lean_object* v_prec_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_Syntax_instReprPreresolved_repr(v_x_1337_, v_prec_1338_);
lean_dec(v_prec_1338_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object* v_a_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_nat_to_int(v_a_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object* v_a_1342_, lean_object* v_n_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_a_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object* v_a_1345_, lean_object* v_n_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(v_a_1345_, v_n_1346_);
lean_dec(v_n_1346_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = l_Lean_Syntax_instReprPreresolved_repr(v___y_1350_, v___x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_1353_, lean_object* v_x_1354_, lean_object* v_x_1355_){
_start:
{
if (lean_obj_tag(v_x_1355_) == 0)
{
lean_dec(v_x_1353_);
return v_x_1354_;
}
else
{
lean_object* v_head_1356_; lean_object* v_tail_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1368_; 
v_head_1356_ = lean_ctor_get(v_x_1355_, 0);
v_tail_1357_ = lean_ctor_get(v_x_1355_, 1);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_x_1355_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1359_ = v_x_1355_;
v_isShared_1360_ = v_isSharedCheck_1368_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_tail_1357_);
lean_inc(v_head_1356_);
lean_dec(v_x_1355_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1368_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
lean_inc(v_x_1353_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 5);
lean_ctor_set(v___x_1359_, 1, v_x_1353_);
lean_ctor_set(v___x_1359_, 0, v_x_1354_);
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_x_1354_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_x_1353_);
v___x_1362_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1356_, v___x_1363_);
v___x_1365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1362_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v_x_1354_ = v___x_1365_;
v_x_1355_ = v_tail_1357_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object* v_x_1369_, lean_object* v_x_1370_, lean_object* v_x_1371_){
_start:
{
if (lean_obj_tag(v_x_1371_) == 0)
{
lean_dec(v_x_1369_);
return v_x_1370_;
}
else
{
lean_object* v_head_1372_; lean_object* v_tail_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1384_; 
v_head_1372_ = lean_ctor_get(v_x_1371_, 0);
v_tail_1373_ = lean_ctor_get(v_x_1371_, 1);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_x_1371_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1375_ = v_x_1371_;
v_isShared_1376_ = v_isSharedCheck_1384_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_tail_1373_);
lean_inc(v_head_1372_);
lean_dec(v_x_1371_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1384_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
lean_inc(v_x_1369_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set_tag(v___x_1375_, 5);
lean_ctor_set(v___x_1375_, 1, v_x_1369_);
lean_ctor_set(v___x_1375_, 0, v_x_1370_);
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_x_1370_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_x_1369_);
v___x_1378_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1372_, v___x_1379_);
v___x_1381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1378_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(v_x_1369_, v___x_1381_, v_tail_1373_);
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object* v_x_1385_, lean_object* v_x_1386_){
_start:
{
if (lean_obj_tag(v_x_1385_) == 0)
{
lean_object* v___x_1387_; 
lean_dec(v_x_1386_);
v___x_1387_ = lean_box(0);
return v___x_1387_;
}
else
{
lean_object* v_tail_1388_; 
v_tail_1388_ = lean_ctor_get(v_x_1385_, 1);
if (lean_obj_tag(v_tail_1388_) == 0)
{
lean_object* v_head_1389_; lean_object* v___x_1390_; 
lean_dec(v_x_1386_);
v_head_1389_ = lean_ctor_get(v_x_1385_, 0);
lean_inc(v_head_1389_);
lean_dec_ref_known(v_x_1385_, 2);
v___x_1390_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1389_);
return v___x_1390_;
}
else
{
lean_object* v_head_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_inc(v_tail_1388_);
v_head_1391_ = lean_ctor_get(v_x_1385_, 0);
lean_inc(v_head_1391_);
lean_dec_ref_known(v_x_1385_, 2);
v___x_1392_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1391_);
v___x_1393_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(v_x_1386_, v___x_1392_, v_tail_1388_);
return v___x_1393_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object* v_a_1394_){
_start:
{
if (lean_obj_tag(v_a_1394_) == 0)
{
lean_object* v___x_1395_; 
v___x_1395_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1395_;
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; lean_object* v___x_1405_; 
v___x_1396_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1397_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(v_a_1394_, v___x_1396_);
v___x_1398_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1399_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1400_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
lean_ctor_set(v___x_1400_, 1, v___x_1397_);
v___x_1401_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1400_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1398_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = 0;
v___x_1405_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1405_, 0, v___x_1403_);
lean_ctor_set_uint8(v___x_1405_, sizeof(void*)*1, v___x_1404_);
return v___x_1405_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1415_, lean_object* v_x_1416_, lean_object* v_x_1417_){
_start:
{
if (lean_obj_tag(v_x_1417_) == 0)
{
lean_dec(v_x_1415_);
return v_x_1416_;
}
else
{
lean_object* v_head_1418_; lean_object* v_tail_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1430_; 
v_head_1418_ = lean_ctor_get(v_x_1417_, 0);
v_tail_1419_ = lean_ctor_get(v_x_1417_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_x_1417_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1421_ = v_x_1417_;
v_isShared_1422_ = v_isSharedCheck_1430_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_tail_1419_);
lean_inc(v_head_1418_);
lean_dec(v_x_1417_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1430_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
lean_inc(v_x_1415_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set_tag(v___x_1421_, 5);
lean_ctor_set(v___x_1421_, 1, v_x_1415_);
lean_ctor_set(v___x_1421_, 0, v_x_1416_);
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_x_1416_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_x_1415_);
v___x_1424_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = l_Lean_Syntax_instRepr_repr(v_head_1418_, v___x_1425_);
v___x_1427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1424_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v_x_1416_ = v___x_1427_;
v_x_1417_ = v_tail_1419_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object* v_x_1431_, lean_object* v_x_1432_, lean_object* v_x_1433_){
_start:
{
if (lean_obj_tag(v_x_1433_) == 0)
{
lean_dec(v_x_1431_);
return v_x_1432_;
}
else
{
lean_object* v_head_1434_; lean_object* v_tail_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1446_; 
v_head_1434_ = lean_ctor_get(v_x_1433_, 0);
v_tail_1435_ = lean_ctor_get(v_x_1433_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_x_1433_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1437_ = v_x_1433_;
v_isShared_1438_ = v_isSharedCheck_1446_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_tail_1435_);
lean_inc(v_head_1434_);
lean_dec(v_x_1433_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1446_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
lean_inc(v_x_1431_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set_tag(v___x_1437_, 5);
lean_ctor_set(v___x_1437_, 1, v_x_1431_);
lean_ctor_set(v___x_1437_, 0, v_x_1432_);
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_x_1432_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_x_1431_);
v___x_1440_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = l_Lean_Syntax_instRepr_repr(v_head_1434_, v___x_1441_);
v___x_1443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1440_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(v_x_1431_, v___x_1443_, v_tail_1435_);
return v___x_1444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object* v_x_1447_, lean_object* v_x_1448_){
_start:
{
if (lean_obj_tag(v_x_1447_) == 0)
{
lean_object* v___x_1449_; 
lean_dec(v_x_1448_);
v___x_1449_ = lean_box(0);
return v___x_1449_;
}
else
{
lean_object* v_tail_1450_; 
v_tail_1450_ = lean_ctor_get(v_x_1447_, 1);
if (lean_obj_tag(v_tail_1450_) == 0)
{
lean_object* v_head_1451_; lean_object* v___x_1452_; 
lean_dec(v_x_1448_);
v_head_1451_ = lean_ctor_get(v_x_1447_, 0);
lean_inc(v_head_1451_);
lean_dec_ref_known(v_x_1447_, 2);
v___x_1452_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1451_);
return v___x_1452_;
}
else
{
lean_object* v_head_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_inc(v_tail_1450_);
v_head_1453_ = lean_ctor_get(v_x_1447_, 0);
lean_inc(v_head_1453_);
lean_dec_ref_known(v_x_1447_, 2);
v___x_1454_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1453_);
v___x_1455_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(v_x_1448_, v___x_1454_, v_tail_1450_);
return v___x_1455_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0));
v___x_1458_ = lean_string_length(v___x_1457_);
return v___x_1458_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1);
v___x_1460_ = lean_nat_to_int(v___x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object* v_xs_1466_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = lean_array_get_size(v_xs_1466_);
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = lean_nat_dec_eq(v___x_1467_, v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1470_ = lean_array_to_list(v_xs_1466_);
v___x_1471_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1472_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(v___x_1470_, v___x_1471_);
v___x_1473_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2);
v___x_1474_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3));
v___x_1475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
lean_ctor_set(v___x_1475_, 1, v___x_1472_);
v___x_1476_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1473_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = l_Std_Format_fill(v___x_1478_);
return v___x_1479_;
}
else
{
lean_object* v___x_1480_; 
lean_dec_ref(v_xs_1466_);
v___x_1480_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5));
return v___x_1480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object* v_x_1494_, lean_object* v_prec_1495_){
_start:
{
lean_object* v___y_1497_; 
switch(lean_obj_tag(v_x_1494_))
{
case 0:
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = lean_unsigned_to_nat(1024u);
v___x_1504_ = lean_nat_dec_le(v___x_1503_, v_prec_1495_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1497_ = v___x_1505_;
goto v___jp_1496_;
}
else
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1497_ = v___x_1506_;
goto v___jp_1496_;
}
}
case 1:
{
lean_object* v_info_1507_; lean_object* v_kind_1508_; lean_object* v_args_1509_; lean_object* v___y_1511_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v_info_1507_ = lean_ctor_get(v_x_1494_, 0);
lean_inc(v_info_1507_);
v_kind_1508_ = lean_ctor_get(v_x_1494_, 1);
lean_inc(v_kind_1508_);
v_args_1509_ = lean_ctor_get(v_x_1494_, 2);
lean_inc_ref(v_args_1509_);
lean_dec_ref_known(v_x_1494_, 3);
v___x_1527_ = lean_unsigned_to_nat(1024u);
v___x_1528_ = lean_nat_dec_le(v___x_1527_, v_prec_1495_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1511_ = v___x_1529_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1511_ = v___x_1530_;
goto v___jp_1510_;
}
v___jp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1512_ = lean_box(1);
v___x_1513_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__4));
v___x_1514_ = lean_unsigned_to_nat(1024u);
v___x_1515_ = l_instReprSourceInfo_repr(v_info_1507_, v___x_1514_);
v___x_1516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1513_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v___x_1512_);
v___x_1518_ = l_Lean_Name_reprPrec(v_kind_1508_, v___x_1514_);
v___x_1519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
lean_ctor_set(v___x_1520_, 1, v___x_1512_);
v___x_1521_ = l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(v_args_1509_);
v___x_1522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1520_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
lean_inc(v___y_1511_);
v___x_1523_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___y_1511_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = 0;
v___x_1525_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*1, v___x_1524_);
v___x_1526_ = l_Repr_addAppParen(v___x_1525_, v_prec_1495_);
return v___x_1526_;
}
}
case 2:
{
lean_object* v_info_1531_; lean_object* v_val_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1557_; 
v_info_1531_ = lean_ctor_get(v_x_1494_, 0);
v_val_1532_ = lean_ctor_get(v_x_1494_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_x_1494_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1534_ = v_x_1494_;
v_isShared_1535_ = v_isSharedCheck_1557_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_val_1532_);
lean_inc(v_info_1531_);
lean_dec(v_x_1494_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1557_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___y_1537_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = lean_unsigned_to_nat(1024u);
v___x_1554_ = lean_nat_dec_le(v___x_1553_, v_prec_1495_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1537_ = v___x_1555_;
goto v___jp_1536_;
}
else
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1537_ = v___x_1556_;
goto v___jp_1536_;
}
v___jp_1536_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1538_ = lean_box(1);
v___x_1539_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__7));
v___x_1540_ = lean_unsigned_to_nat(1024u);
v___x_1541_ = l_instReprSourceInfo_repr(v_info_1531_, v___x_1540_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 5);
lean_ctor_set(v___x_1534_, 1, v___x_1541_);
lean_ctor_set(v___x_1534_, 0, v___x_1539_);
v___x_1543_ = v___x_1534_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v___x_1538_);
v___x_1545_ = l_String_quote(v_val_1532_);
v___x_1546_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
v___x_1547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1544_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
lean_inc(v___y_1537_);
v___x_1548_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___y_1537_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = 0;
v___x_1550_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*1, v___x_1549_);
v___x_1551_ = l_Repr_addAppParen(v___x_1550_, v_prec_1495_);
return v___x_1551_;
}
}
}
}
default: 
{
lean_object* v_info_1558_; lean_object* v_rawVal_1559_; lean_object* v_val_1560_; lean_object* v_preresolved_1561_; lean_object* v___y_1563_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v_info_1558_ = lean_ctor_get(v_x_1494_, 0);
lean_inc(v_info_1558_);
v_rawVal_1559_ = lean_ctor_get(v_x_1494_, 1);
lean_inc_ref(v_rawVal_1559_);
v_val_1560_ = lean_ctor_get(v_x_1494_, 2);
lean_inc(v_val_1560_);
v_preresolved_1561_ = lean_ctor_get(v_x_1494_, 3);
lean_inc(v_preresolved_1561_);
lean_dec_ref_known(v_x_1494_, 4);
v___x_1586_ = lean_unsigned_to_nat(1024u);
v___x_1587_ = lean_nat_dec_le(v___x_1586_, v_prec_1495_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1563_ = v___x_1588_;
goto v___jp_1562_;
}
else
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1563_ = v___x_1589_;
goto v___jp_1562_;
}
v___jp_1562_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1564_ = lean_box(1);
v___x_1565_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__10));
v___x_1566_ = lean_unsigned_to_nat(1024u);
v___x_1567_ = l_instReprSourceInfo_repr(v_info_1558_, v___x_1566_);
v___x_1568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1565_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_ctor_set(v___x_1569_, 1, v___x_1564_);
v___x_1570_ = lean_substring_tostring(v_rawVal_1559_);
v___x_1571_ = l_String_quote(v___x_1570_);
v___x_1572_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__11));
v___x_1573_ = lean_string_append(v___x_1571_, v___x_1572_);
v___x_1574_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1569_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
lean_ctor_set(v___x_1576_, 1, v___x_1564_);
v___x_1577_ = l_Lean_Name_reprPrec(v_val_1560_, v___x_1566_);
v___x_1578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v___x_1564_);
v___x_1580_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_preresolved_1561_);
v___x_1581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
lean_inc(v___y_1563_);
v___x_1582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___y_1563_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = 0;
v___x_1584_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set_uint8(v___x_1584_, sizeof(void*)*1, v___x_1583_);
v___x_1585_ = l_Repr_addAppParen(v___x_1584_, v_prec_1495_);
return v___x_1585_;
}
}
}
v___jp_1496_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1498_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__1));
lean_inc(v___y_1497_);
v___x_1499_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___y_1497_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v___x_1500_ = 0;
v___x_1501_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1501_, 0, v___x_1499_);
lean_ctor_set_uint8(v___x_1501_, sizeof(void*)*1, v___x_1500_);
v___x_1502_ = l_Repr_addAppParen(v___x_1501_, v_prec_1495_);
return v___x_1502_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = l_Lean_Syntax_instRepr_repr(v___y_1590_, v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object* v_x_1593_, lean_object* v_prec_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Syntax_instRepr_repr(v_x_1593_, v_prec_1594_);
lean_dec(v_prec_1594_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object* v_a_1596_, lean_object* v_n_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_a_1596_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object* v_a_1599_, lean_object* v_n_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(v_a_1599_, v_n_1600_);
lean_dec(v_n_1600_);
return v_res_1601_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_unsigned_to_nat(7u);
v___x_1618_ = lean_nat_to_int(v___x_1617_);
return v___x_1618_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0));
v___x_1621_ = lean_string_length(v___x_1620_);
return v___x_1621_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9);
v___x_1623_ = lean_nat_to_int(v___x_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object* v_x_1628_){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1629_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6));
v___x_1630_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = l_Lean_Syntax_instRepr_repr(v_x_1628_, v___x_1631_);
v___x_1633_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1630_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = 0;
v___x_1635_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set_uint8(v___x_1635_, sizeof(void*)*1, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1629_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_1638_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_1639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v___x_1636_);
v___x_1640_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_1641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1637_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*1, v___x_1634_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object* v_ks_1644_, lean_object* v_x_1645_, lean_object* v_prec_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_x_1645_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object* v_ks_1648_, lean_object* v_x_1649_, lean_object* v_prec_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_Syntax_instReprTSyntax_repr(v_ks_1648_, v_x_1649_, v_prec_1650_);
lean_dec(v_prec_1650_);
lean_dec(v_ks_1648_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object* v_ks_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_alloc_closure((void*)(l_Lean_Syntax_instReprTSyntax_repr___boxed), 3, 1);
lean_closure_set(v___x_1653_, 0, v_ks_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_stx_1654_){
_start:
{
lean_inc(v_stx_1654_);
return v_stx_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0___boxed(lean_object* v_stx_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___lam__0(v_stx_1655_);
lean_dec(v_stx_1655_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg(){
_start:
{
lean_object* v___f_1659_; 
v___f_1659_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___boxed(lean_object* v___dummy_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg();
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object* v_k_1662_, lean_object* v_ks_1663_){
_start:
{
lean_object* v___f_1664_; 
v___f_1664_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object* v_k_1665_, lean_object* v_ks_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(v_k_1665_, v_ks_1666_);
lean_dec(v_ks_1666_);
lean_dec(v_k_1665_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg(){
_start:
{
lean_object* v___f_1669_; 
v___f_1669_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg___boxed(lean_object* v___dummy_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind___redArg();
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object* v_ks_1672_, lean_object* v_k_x27_1673_){
_start:
{
lean_object* v___f_1674_; 
v___f_1674_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___redArg___closed__0));
return v___f_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object* v_ks_1675_, lean_object* v_k_x27_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind(v_ks_1675_, v_k_x27_1676_);
lean_dec(v_k_x27_1676_);
lean_dec(v_ks_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object* v_s_1678_){
_start:
{
lean_inc(v_s_1678_);
return v_s_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object* v_s_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_TSyntax_instCoeIdentTerm___lam__0(v_s_1679_);
lean_dec(v_s_1679_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object* v_info_1683_, lean_object* v_ss_1684_, lean_object* v_n_1685_, lean_object* v_res_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1687_, 0, v_info_1683_);
lean_ctor_set(v___x_1687_, 1, v_ss_1684_);
lean_ctor_set(v___x_1687_, 2, v_n_1685_);
lean_ctor_set(v___x_1687_, 3, v_res_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg(){
_start:
{
lean_object* v___f_1697_; 
v___f_1697_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg___boxed(lean_object* v___dummy_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_TSyntax_Compat_instCoeTailSyntax___redArg();
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object* v_k_1700_){
_start:
{
lean_object* v___f_1701_; 
v___f_1701_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object* v_k_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_TSyntax_Compat_instCoeTailSyntax(v_k_1702_);
lean_dec(v_k_1702_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object* v_k_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_alloc_closure((void*)(l_Lean_TSyntaxArray_mkImpl___boxed), 2, 1);
lean_closure_set(v___x_1705_, 0, v_k_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object* v_x_1706_, lean_object* v_x_1707_){
_start:
{
if (lean_obj_tag(v_x_1706_) == 0)
{
if (lean_obj_tag(v_x_1707_) == 0)
{
uint8_t v___x_1708_; 
v___x_1708_ = 1;
return v___x_1708_;
}
else
{
uint8_t v___x_1709_; 
v___x_1709_ = 0;
return v___x_1709_;
}
}
else
{
if (lean_obj_tag(v_x_1707_) == 0)
{
uint8_t v___x_1710_; 
v___x_1710_ = 0;
return v___x_1710_;
}
else
{
lean_object* v_head_1711_; lean_object* v_tail_1712_; lean_object* v_head_1713_; lean_object* v_tail_1714_; uint8_t v___x_1715_; 
v_head_1711_ = lean_ctor_get(v_x_1706_, 0);
v_tail_1712_ = lean_ctor_get(v_x_1706_, 1);
v_head_1713_ = lean_ctor_get(v_x_1707_, 0);
v_tail_1714_ = lean_ctor_get(v_x_1707_, 1);
v___x_1715_ = lean_string_dec_eq(v_head_1711_, v_head_1713_);
if (v___x_1715_ == 0)
{
return v___x_1715_;
}
else
{
v_x_1706_ = v_tail_1712_;
v_x_1707_ = v_tail_1714_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object* v_x_1717_, lean_object* v_x_1718_){
_start:
{
uint8_t v_res_1719_; lean_object* v_r_1720_; 
v_res_1719_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_x_1717_, v_x_1718_);
lean_dec(v_x_1718_);
lean_dec(v_x_1717_);
v_r_1720_ = lean_box(v_res_1719_);
return v_r_1720_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object* v_x_1721_, lean_object* v_x_1722_){
_start:
{
if (lean_obj_tag(v_x_1721_) == 0)
{
if (lean_obj_tag(v_x_1722_) == 0)
{
lean_object* v_ns_1723_; lean_object* v_ns_1724_; uint8_t v___x_1725_; 
v_ns_1723_ = lean_ctor_get(v_x_1721_, 0);
v_ns_1724_ = lean_ctor_get(v_x_1722_, 0);
v___x_1725_ = lean_name_eq(v_ns_1723_, v_ns_1724_);
return v___x_1725_;
}
else
{
uint8_t v___x_1726_; 
v___x_1726_ = 0;
return v___x_1726_;
}
}
else
{
if (lean_obj_tag(v_x_1722_) == 1)
{
lean_object* v_n_1727_; lean_object* v_fields_1728_; lean_object* v_n_1729_; lean_object* v_fields_1730_; uint8_t v___x_1731_; 
v_n_1727_ = lean_ctor_get(v_x_1721_, 0);
v_fields_1728_ = lean_ctor_get(v_x_1721_, 1);
v_n_1729_ = lean_ctor_get(v_x_1722_, 0);
v_fields_1730_ = lean_ctor_get(v_x_1722_, 1);
v___x_1731_ = lean_name_eq(v_n_1727_, v_n_1729_);
if (v___x_1731_ == 0)
{
return v___x_1731_;
}
else
{
uint8_t v___x_1732_; 
v___x_1732_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_fields_1728_, v_fields_1730_);
return v___x_1732_;
}
}
else
{
uint8_t v___x_1733_; 
v___x_1733_ = 0;
return v___x_1733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object* v_x_1734_, lean_object* v_x_1735_){
_start:
{
uint8_t v_res_1736_; lean_object* v_r_1737_; 
v_res_1736_ = l_Lean_Syntax_instBEqPreresolved_beq(v_x_1734_, v_x_1735_);
lean_dec_ref(v_x_1735_);
lean_dec_ref(v_x_1734_);
v_r_1737_ = lean_box(v_res_1736_);
return v_r_1737_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object* v_x_1740_, lean_object* v_x_1741_){
_start:
{
if (lean_obj_tag(v_x_1740_) == 0)
{
if (lean_obj_tag(v_x_1741_) == 0)
{
uint8_t v___x_1742_; 
v___x_1742_ = 1;
return v___x_1742_;
}
else
{
uint8_t v___x_1743_; 
v___x_1743_ = 0;
return v___x_1743_;
}
}
else
{
if (lean_obj_tag(v_x_1741_) == 0)
{
uint8_t v___x_1744_; 
v___x_1744_ = 0;
return v___x_1744_;
}
else
{
lean_object* v_head_1745_; lean_object* v_tail_1746_; lean_object* v_head_1747_; lean_object* v_tail_1748_; uint8_t v___x_1749_; 
v_head_1745_ = lean_ctor_get(v_x_1740_, 0);
v_tail_1746_ = lean_ctor_get(v_x_1740_, 1);
v_head_1747_ = lean_ctor_get(v_x_1741_, 0);
v_tail_1748_ = lean_ctor_get(v_x_1741_, 1);
v___x_1749_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_1745_, v_head_1747_);
if (v___x_1749_ == 0)
{
return v___x_1749_;
}
else
{
v_x_1740_ = v_tail_1746_;
v_x_1741_ = v_tail_1748_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
uint8_t v_res_1753_; lean_object* v_r_1754_; 
v_res_1753_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_x_1751_, v_x_1752_);
lean_dec(v_x_1752_);
lean_dec(v_x_1751_);
v_r_1754_ = lean_box(v_res_1753_);
return v_r_1754_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structEq(lean_object* v_x_1755_, lean_object* v_x_1756_){
_start:
{
switch(lean_obj_tag(v_x_1755_))
{
case 0:
{
if (lean_obj_tag(v_x_1756_) == 0)
{
uint8_t v___x_1757_; 
v___x_1757_ = 1;
return v___x_1757_;
}
else
{
uint8_t v___x_1758_; 
v___x_1758_ = 0;
return v___x_1758_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1756_) == 1)
{
lean_object* v_kind_1759_; lean_object* v_args_1760_; lean_object* v_kind_1761_; lean_object* v_args_1762_; uint8_t v___x_1763_; 
v_kind_1759_ = lean_ctor_get(v_x_1755_, 1);
v_args_1760_ = lean_ctor_get(v_x_1755_, 2);
v_kind_1761_ = lean_ctor_get(v_x_1756_, 1);
v_args_1762_ = lean_ctor_get(v_x_1756_, 2);
v___x_1763_ = lean_name_eq(v_kind_1759_, v_kind_1761_);
if (v___x_1763_ == 0)
{
return v___x_1763_;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1764_ = lean_array_get_size(v_args_1760_);
v___x_1765_ = lean_array_get_size(v_args_1762_);
v___x_1766_ = lean_nat_dec_eq(v___x_1764_, v___x_1765_);
if (v___x_1766_ == 0)
{
return v___x_1766_;
}
else
{
uint8_t v___x_1767_; 
v___x_1767_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_args_1760_, v_args_1762_, v___x_1764_);
return v___x_1767_;
}
}
}
else
{
uint8_t v___x_1768_; 
v___x_1768_ = 0;
return v___x_1768_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1756_) == 2)
{
lean_object* v_val_1769_; lean_object* v_val_1770_; uint8_t v___x_1771_; 
v_val_1769_ = lean_ctor_get(v_x_1755_, 1);
v_val_1770_ = lean_ctor_get(v_x_1756_, 1);
v___x_1771_ = lean_string_dec_eq(v_val_1769_, v_val_1770_);
return v___x_1771_;
}
else
{
uint8_t v___x_1772_; 
v___x_1772_ = 0;
return v___x_1772_;
}
}
default: 
{
if (lean_obj_tag(v_x_1756_) == 3)
{
lean_object* v_rawVal_1773_; lean_object* v_val_1774_; lean_object* v_preresolved_1775_; lean_object* v_rawVal_1776_; lean_object* v_val_1777_; lean_object* v_preresolved_1778_; uint8_t v___x_1779_; 
v_rawVal_1773_ = lean_ctor_get(v_x_1755_, 1);
v_val_1774_ = lean_ctor_get(v_x_1755_, 2);
v_preresolved_1775_ = lean_ctor_get(v_x_1755_, 3);
v_rawVal_1776_ = lean_ctor_get(v_x_1756_, 1);
v_val_1777_ = lean_ctor_get(v_x_1756_, 2);
v_preresolved_1778_ = lean_ctor_get(v_x_1756_, 3);
lean_inc_ref(v_rawVal_1776_);
lean_inc_ref(v_rawVal_1773_);
v___x_1779_ = lean_substring_beq(v_rawVal_1773_, v_rawVal_1776_);
if (v___x_1779_ == 0)
{
return v___x_1779_;
}
else
{
uint8_t v___x_1780_; 
v___x_1780_ = lean_name_eq(v_val_1774_, v_val_1777_);
if (v___x_1780_ == 0)
{
return v___x_1780_;
}
else
{
uint8_t v___x_1781_; 
v___x_1781_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_preresolved_1775_, v_preresolved_1778_);
return v___x_1781_;
}
}
}
else
{
uint8_t v___x_1782_; 
v___x_1782_ = 0;
return v___x_1782_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object* v_xs_1783_, lean_object* v_ys_1784_, lean_object* v_x_1785_){
_start:
{
lean_object* v_zero_1786_; uint8_t v_isZero_1787_; 
v_zero_1786_ = lean_unsigned_to_nat(0u);
v_isZero_1787_ = lean_nat_dec_eq(v_x_1785_, v_zero_1786_);
if (v_isZero_1787_ == 1)
{
lean_dec(v_x_1785_);
return v_isZero_1787_;
}
else
{
lean_object* v_one_1788_; lean_object* v_n_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v_one_1788_ = lean_unsigned_to_nat(1u);
v_n_1789_ = lean_nat_sub(v_x_1785_, v_one_1788_);
lean_dec(v_x_1785_);
v___x_1790_ = lean_array_fget_borrowed(v_xs_1783_, v_n_1789_);
v___x_1791_ = lean_array_fget_borrowed(v_ys_1784_, v_n_1789_);
v___x_1792_ = l_Lean_Syntax_structEq(v___x_1790_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_dec(v_n_1789_);
return v___x_1792_;
}
else
{
v_x_1785_ = v_n_1789_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object* v_xs_1794_, lean_object* v_ys_1795_, lean_object* v_x_1796_){
_start:
{
uint8_t v_res_1797_; lean_object* v_r_1798_; 
v_res_1797_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1794_, v_ys_1795_, v_x_1796_);
lean_dec_ref(v_ys_1795_);
lean_dec_ref(v_xs_1794_);
v_r_1798_ = lean_box(v_res_1797_);
return v_r_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object* v_x_1799_, lean_object* v_x_1800_){
_start:
{
uint8_t v_res_1801_; lean_object* v_r_1802_; 
v_res_1801_ = l_Lean_Syntax_structEq(v_x_1799_, v_x_1800_);
lean_dec(v_x_1800_);
lean_dec(v_x_1799_);
v_r_1802_ = lean_box(v_res_1801_);
return v_r_1802_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object* v_xs_1803_, lean_object* v_ys_1804_, lean_object* v_hsz_1805_, lean_object* v_x_1806_, lean_object* v_x_1807_){
_start:
{
uint8_t v___x_1808_; 
v___x_1808_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1803_, v_ys_1804_, v_x_1806_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object* v_xs_1809_, lean_object* v_ys_1810_, lean_object* v_hsz_1811_, lean_object* v_x_1812_, lean_object* v_x_1813_){
_start:
{
uint8_t v_res_1814_; lean_object* v_r_1815_; 
v_res_1814_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(v_xs_1809_, v_ys_1810_, v_hsz_1811_, v_x_1812_, v_x_1813_);
lean_dec_ref(v_ys_1810_);
lean_dec_ref(v_xs_1809_);
v_r_1815_ = lean_box(v_res_1814_);
return v_r_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg(){
_start:
{
lean_object* v___f_1820_; 
v___f_1820_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___redArg___closed__0));
return v___f_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___redArg___boxed(lean_object* v___dummy_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Syntax_instBEqTSyntax___redArg();
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object* v_k_1823_){
_start:
{
lean_object* v___f_1824_; 
v___f_1824_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___redArg___closed__0));
return v___f_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object* v_k_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Syntax_instBEqTSyntax(v_k_1825_);
lean_dec(v_k_1825_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object* v_as_1827_, lean_object* v_i_1828_){
_start:
{
lean_object* v_zero_1829_; uint8_t v_isZero_1830_; 
v_zero_1829_ = lean_unsigned_to_nat(0u);
v_isZero_1830_ = lean_nat_dec_eq(v_i_1828_, v_zero_1829_);
if (v_isZero_1830_ == 1)
{
lean_object* v___x_1831_; 
lean_dec(v_i_1828_);
v___x_1831_ = lean_box(0);
return v___x_1831_;
}
else
{
lean_object* v_one_1832_; lean_object* v_n_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_one_1832_ = lean_unsigned_to_nat(1u);
v_n_1833_ = lean_nat_sub(v_i_1828_, v_one_1832_);
lean_dec(v_i_1828_);
v___x_1834_ = lean_array_fget_borrowed(v_as_1827_, v_n_1833_);
v___x_1835_ = l_Lean_Syntax_getTailInfo_x3f(v___x_1834_);
if (lean_obj_tag(v___x_1835_) == 0)
{
v_i_1828_ = v_n_1833_;
goto _start;
}
else
{
lean_dec(v_n_1833_);
return v___x_1835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object* v_x_1837_){
_start:
{
switch(lean_obj_tag(v_x_1837_))
{
case 2:
{
lean_object* v_info_1838_; lean_object* v___x_1839_; 
v_info_1838_ = lean_ctor_get(v_x_1837_, 0);
lean_inc(v_info_1838_);
v___x_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1839_, 0, v_info_1838_);
return v___x_1839_;
}
case 3:
{
lean_object* v_info_1840_; lean_object* v___x_1841_; 
v_info_1840_ = lean_ctor_get(v_x_1837_, 0);
lean_inc(v_info_1840_);
v___x_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_info_1840_);
return v___x_1841_;
}
case 1:
{
lean_object* v_info_1842_; 
v_info_1842_ = lean_ctor_get(v_x_1837_, 0);
if (lean_obj_tag(v_info_1842_) == 2)
{
lean_object* v_args_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v_args_1843_ = lean_ctor_get(v_x_1837_, 2);
v___x_1844_ = lean_array_get_size(v_args_1843_);
v___x_1845_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_args_1843_, v___x_1844_);
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; 
lean_inc(v_info_1842_);
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v_info_1842_);
return v___x_1846_;
}
}
default: 
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_box(0);
return v___x_1847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object* v_x_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_Syntax_getTailInfo_x3f(v_x_1848_);
lean_dec(v_x_1848_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object* v_as_1850_, lean_object* v_i_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1850_, v_i_1851_);
lean_dec_ref(v_as_1850_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object* v_as_1853_, lean_object* v_i_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1853_, v_i_1854_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object* v_as_1857_, lean_object* v_i_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(v_as_1857_, v_i_1858_, v_a_1859_);
lean_dec_ref(v_as_1857_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object* v_stx_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1861_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_box(2);
return v___x_1863_;
}
else
{
lean_object* v_val_1864_; 
v_val_1864_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_val_1864_);
lean_dec_ref_known(v___x_1862_, 1);
return v_val_1864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object* v_stx_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_Syntax_getTailInfo(v_stx_1865_);
lean_dec(v_stx_1865_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object* v_stx_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1867_);
if (lean_obj_tag(v___x_1868_) == 1)
{
lean_object* v_val_1869_; 
v_val_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_val_1869_);
lean_dec_ref_known(v___x_1868_, 1);
if (lean_obj_tag(v_val_1869_) == 0)
{
lean_object* v_trailing_1870_; lean_object* v_startPos_1871_; lean_object* v_stopPos_1872_; lean_object* v___x_1873_; 
v_trailing_1870_ = lean_ctor_get(v_val_1869_, 2);
lean_inc_ref(v_trailing_1870_);
lean_dec_ref_known(v_val_1869_, 4);
v_startPos_1871_ = lean_ctor_get(v_trailing_1870_, 1);
lean_inc(v_startPos_1871_);
v_stopPos_1872_ = lean_ctor_get(v_trailing_1870_, 2);
lean_inc(v_stopPos_1872_);
lean_dec_ref(v_trailing_1870_);
v___x_1873_ = lean_nat_sub(v_stopPos_1872_, v_startPos_1871_);
lean_dec(v_startPos_1871_);
lean_dec(v_stopPos_1872_);
return v___x_1873_;
}
else
{
lean_object* v___x_1874_; 
lean_dec(v_val_1869_);
v___x_1874_ = lean_unsigned_to_nat(0u);
return v___x_1874_;
}
}
else
{
lean_object* v___x_1875_; 
lean_dec(v___x_1868_);
v___x_1875_ = lean_unsigned_to_nat(0u);
return v___x_1875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object* v_stx_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_Syntax_getTrailingSize(v_stx_1876_);
lean_dec(v_stx_1876_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object* v_stx_1878_){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = l_Lean_Syntax_getTailInfo(v_stx_1878_);
v___x_1880_ = l_Lean_SourceInfo_getTrailing_x3f(v___x_1879_);
lean_dec(v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object* v_stx_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Syntax_getTrailing_x3f(v_stx_1881_);
lean_dec(v_stx_1881_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object* v_stx_1883_, uint8_t v_canonicalOnly_1884_){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = l_Lean_Syntax_getTailInfo(v_stx_1883_);
v___x_1886_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v___x_1885_, v_canonicalOnly_1884_);
lean_dec(v___x_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object* v_stx_1887_, lean_object* v_canonicalOnly_1888_){
_start:
{
uint8_t v_canonicalOnly_boxed_1889_; lean_object* v_res_1890_; 
v_canonicalOnly_boxed_1889_ = lean_unbox(v_canonicalOnly_1888_);
v_res_1890_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1887_, v_canonicalOnly_boxed_1889_);
lean_dec(v_stx_1887_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object* v_stx_1891_, uint8_t v_withLeading_1892_, uint8_t v_withTrailing_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_Syntax_getHeadInfo(v_stx_1891_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_leading_1895_; lean_object* v_pos_1896_; lean_object* v___x_1897_; 
v_leading_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc_ref(v_leading_1895_);
v_pos_1896_ = lean_ctor_get(v___x_1894_, 1);
lean_inc(v_pos_1896_);
lean_dec_ref_known(v___x_1894_, 4);
v___x_1897_ = l_Lean_Syntax_getTailInfo(v_stx_1891_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_trailing_1898_; lean_object* v_endPos_1899_; lean_object* v_str_1900_; lean_object* v_startPos_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1915_; 
v_trailing_1898_ = lean_ctor_get(v___x_1897_, 2);
lean_inc_ref(v_trailing_1898_);
v_endPos_1899_ = lean_ctor_get(v___x_1897_, 3);
lean_inc(v_endPos_1899_);
lean_dec_ref_known(v___x_1897_, 4);
v_str_1900_ = lean_ctor_get(v_leading_1895_, 0);
v_startPos_1901_ = lean_ctor_get(v_leading_1895_, 1);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_leading_1895_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v_leading_1895_, 2);
lean_dec(v_unused_1916_);
v___x_1903_ = v_leading_1895_;
v_isShared_1904_ = v_isSharedCheck_1915_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_startPos_1901_);
lean_inc(v_str_1900_);
lean_dec(v_leading_1895_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1915_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1913_; 
if (v_withLeading_1892_ == 0)
{
lean_dec(v_startPos_1901_);
v___y_1913_ = v_pos_1896_;
goto v___jp_1912_;
}
else
{
lean_dec(v_pos_1896_);
v___y_1913_ = v_startPos_1901_;
goto v___jp_1912_;
}
v___jp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 2, v___y_1907_);
lean_ctor_set(v___x_1903_, 1, v___y_1906_);
v___x_1909_ = v___x_1903_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_str_1900_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v___y_1906_);
lean_ctor_set(v_reuseFailAlloc_1911_, 2, v___y_1907_);
v___x_1909_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
return v___x_1910_;
}
}
v___jp_1912_:
{
if (v_withTrailing_1893_ == 0)
{
lean_dec_ref(v_trailing_1898_);
v___y_1906_ = v___y_1913_;
v___y_1907_ = v_endPos_1899_;
goto v___jp_1905_;
}
else
{
lean_object* v_stopPos_1914_; 
lean_dec(v_endPos_1899_);
v_stopPos_1914_ = lean_ctor_get(v_trailing_1898_, 2);
lean_inc(v_stopPos_1914_);
lean_dec_ref(v_trailing_1898_);
v___y_1906_ = v___y_1913_;
v___y_1907_ = v_stopPos_1914_;
goto v___jp_1905_;
}
}
}
}
else
{
lean_object* v___x_1917_; 
lean_dec(v___x_1897_);
lean_dec(v_pos_1896_);
lean_dec_ref(v_leading_1895_);
v___x_1917_ = lean_box(0);
return v___x_1917_;
}
}
else
{
lean_object* v___x_1918_; 
lean_dec(v___x_1894_);
v___x_1918_ = lean_box(0);
return v___x_1918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object* v_stx_1919_, lean_object* v_withLeading_1920_, lean_object* v_withTrailing_1921_){
_start:
{
uint8_t v_withLeading_boxed_1922_; uint8_t v_withTrailing_boxed_1923_; lean_object* v_res_1924_; 
v_withLeading_boxed_1922_ = lean_unbox(v_withLeading_1920_);
v_withTrailing_boxed_1923_ = lean_unbox(v_withTrailing_1921_);
v_res_1924_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1919_, v_withLeading_boxed_1922_, v_withTrailing_boxed_1923_);
lean_dec(v_stx_1919_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object* v_a_1925_, lean_object* v_f_1926_, lean_object* v_i_1927_){
_start:
{
lean_object* v_zero_1928_; uint8_t v_isZero_1929_; 
v_zero_1928_ = lean_unsigned_to_nat(0u);
v_isZero_1929_ = lean_nat_dec_eq(v_i_1927_, v_zero_1928_);
if (v_isZero_1929_ == 1)
{
lean_object* v___x_1930_; 
lean_dec(v_i_1927_);
lean_dec_ref(v_f_1926_);
lean_dec_ref(v_a_1925_);
v___x_1930_ = lean_box(0);
return v___x_1930_;
}
else
{
lean_object* v_one_1931_; lean_object* v_n_1932_; lean_object* v_v_1933_; lean_object* v___x_1934_; 
v_one_1931_ = lean_unsigned_to_nat(1u);
v_n_1932_ = lean_nat_sub(v_i_1927_, v_one_1931_);
lean_dec(v_i_1927_);
v_v_1933_ = lean_array_fget_borrowed(v_a_1925_, v_n_1932_);
lean_inc_ref(v_f_1926_);
lean_inc(v_v_1933_);
v___x_1934_ = lean_apply_1(v_f_1926_, v_v_1933_);
if (lean_obj_tag(v___x_1934_) == 0)
{
v_i_1927_ = v_n_1932_;
goto _start;
}
else
{
lean_object* v_val_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v_f_1926_);
v_val_1936_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1938_ = v___x_1934_;
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_val_1936_);
lean_dec(v___x_1934_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_array_fset(v_a_1925_, v_n_1932_, v_val_1936_);
lean_dec(v_n_1932_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1940_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object* v_00_u03b1_1945_, lean_object* v_a_1946_, lean_object* v_f_1947_, lean_object* v_i_1948_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(v_a_1946_, v_f_1947_, v_i_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* v_info_1950_, lean_object* v_x_1951_){
_start:
{
switch(lean_obj_tag(v_x_1951_))
{
case 2:
{
lean_object* v_val_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1960_; 
v_val_1952_ = lean_ctor_get(v_x_1951_, 1);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_x_1951_);
if (v_isSharedCheck_1960_ == 0)
{
lean_object* v_unused_1961_; 
v_unused_1961_ = lean_ctor_get(v_x_1951_, 0);
lean_dec(v_unused_1961_);
v___x_1954_ = v_x_1951_;
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_val_1952_);
lean_dec(v_x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v_info_1950_);
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_info_1950_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_val_1952_);
v___x_1957_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
return v___x_1958_;
}
}
}
case 3:
{
lean_object* v_rawVal_1962_; lean_object* v_val_1963_; lean_object* v_preresolved_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v_rawVal_1962_ = lean_ctor_get(v_x_1951_, 1);
v_val_1963_ = lean_ctor_get(v_x_1951_, 2);
v_preresolved_1964_ = lean_ctor_get(v_x_1951_, 3);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_x_1951_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v_x_1951_, 0);
lean_dec(v_unused_1973_);
v___x_1966_ = v_x_1951_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_preresolved_1964_);
lean_inc(v_val_1963_);
lean_inc(v_rawVal_1962_);
lean_dec(v_x_1951_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v_info_1950_);
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_info_1950_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_rawVal_1962_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_val_1963_);
lean_ctor_set(v_reuseFailAlloc_1971_, 3, v_preresolved_1964_);
v___x_1969_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1970_; 
v___x_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
return v___x_1970_;
}
}
}
case 1:
{
lean_object* v_info_1974_; lean_object* v_kind_1975_; lean_object* v_args_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1994_; 
v_info_1974_ = lean_ctor_get(v_x_1951_, 0);
v_kind_1975_ = lean_ctor_get(v_x_1951_, 1);
v_args_1976_ = lean_ctor_get(v_x_1951_, 2);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_x_1951_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1978_ = v_x_1951_;
v_isShared_1979_ = v_isSharedCheck_1994_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_args_1976_);
lean_inc(v_kind_1975_);
lean_inc(v_info_1974_);
lean_dec(v_x_1951_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1994_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = lean_array_get_size(v_args_1976_);
v___x_1981_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(v_info_1950_, v_args_1976_, v___x_1980_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v___x_1982_; 
lean_del_object(v___x_1978_);
lean_dec(v_kind_1975_);
lean_dec(v_info_1974_);
v___x_1982_ = lean_box(0);
return v___x_1982_;
}
else
{
lean_object* v_val_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1993_; 
v_val_1983_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1985_ = v___x_1981_;
v_isShared_1986_ = v_isSharedCheck_1993_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_val_1983_);
lean_dec(v___x_1981_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1993_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 2, v_val_1983_);
v___x_1988_ = v___x_1978_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_info_1974_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_kind_1975_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_val_1983_);
v___x_1988_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1990_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_1988_);
v___x_1990_ = v___x_1985_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1995_; 
lean_dec(v_x_1951_);
lean_dec(v_info_1950_);
v___x_1995_ = lean_box(0);
return v___x_1995_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object* v_info_1996_, lean_object* v_a_1997_, lean_object* v_i_1998_){
_start:
{
lean_object* v_zero_1999_; uint8_t v_isZero_2000_; 
v_zero_1999_ = lean_unsigned_to_nat(0u);
v_isZero_2000_ = lean_nat_dec_eq(v_i_1998_, v_zero_1999_);
if (v_isZero_2000_ == 1)
{
lean_object* v___x_2001_; 
lean_dec(v_i_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_info_1996_);
v___x_2001_ = lean_box(0);
return v___x_2001_;
}
else
{
lean_object* v_one_2002_; lean_object* v_n_2003_; lean_object* v_v_2004_; lean_object* v___x_2005_; 
v_one_2002_ = lean_unsigned_to_nat(1u);
v_n_2003_ = lean_nat_sub(v_i_1998_, v_one_2002_);
lean_dec(v_i_1998_);
v_v_2004_ = lean_array_fget_borrowed(v_a_1997_, v_n_2003_);
lean_inc(v_v_2004_);
lean_inc(v_info_1996_);
v___x_2005_ = l_Lean_Syntax_setTailInfoAux(v_info_1996_, v_v_2004_);
if (lean_obj_tag(v___x_2005_) == 0)
{
v_i_1998_ = v_n_2003_;
goto _start;
}
else
{
lean_object* v_val_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_info_1996_);
v_val_2007_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2009_ = v___x_2005_;
v_isShared_2010_ = v_isSharedCheck_2015_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_val_2007_);
lean_dec(v___x_2005_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2015_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2011_ = lean_array_fset(v_a_1997_, v_n_2003_, v_val_2007_);
lean_dec(v_n_2003_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2011_);
v___x_2013_ = v___x_2009_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object* v_stx_2016_, lean_object* v_info_2017_){
_start:
{
lean_object* v___x_2018_; 
lean_inc(v_stx_2016_);
v___x_2018_ = l_Lean_Syntax_setTailInfoAux(v_info_2017_, v_stx_2016_);
if (lean_obj_tag(v___x_2018_) == 0)
{
return v_stx_2016_;
}
else
{
lean_object* v_val_2019_; 
lean_dec(v_stx_2016_);
v_val_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_val_2019_);
lean_dec_ref_known(v___x_2018_, 1);
return v_val_2019_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object* v_stx_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_Syntax_getTailInfo(v_stx_2020_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_trailing_2022_; lean_object* v_leading_2023_; lean_object* v_pos_2024_; lean_object* v_endPos_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2043_; 
v_trailing_2022_ = lean_ctor_get(v___x_2021_, 2);
v_leading_2023_ = lean_ctor_get(v___x_2021_, 0);
v_pos_2024_ = lean_ctor_get(v___x_2021_, 1);
v_endPos_2025_ = lean_ctor_get(v___x_2021_, 3);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2027_ = v___x_2021_;
v_isShared_2028_ = v_isSharedCheck_2043_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_endPos_2025_);
lean_inc(v_trailing_2022_);
lean_inc(v_pos_2024_);
lean_inc(v_leading_2023_);
lean_dec(v___x_2021_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2043_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v_str_2029_; lean_object* v_startPos_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2041_; 
v_str_2029_ = lean_ctor_get(v_trailing_2022_, 0);
v_startPos_2030_ = lean_ctor_get(v_trailing_2022_, 1);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_trailing_2022_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v_trailing_2022_, 2);
lean_dec(v_unused_2042_);
v___x_2032_ = v_trailing_2022_;
v_isShared_2033_ = v_isSharedCheck_2041_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_startPos_2030_);
lean_inc(v_str_2029_);
lean_dec(v_trailing_2022_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2041_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
lean_inc(v_startPos_2030_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 2, v_startPos_2030_);
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_str_2029_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_startPos_2030_);
lean_ctor_set(v_reuseFailAlloc_2040_, 2, v_startPos_2030_);
v___x_2035_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2037_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 2, v___x_2035_);
v___x_2037_ = v___x_2027_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_leading_2023_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_pos_2024_);
lean_ctor_set(v_reuseFailAlloc_2039_, 2, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2039_, 3, v_endPos_2025_);
v___x_2037_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_Syntax_setTailInfo(v_stx_2020_, v___x_2037_);
return v___x_2038_;
}
}
}
}
}
else
{
lean_dec(v___x_2021_);
return v_stx_2020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object* v_a_2044_, lean_object* v_f_2045_, lean_object* v_i_2046_){
_start:
{
lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = lean_array_get_size(v_a_2044_);
v___x_2048_ = lean_nat_dec_lt(v_i_2046_, v___x_2047_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
lean_dec(v_i_2046_);
lean_dec_ref(v_f_2045_);
lean_dec_ref(v_a_2044_);
v___x_2049_ = lean_box(0);
return v___x_2049_;
}
else
{
lean_object* v_v_2050_; lean_object* v___x_2051_; 
v_v_2050_ = lean_array_fget_borrowed(v_a_2044_, v_i_2046_);
lean_inc_ref(v_f_2045_);
lean_inc(v_v_2050_);
v___x_2051_ = lean_apply_1(v_f_2045_, v_v_2050_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = lean_unsigned_to_nat(1u);
v___x_2053_ = lean_nat_add(v_i_2046_, v___x_2052_);
lean_dec(v_i_2046_);
v_i_2046_ = v___x_2053_;
goto _start;
}
else
{
lean_object* v_val_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2063_; 
lean_dec_ref(v_f_2045_);
v_val_2055_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2057_ = v___x_2051_;
v_isShared_2058_ = v_isSharedCheck_2063_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_val_2055_);
lean_dec(v___x_2051_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2063_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2059_ = lean_array_fset(v_a_2044_, v_i_2046_, v_val_2055_);
lean_dec(v_i_2046_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v___x_2059_);
v___x_2061_ = v___x_2057_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object* v_00_u03b1_2064_, lean_object* v_inst_2065_, lean_object* v_a_2066_, lean_object* v_f_2067_, lean_object* v_i_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(v_a_2066_, v_f_2067_, v_i_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object* v_00_u03b1_2070_, lean_object* v_inst_2071_, lean_object* v_a_2072_, lean_object* v_f_2073_, lean_object* v_i_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(v_00_u03b1_2070_, v_inst_2071_, v_a_2072_, v_f_2073_, v_i_2074_);
lean_dec(v_inst_2071_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object* v_info_2076_, lean_object* v_x_2077_){
_start:
{
switch(lean_obj_tag(v_x_2077_))
{
case 2:
{
lean_object* v_val_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2086_; 
v_val_2078_ = lean_ctor_get(v_x_2077_, 1);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_x_2077_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v_x_2077_, 0);
lean_dec(v_unused_2087_);
v___x_2080_ = v_x_2077_;
v_isShared_2081_ = v_isSharedCheck_2086_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_val_2078_);
lean_dec(v_x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2086_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v_info_2076_);
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_info_2076_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_val_2078_);
v___x_2083_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
}
}
case 3:
{
lean_object* v_rawVal_2088_; lean_object* v_val_2089_; lean_object* v_preresolved_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2098_; 
v_rawVal_2088_ = lean_ctor_get(v_x_2077_, 1);
v_val_2089_ = lean_ctor_get(v_x_2077_, 2);
v_preresolved_2090_ = lean_ctor_get(v_x_2077_, 3);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_x_2077_);
if (v_isSharedCheck_2098_ == 0)
{
lean_object* v_unused_2099_; 
v_unused_2099_ = lean_ctor_get(v_x_2077_, 0);
lean_dec(v_unused_2099_);
v___x_2092_ = v_x_2077_;
v_isShared_2093_ = v_isSharedCheck_2098_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_preresolved_2090_);
lean_inc(v_val_2089_);
lean_inc(v_rawVal_2088_);
lean_dec(v_x_2077_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2098_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v_info_2076_);
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_info_2076_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_rawVal_2088_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_val_2089_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_preresolved_2090_);
v___x_2095_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2096_; 
v___x_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
return v___x_2096_;
}
}
}
case 1:
{
lean_object* v_info_2100_; lean_object* v_kind_2101_; lean_object* v_args_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2120_; 
v_info_2100_ = lean_ctor_get(v_x_2077_, 0);
v_kind_2101_ = lean_ctor_get(v_x_2077_, 1);
v_args_2102_ = lean_ctor_get(v_x_2077_, 2);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_x_2077_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2104_ = v_x_2077_;
v_isShared_2105_ = v_isSharedCheck_2120_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_args_2102_);
lean_inc(v_kind_2101_);
lean_inc(v_info_2100_);
lean_dec(v_x_2077_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2120_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_unsigned_to_nat(0u);
v___x_2107_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(v_info_2076_, v_args_2102_, v___x_2106_);
if (lean_obj_tag(v___x_2107_) == 1)
{
lean_object* v_val_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2118_; 
v_val_2108_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2110_ = v___x_2107_;
v_isShared_2111_ = v_isSharedCheck_2118_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_val_2108_);
lean_dec(v___x_2107_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2118_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 2, v_val_2108_);
v___x_2113_ = v___x_2104_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_info_2100_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_kind_2101_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_val_2108_);
v___x_2113_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v___x_2113_);
v___x_2115_ = v___x_2110_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_object* v___x_2119_; 
lean_dec(v___x_2107_);
lean_del_object(v___x_2104_);
lean_dec(v_kind_2101_);
lean_dec(v_info_2100_);
v___x_2119_ = lean_box(0);
return v___x_2119_;
}
}
}
default: 
{
lean_object* v___x_2121_; 
lean_dec(v_x_2077_);
lean_dec(v_info_2076_);
v___x_2121_ = lean_box(0);
return v___x_2121_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object* v_info_2122_, lean_object* v_a_2123_, lean_object* v_i_2124_){
_start:
{
lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2125_ = lean_array_get_size(v_a_2123_);
v___x_2126_ = lean_nat_dec_lt(v_i_2124_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; 
lean_dec(v_i_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_info_2122_);
v___x_2127_ = lean_box(0);
return v___x_2127_;
}
else
{
lean_object* v_v_2128_; lean_object* v___x_2129_; 
v_v_2128_ = lean_array_fget_borrowed(v_a_2123_, v_i_2124_);
lean_inc(v_v_2128_);
lean_inc(v_info_2122_);
v___x_2129_ = l_Lean_Syntax_setHeadInfoAux(v_info_2122_, v_v_2128_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = lean_unsigned_to_nat(1u);
v___x_2131_ = lean_nat_add(v_i_2124_, v___x_2130_);
lean_dec(v_i_2124_);
v_i_2124_ = v___x_2131_;
goto _start;
}
else
{
lean_object* v_val_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_info_2122_);
v_val_2133_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2135_ = v___x_2129_;
v_isShared_2136_ = v_isSharedCheck_2141_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_val_2133_);
lean_dec(v___x_2129_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2141_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2137_ = lean_array_fset(v_a_2123_, v_i_2124_, v_val_2133_);
lean_dec(v_i_2124_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2137_);
v___x_2139_ = v___x_2135_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object* v_stx_2142_, lean_object* v_info_2143_){
_start:
{
lean_object* v___x_2144_; 
lean_inc(v_stx_2142_);
v___x_2144_ = l_Lean_Syntax_setHeadInfoAux(v_info_2143_, v_stx_2142_);
if (lean_obj_tag(v___x_2144_) == 0)
{
return v_stx_2142_;
}
else
{
lean_object* v_val_2145_; 
lean_dec(v_stx_2142_);
v_val_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v___x_2144_, 1);
return v_val_2145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object* v_info_2146_, lean_object* v_x_2147_){
_start:
{
switch(lean_obj_tag(v_x_2147_))
{
case 0:
{
lean_dec(v_info_2146_);
return v_x_2147_;
}
case 1:
{
lean_object* v_kind_2148_; lean_object* v_args_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
v_kind_2148_ = lean_ctor_get(v_x_2147_, 1);
v_args_2149_ = lean_ctor_get(v_x_2147_, 2);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_x_2147_);
if (v_isSharedCheck_2156_ == 0)
{
lean_object* v_unused_2157_; 
v_unused_2157_ = lean_ctor_get(v_x_2147_, 0);
lean_dec(v_unused_2157_);
v___x_2151_ = v_x_2147_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_args_2149_);
lean_inc(v_kind_2148_);
lean_dec(v_x_2147_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v_info_2146_);
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_info_2146_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_kind_2148_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_args_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
case 2:
{
lean_object* v_val_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
v_val_2158_ = lean_ctor_get(v_x_2147_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_x_2147_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v_x_2147_, 0);
lean_dec(v_unused_2166_);
v___x_2160_ = v_x_2147_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_val_2158_);
lean_dec(v_x_2147_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v_info_2146_);
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_info_2146_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_val_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
default: 
{
lean_object* v_rawVal_2167_; lean_object* v_val_2168_; lean_object* v_preresolved_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
v_rawVal_2167_ = lean_ctor_get(v_x_2147_, 1);
v_val_2168_ = lean_ctor_get(v_x_2147_, 2);
v_preresolved_2169_ = lean_ctor_get(v_x_2147_, 3);
v_isSharedCheck_2176_ = !lean_is_exclusive(v_x_2147_);
if (v_isSharedCheck_2176_ == 0)
{
lean_object* v_unused_2177_; 
v_unused_2177_ = lean_ctor_get(v_x_2147_, 0);
lean_dec(v_unused_2177_);
v___x_2171_ = v_x_2147_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_preresolved_2169_);
lean_inc(v_val_2168_);
lean_inc(v_rawVal_2167_);
lean_dec(v_x_2147_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v_info_2146_);
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_info_2146_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_rawVal_2167_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_val_2168_);
lean_ctor_set(v_reuseFailAlloc_2175_, 3, v_preresolved_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object* v_x_2181_){
_start:
{
switch(lean_obj_tag(v_x_2181_))
{
case 2:
{
lean_object* v_info_2182_; uint8_t v___x_2183_; lean_object* v___x_2184_; 
v_info_2182_ = lean_ctor_get(v_x_2181_, 0);
v___x_2183_ = 0;
v___x_2184_ = l_Lean_SourceInfo_getPos_x3f(v_info_2182_, v___x_2183_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v___x_2185_; 
lean_dec_ref_known(v_x_2181_, 2);
v___x_2185_ = lean_box(0);
return v___x_2185_;
}
else
{
lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2192_ == 0)
{
lean_object* v_unused_2193_; 
v_unused_2193_ = lean_ctor_get(v___x_2184_, 0);
lean_dec(v_unused_2193_);
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v_x_2181_);
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_x_2181_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
case 3:
{
lean_object* v_info_2194_; uint8_t v___x_2195_; lean_object* v___x_2196_; 
v_info_2194_ = lean_ctor_get(v_x_2181_, 0);
v___x_2195_ = 0;
v___x_2196_ = l_Lean_SourceInfo_getPos_x3f(v_info_2194_, v___x_2195_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v___x_2197_; 
lean_dec_ref_known(v_x_2181_, 4);
v___x_2197_ = lean_box(0);
return v___x_2197_;
}
else
{
lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2204_ == 0)
{
lean_object* v_unused_2205_; 
v_unused_2205_ = lean_ctor_get(v___x_2196_, 0);
lean_dec(v_unused_2205_);
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v_x_2181_);
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_x_2181_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
case 1:
{
lean_object* v_info_2206_; 
v_info_2206_ = lean_ctor_get(v_x_2181_, 0);
if (lean_obj_tag(v_info_2206_) == 2)
{
lean_object* v_args_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; size_t v_sz_2210_; size_t v___x_2211_; lean_object* v___x_2212_; lean_object* v_fst_2213_; 
v_args_2207_ = lean_ctor_get(v_x_2181_, 2);
lean_inc_ref(v_args_2207_);
lean_dec_ref_known(v_x_2181_, 3);
v___x_2208_ = lean_box(0);
v___x_2209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_2210_ = lean_array_size(v_args_2207_);
v___x_2211_ = ((size_t)0ULL);
v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_args_2207_, v_sz_2210_, v___x_2211_, v___x_2209_);
lean_dec_ref(v_args_2207_);
v_fst_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_fst_2213_);
lean_dec_ref(v___x_2212_);
if (lean_obj_tag(v_fst_2213_) == 0)
{
return v___x_2208_;
}
else
{
lean_object* v_val_2214_; 
v_val_2214_ = lean_ctor_get(v_fst_2213_, 0);
lean_inc(v_val_2214_);
lean_dec_ref_known(v_fst_2213_, 1);
return v_val_2214_;
}
}
else
{
lean_object* v___x_2215_; 
v___x_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2215_, 0, v_x_2181_);
return v___x_2215_;
}
}
default: 
{
lean_object* v___x_2216_; 
lean_dec(v_x_2181_);
v___x_2216_ = lean_box(0);
return v___x_2216_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object* v_as_2217_, size_t v_sz_2218_, size_t v_i_2219_, lean_object* v_b_2220_){
_start:
{
uint8_t v___x_2221_; 
v___x_2221_ = lean_usize_dec_lt(v_i_2219_, v_sz_2218_);
if (v___x_2221_ == 0)
{
lean_inc_ref(v_b_2220_);
return v_b_2220_;
}
else
{
lean_object* v___x_2222_; lean_object* v_a_2223_; lean_object* v___x_2224_; 
v___x_2222_ = lean_box(0);
v_a_2223_ = lean_array_uget_borrowed(v_as_2217_, v_i_2219_);
lean_inc(v_a_2223_);
v___x_2224_ = l_Lean_Syntax_getHead_x3f(v_a_2223_);
if (lean_obj_tag(v___x_2224_) == 1)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
v___x_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v___x_2222_);
return v___x_2226_;
}
else
{
lean_object* v___x_2227_; size_t v___x_2228_; size_t v___x_2229_; 
lean_dec(v___x_2224_);
v___x_2227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_2228_ = ((size_t)1ULL);
v___x_2229_ = lean_usize_add(v_i_2219_, v___x_2228_);
v_i_2219_ = v___x_2229_;
v_b_2220_ = v___x_2227_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object* v_as_2231_, lean_object* v_sz_2232_, lean_object* v_i_2233_, lean_object* v_b_2234_){
_start:
{
size_t v_sz_boxed_2235_; size_t v_i_boxed_2236_; lean_object* v_res_2237_; 
v_sz_boxed_2235_ = lean_unbox_usize(v_sz_2232_);
lean_dec(v_sz_2232_);
v_i_boxed_2236_ = lean_unbox_usize(v_i_2233_);
lean_dec(v_i_2233_);
v_res_2237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_as_2231_, v_sz_boxed_2235_, v_i_boxed_2236_, v_b_2234_);
lean_dec_ref(v_b_2234_);
lean_dec_ref(v_as_2231_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object* v_target_2238_, lean_object* v_source_2239_){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2240_ = l_Lean_Syntax_getHeadInfo(v_source_2239_);
v___x_2241_ = l_Lean_Syntax_setHeadInfo(v_target_2238_, v___x_2240_);
v___x_2242_ = l_Lean_Syntax_getTailInfo(v_source_2239_);
v___x_2243_ = l_Lean_Syntax_setTailInfo(v___x_2241_, v___x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object* v_target_2244_, lean_object* v_source_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_target_2244_, v_source_2245_);
lean_dec(v_source_2245_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object* v_stx_2247_){
_start:
{
uint8_t v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = 0;
v___x_2249_ = l_Lean_SourceInfo_fromRef(v_stx_2247_, v___x_2248_);
v___x_2250_ = l_Lean_Syntax_setHeadInfo(v_stx_2247_, v___x_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object* v_val_2251_, lean_object* v_withRef_2252_, lean_object* v_x_2253_, lean_object* v_oldRef_2254_){
_start:
{
lean_object* v_ref_2255_; lean_object* v___x_2256_; 
v_ref_2255_ = l_Lean_replaceRef(v_val_2251_, v_oldRef_2254_);
v___x_2256_ = lean_apply_3(v_withRef_2252_, lean_box(0), v_ref_2255_, v_x_2253_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object* v_val_2257_, lean_object* v_withRef_2258_, lean_object* v_x_2259_, lean_object* v_oldRef_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_withHeadRefOnly___redArg___lam__0(v_val_2257_, v_withRef_2258_, v_x_2259_, v_oldRef_2260_);
lean_dec(v_oldRef_2260_);
lean_dec(v_val_2257_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object* v_x_2262_, lean_object* v_withRef_2263_, lean_object* v_toBind_2264_, lean_object* v_getRef_2265_, lean_object* v_____do__lift_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Syntax_getHead_x3f(v_____do__lift_2266_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_dec(v_getRef_2265_);
lean_dec(v_toBind_2264_);
lean_dec(v_withRef_2263_);
return v_x_2262_;
}
else
{
lean_object* v_val_2268_; lean_object* v___f_2269_; lean_object* v___x_2270_; 
v_val_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_val_2268_);
lean_dec_ref_known(v___x_2267_, 1);
v___f_2269_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2269_, 0, v_val_2268_);
lean_closure_set(v___f_2269_, 1, v_withRef_2263_);
lean_closure_set(v___f_2269_, 2, v_x_2262_);
v___x_2270_ = lean_apply_4(v_toBind_2264_, lean_box(0), lean_box(0), v_getRef_2265_, v___f_2269_);
return v___x_2270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object* v_inst_2271_, lean_object* v_inst_2272_, lean_object* v_x_2273_){
_start:
{
lean_object* v_toBind_2274_; lean_object* v_getRef_2275_; lean_object* v_withRef_2276_; lean_object* v___f_2277_; lean_object* v___x_2278_; 
v_toBind_2274_ = lean_ctor_get(v_inst_2271_, 1);
lean_inc_n(v_toBind_2274_, 2);
lean_dec_ref(v_inst_2271_);
v_getRef_2275_ = lean_ctor_get(v_inst_2272_, 0);
lean_inc_n(v_getRef_2275_, 2);
v_withRef_2276_ = lean_ctor_get(v_inst_2272_, 1);
lean_inc(v_withRef_2276_);
lean_dec_ref(v_inst_2272_);
v___f_2277_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2277_, 0, v_x_2273_);
lean_closure_set(v___f_2277_, 1, v_withRef_2276_);
lean_closure_set(v___f_2277_, 2, v_toBind_2274_);
lean_closure_set(v___f_2277_, 3, v_getRef_2275_);
v___x_2278_ = lean_apply_4(v_toBind_2274_, lean_box(0), lean_box(0), v_getRef_2275_, v___f_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object* v_m_2279_, lean_object* v_inst_2280_, lean_object* v_inst_2281_, lean_object* v_00_u03b1_2282_, lean_object* v_x_2283_){
_start:
{
lean_object* v_toBind_2284_; lean_object* v_getRef_2285_; lean_object* v_withRef_2286_; lean_object* v___f_2287_; lean_object* v___x_2288_; 
v_toBind_2284_ = lean_ctor_get(v_inst_2280_, 1);
lean_inc_n(v_toBind_2284_, 2);
lean_dec_ref(v_inst_2280_);
v_getRef_2285_ = lean_ctor_get(v_inst_2281_, 0);
lean_inc_n(v_getRef_2285_, 2);
v_withRef_2286_ = lean_ctor_get(v_inst_2281_, 1);
lean_inc(v_withRef_2286_);
lean_dec_ref(v_inst_2281_);
v___f_2287_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2287_, 0, v_x_2283_);
lean_closure_set(v___f_2287_, 1, v_withRef_2286_);
lean_closure_set(v___f_2287_, 2, v_toBind_2284_);
lean_closure_set(v___f_2287_, 3, v_getRef_2285_);
v___x_2288_ = lean_apply_4(v_toBind_2284_, lean_box(0), lean_box(0), v_getRef_2285_, v___f_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(uint8_t v___x_2298_, lean_object* v_k_2299_){
_start:
{
lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_2301_ = lean_name_eq(v_k_2299_, v___x_2300_);
if (v___x_2301_ == 0)
{
return v___x_2298_;
}
else
{
uint8_t v___x_2302_; 
v___x_2302_ = 0;
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object* v___x_2303_, lean_object* v_k_2304_){
_start:
{
uint8_t v___x_1884__boxed_2305_; uint8_t v_res_2306_; lean_object* v_r_2307_; 
v___x_1884__boxed_2305_ = lean_unbox(v___x_2303_);
v_res_2306_ = l_Lean_expandMacros___lam__0(v___x_1884__boxed_2305_, v_k_2304_);
lean_dec(v_k_2304_);
v_r_2307_ = lean_box(v_res_2306_);
return v_r_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object* v_stx_2309_, lean_object* v_p_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
if (lean_obj_tag(v_stx_2309_) == 1)
{
lean_object* v_info_2313_; lean_object* v_kind_2314_; lean_object* v_args_2315_; lean_object* v___x_2316_; lean_object* v_methods_2318_; lean_object* v_quotContext_2319_; lean_object* v_currMacroScope_2320_; lean_object* v_currRecDepth_2321_; lean_object* v_maxRecDepth_2322_; lean_object* v_ref_2323_; lean_object* v___y_2324_; uint8_t v___x_2351_; 
v_info_2313_ = lean_ctor_get(v_stx_2309_, 0);
v_kind_2314_ = lean_ctor_get(v_stx_2309_, 1);
v_args_2315_ = lean_ctor_get(v_stx_2309_, 2);
lean_inc(v_kind_2314_);
v___x_2316_ = lean_apply_1(v_p_2310_, v_kind_2314_);
v___x_2351_ = lean_unbox(v___x_2316_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; 
lean_dec_ref(v_a_2311_);
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v_stx_2309_);
lean_ctor_set(v___x_2352_, 1, v_a_2312_);
return v___x_2352_;
}
else
{
lean_object* v_methods_2353_; lean_object* v_quotContext_2354_; lean_object* v_currMacroScope_2355_; lean_object* v_currRecDepth_2356_; lean_object* v_maxRecDepth_2357_; lean_object* v_ref_2358_; lean_object* v_ref_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v_methods_2353_ = lean_ctor_get(v_a_2311_, 0);
lean_inc_n(v_methods_2353_, 2);
v_quotContext_2354_ = lean_ctor_get(v_a_2311_, 1);
lean_inc_n(v_quotContext_2354_, 2);
v_currMacroScope_2355_ = lean_ctor_get(v_a_2311_, 2);
lean_inc_n(v_currMacroScope_2355_, 2);
v_currRecDepth_2356_ = lean_ctor_get(v_a_2311_, 3);
lean_inc_n(v_currRecDepth_2356_, 2);
v_maxRecDepth_2357_ = lean_ctor_get(v_a_2311_, 4);
lean_inc_n(v_maxRecDepth_2357_, 2);
v_ref_2358_ = lean_ctor_get(v_a_2311_, 5);
lean_inc(v_ref_2358_);
lean_dec_ref(v_a_2311_);
v_ref_2359_ = l_Lean_replaceRef(v_stx_2309_, v_ref_2358_);
lean_dec(v_ref_2358_);
lean_inc(v_ref_2359_);
v___x_2360_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2360_, 0, v_methods_2353_);
lean_ctor_set(v___x_2360_, 1, v_quotContext_2354_);
lean_ctor_set(v___x_2360_, 2, v_currMacroScope_2355_);
lean_ctor_set(v___x_2360_, 3, v_currRecDepth_2356_);
lean_ctor_set(v___x_2360_, 4, v_maxRecDepth_2357_);
lean_ctor_set(v___x_2360_, 5, v_ref_2359_);
lean_inc_ref(v_stx_2309_);
v___x_2361_ = l_Lean_Macro_expandMacro_x3f(v_stx_2309_, v___x_2360_, v_a_2312_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
if (lean_obj_tag(v_a_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2375_; 
lean_dec_ref_known(v___x_2360_, 6);
v_a_2363_ = lean_ctor_get(v___x_2361_, 1);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; 
v_unused_2376_ = lean_ctor_get(v___x_2361_, 0);
lean_dec(v_unused_2376_);
v___x_2365_ = v___x_2361_;
v_isShared_2366_ = v_isSharedCheck_2375_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2361_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2375_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2367_ = lean_unsigned_to_nat(0u);
v___x_2368_ = lean_nat_dec_eq(v_maxRecDepth_2357_, v___x_2367_);
if (v___x_2368_ == 0)
{
uint8_t v___x_2369_; 
v___x_2369_ = lean_nat_dec_eq(v_currRecDepth_2356_, v_maxRecDepth_2357_);
if (v___x_2369_ == 0)
{
lean_inc_ref(v_args_2315_);
lean_inc(v_kind_2314_);
lean_inc(v_info_2313_);
lean_del_object(v___x_2365_);
lean_dec_ref_known(v_stx_2309_, 3);
v_methods_2318_ = v_methods_2353_;
v_quotContext_2319_ = v_quotContext_2354_;
v_currMacroScope_2320_ = v_currMacroScope_2355_;
v_currRecDepth_2321_ = v_currRecDepth_2356_;
v_maxRecDepth_2322_ = v_maxRecDepth_2357_;
v_ref_2323_ = v_ref_2359_;
v___y_2324_ = v_a_2363_;
goto v___jp_2317_;
}
else
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2373_; 
lean_dec(v_ref_2359_);
lean_dec(v_maxRecDepth_2357_);
lean_dec(v_currRecDepth_2356_);
lean_dec(v_currMacroScope_2355_);
lean_dec(v_quotContext_2354_);
lean_dec(v_methods_2353_);
v___x_2370_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v_stx_2309_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set_tag(v___x_2365_, 1);
lean_ctor_set(v___x_2365_, 0, v___x_2371_);
v___x_2373_ = v___x_2365_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_a_2363_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
else
{
lean_inc_ref(v_args_2315_);
lean_inc(v_kind_2314_);
lean_inc(v_info_2313_);
lean_del_object(v___x_2365_);
lean_dec_ref_known(v_stx_2309_, 3);
v_methods_2318_ = v_methods_2353_;
v_quotContext_2319_ = v_quotContext_2354_;
v_currMacroScope_2320_ = v_currMacroScope_2355_;
v_currRecDepth_2321_ = v_currRecDepth_2356_;
v_maxRecDepth_2322_ = v_maxRecDepth_2357_;
v_ref_2323_ = v_ref_2359_;
v___y_2324_ = v_a_2363_;
goto v___jp_2317_;
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v_val_2378_; lean_object* v___f_2379_; 
lean_inc_ref(v_a_2362_);
lean_dec(v_ref_2359_);
lean_dec(v_maxRecDepth_2357_);
lean_dec(v_currRecDepth_2356_);
lean_dec(v_currMacroScope_2355_);
lean_dec(v_quotContext_2354_);
lean_dec(v_methods_2353_);
lean_dec_ref_known(v_stx_2309_, 3);
v_a_2377_ = lean_ctor_get(v___x_2361_, 1);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2361_, 2);
v_val_2378_ = lean_ctor_get(v_a_2362_, 0);
lean_inc(v_val_2378_);
lean_dec_ref_known(v_a_2362_, 1);
v___f_2379_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2379_, 0, v___x_2316_);
v_stx_2309_ = v_val_2378_;
v_p_2310_ = v___f_2379_;
v_a_2311_ = v___x_2360_;
v_a_2312_ = v_a_2377_;
goto _start;
}
}
else
{
lean_object* v_a_2381_; lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref_known(v___x_2360_, 6);
lean_dec(v_ref_2359_);
lean_dec(v_maxRecDepth_2357_);
lean_dec(v_currRecDepth_2356_);
lean_dec(v_currMacroScope_2355_);
lean_dec(v_quotContext_2354_);
lean_dec(v_methods_2353_);
lean_dec_ref_known(v_stx_2309_, 3);
v_a_2381_ = lean_ctor_get(v___x_2361_, 0);
v_a_2382_ = lean_ctor_get(v___x_2361_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2361_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_inc(v_a_2381_);
lean_dec(v___x_2361_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2381_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
v___jp_2317_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; size_t v_sz_2328_; size_t v___x_2329_; uint8_t v___x_2330_; lean_object* v___x_2331_; 
v___x_2325_ = lean_unsigned_to_nat(1u);
v___x_2326_ = lean_nat_add(v_currRecDepth_2321_, v___x_2325_);
lean_dec(v_currRecDepth_2321_);
v___x_2327_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2327_, 0, v_methods_2318_);
lean_ctor_set(v___x_2327_, 1, v_quotContext_2319_);
lean_ctor_set(v___x_2327_, 2, v_currMacroScope_2320_);
lean_ctor_set(v___x_2327_, 3, v___x_2326_);
lean_ctor_set(v___x_2327_, 4, v_maxRecDepth_2322_);
lean_ctor_set(v___x_2327_, 5, v_ref_2323_);
v_sz_2328_ = lean_array_size(v_args_2315_);
v___x_2329_ = ((size_t)0ULL);
v___x_2330_ = lean_unbox(v___x_2316_);
v___x_2331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2330_, v_sz_2328_, v___x_2329_, v_args_2315_, v___x_2327_, v___y_2324_);
lean_dec_ref_known(v___x_2327_, 6);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2341_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
v_a_2333_ = lean_ctor_get(v___x_2331_, 1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2335_ = v___x_2331_;
v_isShared_2336_ = v_isSharedCheck_2341_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_inc(v_a_2332_);
lean_dec(v___x_2331_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2341_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2337_, 0, v_info_2313_);
lean_ctor_set(v___x_2337_, 1, v_kind_2314_);
lean_ctor_set(v___x_2337_, 2, v_a_2332_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2337_);
v___x_2339_ = v___x_2335_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_a_2333_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_kind_2314_);
lean_dec(v_info_2313_);
v_a_2342_ = lean_ctor_get(v___x_2331_, 0);
v_a_2343_ = lean_ctor_get(v___x_2331_, 1);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2331_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_inc(v_a_2342_);
lean_dec(v___x_2331_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2342_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
else
{
lean_object* v___x_2390_; 
lean_dec_ref(v_a_2311_);
lean_dec_ref(v_p_2310_);
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v_stx_2309_);
lean_ctor_set(v___x_2390_, 1, v_a_2312_);
return v___x_2390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t v___x_2391_, size_t v_sz_2392_, size_t v_i_2393_, lean_object* v_bs_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
uint8_t v___x_2397_; 
v___x_2397_ = lean_usize_dec_lt(v_i_2393_, v_sz_2392_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2398_, 0, v_bs_2394_);
lean_ctor_set(v___x_2398_, 1, v___y_2396_);
return v___x_2398_;
}
else
{
lean_object* v___x_2399_; lean_object* v___f_2400_; lean_object* v_v_2401_; lean_object* v___x_2402_; 
v___x_2399_ = lean_box(v___x_2391_);
v___f_2400_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2400_, 0, v___x_2399_);
v_v_2401_ = lean_array_uget_borrowed(v_bs_2394_, v_i_2393_);
lean_inc_ref(v___y_2395_);
lean_inc(v_v_2401_);
v___x_2402_ = l_Lean_expandMacros(v_v_2401_, v___f_2400_, v___y_2395_, v___y_2396_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v_a_2404_; lean_object* v___x_2405_; lean_object* v_bs_x27_2406_; size_t v___x_2407_; size_t v___x_2408_; lean_object* v___x_2409_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
v_a_2404_ = lean_ctor_get(v___x_2402_, 1);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2402_, 2);
v___x_2405_ = lean_unsigned_to_nat(0u);
v_bs_x27_2406_ = lean_array_uset(v_bs_2394_, v_i_2393_, v___x_2405_);
v___x_2407_ = ((size_t)1ULL);
v___x_2408_ = lean_usize_add(v_i_2393_, v___x_2407_);
v___x_2409_ = lean_array_uset(v_bs_x27_2406_, v_i_2393_, v_a_2403_);
v_i_2393_ = v___x_2408_;
v_bs_2394_ = v___x_2409_;
v___y_2396_ = v_a_2404_;
goto _start;
}
else
{
lean_object* v_a_2411_; lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec_ref(v_bs_2394_);
v_a_2411_ = lean_ctor_get(v___x_2402_, 0);
v_a_2412_ = lean_ctor_get(v___x_2402_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2402_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_inc(v_a_2411_);
lean_dec(v___x_2402_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2411_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object* v___x_2420_, lean_object* v_sz_2421_, lean_object* v_i_2422_, lean_object* v_bs_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
uint8_t v___x_1903__boxed_2426_; size_t v_sz_boxed_2427_; size_t v_i_boxed_2428_; lean_object* v_res_2429_; 
v___x_1903__boxed_2426_ = lean_unbox(v___x_2420_);
v_sz_boxed_2427_ = lean_unbox_usize(v_sz_2421_);
lean_dec(v_sz_2421_);
v_i_boxed_2428_ = lean_unbox_usize(v_i_2422_);
lean_dec(v_i_2422_);
v_res_2429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_1903__boxed_2426_, v_sz_boxed_2427_, v_i_boxed_2428_, v_bs_2423_, v___y_2424_, v___y_2425_);
lean_dec_ref(v___y_2424_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object* v_src_2430_, lean_object* v_val_2431_, uint8_t v_canonical_2432_){
_start:
{
lean_object* v___x_2433_; uint8_t v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2433_ = l_Lean_SourceInfo_fromRef(v_src_2430_, v_canonical_2432_);
v___x_2434_ = 1;
lean_inc(v_val_2431_);
v___x_2435_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2431_, v___x_2434_);
v___x_2436_ = lean_unsigned_to_nat(0u);
v___x_2437_ = lean_string_utf8_byte_size(v___x_2435_);
v___x_2438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2435_);
lean_ctor_set(v___x_2438_, 1, v___x_2436_);
lean_ctor_set(v___x_2438_, 2, v___x_2437_);
v___x_2439_ = lean_box(0);
v___x_2440_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2433_);
lean_ctor_set(v___x_2440_, 1, v___x_2438_);
lean_ctor_set(v___x_2440_, 2, v_val_2431_);
lean_ctor_set(v___x_2440_, 3, v___x_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object* v_src_2441_, lean_object* v_val_2442_, lean_object* v_canonical_2443_){
_start:
{
uint8_t v_canonical_boxed_2444_; lean_object* v_res_2445_; 
v_canonical_boxed_2444_ = lean_unbox(v_canonical_2443_);
v_res_2445_ = l_Lean_mkIdentFrom(v_src_2441_, v_val_2442_, v_canonical_boxed_2444_);
lean_dec(v_src_2441_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom(lean_object* v_src_2461_, lean_object* v_text_2462_, uint8_t v_canonical_2463_){
_start:
{
lean_object* v_info_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v_body_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v_info_2464_ = l_Lean_SourceInfo_fromRef(v_src_2461_, v_canonical_2463_);
v___x_2465_ = lean_box(2);
v___x_2466_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__2));
lean_inc_n(v_info_2464_, 2);
v___x_2467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2467_, 0, v_info_2464_);
lean_ctor_set(v___x_2467_, 1, v_text_2462_);
v___x_2468_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__3));
v___x_2469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2469_, 0, v_info_2464_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_unsigned_to_nat(2u);
v___x_2471_ = lean_mk_empty_array_with_capacity(v___x_2470_);
lean_inc_ref(v___x_2471_);
v___x_2472_ = lean_array_push(v___x_2471_, v___x_2467_);
v___x_2473_ = lean_array_push(v___x_2472_, v___x_2469_);
v_body_2474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_body_2474_, 0, v___x_2465_);
lean_ctor_set(v_body_2474_, 1, v___x_2466_);
lean_ctor_set(v_body_2474_, 2, v___x_2473_);
v___x_2475_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__5));
v___x_2476_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__6));
v___x_2477_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2477_, 0, v_info_2464_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = lean_array_push(v___x_2471_, v___x_2477_);
v___x_2479_ = lean_array_push(v___x_2478_, v_body_2474_);
v___x_2480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2465_);
lean_ctor_set(v___x_2480_, 1, v___x_2475_);
lean_ctor_set(v___x_2480_, 2, v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocCommentFrom___boxed(lean_object* v_src_2481_, lean_object* v_text_2482_, lean_object* v_canonical_2483_){
_start:
{
uint8_t v_canonical_boxed_2484_; lean_object* v_res_2485_; 
v_canonical_boxed_2484_ = lean_unbox(v_canonical_2483_);
v_res_2485_ = l_Lean_mkMarkdownDocCommentFrom(v_src_2481_, v_text_2482_, v_canonical_boxed_2484_);
lean_dec(v_src_2481_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMarkdownDocComment(lean_object* v_text_2486_){
_start:
{
lean_object* v___x_2487_; uint8_t v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = lean_box(0);
v___x_2488_ = 0;
v___x_2489_ = l_Lean_mkMarkdownDocCommentFrom(v___x_2487_, v_text_2486_, v___x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object* v_val_2490_, uint8_t v_canonical_2491_, lean_object* v_toPure_2492_, lean_object* v_____do__lift_2493_){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = l_Lean_mkIdentFrom(v_____do__lift_2493_, v_val_2490_, v_canonical_2491_);
v___x_2495_ = lean_apply_2(v_toPure_2492_, lean_box(0), v___x_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object* v_val_2496_, lean_object* v_canonical_2497_, lean_object* v_toPure_2498_, lean_object* v_____do__lift_2499_){
_start:
{
uint8_t v_canonical_boxed_2500_; lean_object* v_res_2501_; 
v_canonical_boxed_2500_ = lean_unbox(v_canonical_2497_);
v_res_2501_ = l_Lean_mkIdentFromRef___redArg___lam__0(v_val_2496_, v_canonical_boxed_2500_, v_toPure_2498_, v_____do__lift_2499_);
lean_dec(v_____do__lift_2499_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object* v_inst_2502_, lean_object* v_inst_2503_, lean_object* v_val_2504_, uint8_t v_canonical_2505_){
_start:
{
lean_object* v_toApplicative_2506_; lean_object* v_toBind_2507_; lean_object* v_getRef_2508_; lean_object* v_toPure_2509_; lean_object* v___x_2510_; lean_object* v___f_2511_; lean_object* v___x_2512_; 
v_toApplicative_2506_ = lean_ctor_get(v_inst_2502_, 0);
lean_inc_ref(v_toApplicative_2506_);
v_toBind_2507_ = lean_ctor_get(v_inst_2502_, 1);
lean_inc(v_toBind_2507_);
lean_dec_ref(v_inst_2502_);
v_getRef_2508_ = lean_ctor_get(v_inst_2503_, 0);
lean_inc(v_getRef_2508_);
lean_dec_ref(v_inst_2503_);
v_toPure_2509_ = lean_ctor_get(v_toApplicative_2506_, 1);
lean_inc(v_toPure_2509_);
lean_dec_ref(v_toApplicative_2506_);
v___x_2510_ = lean_box(v_canonical_2505_);
v___f_2511_ = lean_alloc_closure((void*)(l_Lean_mkIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2511_, 0, v_val_2504_);
lean_closure_set(v___f_2511_, 1, v___x_2510_);
lean_closure_set(v___f_2511_, 2, v_toPure_2509_);
v___x_2512_ = lean_apply_4(v_toBind_2507_, lean_box(0), lean_box(0), v_getRef_2508_, v___f_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object* v_inst_2513_, lean_object* v_inst_2514_, lean_object* v_val_2515_, lean_object* v_canonical_2516_){
_start:
{
uint8_t v_canonical_boxed_2517_; lean_object* v_res_2518_; 
v_canonical_boxed_2517_ = lean_unbox(v_canonical_2516_);
v_res_2518_ = l_Lean_mkIdentFromRef___redArg(v_inst_2513_, v_inst_2514_, v_val_2515_, v_canonical_boxed_2517_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object* v_m_2519_, lean_object* v_inst_2520_, lean_object* v_inst_2521_, lean_object* v_val_2522_, uint8_t v_canonical_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_mkIdentFromRef___redArg(v_inst_2520_, v_inst_2521_, v_val_2522_, v_canonical_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object* v_m_2525_, lean_object* v_inst_2526_, lean_object* v_inst_2527_, lean_object* v_val_2528_, lean_object* v_canonical_2529_){
_start:
{
uint8_t v_canonical_boxed_2530_; lean_object* v_res_2531_; 
v_canonical_boxed_2530_ = lean_unbox(v_canonical_2529_);
v_res_2531_ = l_Lean_mkIdentFromRef(v_m_2525_, v_inst_2526_, v_inst_2527_, v_val_2528_, v_canonical_boxed_2530_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object* v_src_2535_, lean_object* v_c_2536_, uint8_t v_canonical_2537_){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v_id_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2538_ = ((lean_object*)(l_Lean_mkCIdentFrom___closed__1));
v___x_2539_ = lean_unsigned_to_nat(0u);
lean_inc(v_c_2536_);
v_id_2540_ = l_Lean_addMacroScope(v___x_2538_, v_c_2536_, v___x_2539_);
v___x_2541_ = l_Lean_SourceInfo_fromRef(v_src_2535_, v_canonical_2537_);
v___x_2542_ = 1;
lean_inc(v_id_2540_);
v___x_2543_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_id_2540_, v___x_2542_);
v___x_2544_ = lean_string_utf8_byte_size(v___x_2543_);
v___x_2545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2539_);
lean_ctor_set(v___x_2545_, 2, v___x_2544_);
v___x_2546_ = lean_box(0);
v___x_2547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2547_, 0, v_c_2536_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
lean_ctor_set(v___x_2548_, 1, v___x_2546_);
v___x_2549_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2541_);
lean_ctor_set(v___x_2549_, 1, v___x_2545_);
lean_ctor_set(v___x_2549_, 2, v_id_2540_);
lean_ctor_set(v___x_2549_, 3, v___x_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* v_src_2550_, lean_object* v_c_2551_, lean_object* v_canonical_2552_){
_start:
{
uint8_t v_canonical_boxed_2553_; lean_object* v_res_2554_; 
v_canonical_boxed_2553_ = lean_unbox(v_canonical_2552_);
v_res_2554_ = l_Lean_mkCIdentFrom(v_src_2550_, v_c_2551_, v_canonical_boxed_2553_);
lean_dec(v_src_2550_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object* v_c_2555_, uint8_t v_canonical_2556_, lean_object* v_toPure_2557_, lean_object* v_____do__lift_2558_){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = l_Lean_mkCIdentFrom(v_____do__lift_2558_, v_c_2555_, v_canonical_2556_);
v___x_2560_ = lean_apply_2(v_toPure_2557_, lean_box(0), v___x_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object* v_c_2561_, lean_object* v_canonical_2562_, lean_object* v_toPure_2563_, lean_object* v_____do__lift_2564_){
_start:
{
uint8_t v_canonical_boxed_2565_; lean_object* v_res_2566_; 
v_canonical_boxed_2565_ = lean_unbox(v_canonical_2562_);
v_res_2566_ = l_Lean_mkCIdentFromRef___redArg___lam__0(v_c_2561_, v_canonical_boxed_2565_, v_toPure_2563_, v_____do__lift_2564_);
lean_dec(v_____do__lift_2564_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object* v_inst_2567_, lean_object* v_inst_2568_, lean_object* v_c_2569_, uint8_t v_canonical_2570_){
_start:
{
lean_object* v_toApplicative_2571_; lean_object* v_toBind_2572_; lean_object* v_getRef_2573_; lean_object* v_toPure_2574_; lean_object* v___x_2575_; lean_object* v___f_2576_; lean_object* v___x_2577_; 
v_toApplicative_2571_ = lean_ctor_get(v_inst_2567_, 0);
lean_inc_ref(v_toApplicative_2571_);
v_toBind_2572_ = lean_ctor_get(v_inst_2567_, 1);
lean_inc(v_toBind_2572_);
lean_dec_ref(v_inst_2567_);
v_getRef_2573_ = lean_ctor_get(v_inst_2568_, 0);
lean_inc(v_getRef_2573_);
lean_dec_ref(v_inst_2568_);
v_toPure_2574_ = lean_ctor_get(v_toApplicative_2571_, 1);
lean_inc(v_toPure_2574_);
lean_dec_ref(v_toApplicative_2571_);
v___x_2575_ = lean_box(v_canonical_2570_);
v___f_2576_ = lean_alloc_closure((void*)(l_Lean_mkCIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2576_, 0, v_c_2569_);
lean_closure_set(v___f_2576_, 1, v___x_2575_);
lean_closure_set(v___f_2576_, 2, v_toPure_2574_);
v___x_2577_ = lean_apply_4(v_toBind_2572_, lean_box(0), lean_box(0), v_getRef_2573_, v___f_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object* v_inst_2578_, lean_object* v_inst_2579_, lean_object* v_c_2580_, lean_object* v_canonical_2581_){
_start:
{
uint8_t v_canonical_boxed_2582_; lean_object* v_res_2583_; 
v_canonical_boxed_2582_ = lean_unbox(v_canonical_2581_);
v_res_2583_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2578_, v_inst_2579_, v_c_2580_, v_canonical_boxed_2582_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object* v_m_2584_, lean_object* v_inst_2585_, lean_object* v_inst_2586_, lean_object* v_c_2587_, uint8_t v_canonical_2588_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2585_, v_inst_2586_, v_c_2587_, v_canonical_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object* v_m_2590_, lean_object* v_inst_2591_, lean_object* v_inst_2592_, lean_object* v_c_2593_, lean_object* v_canonical_2594_){
_start:
{
uint8_t v_canonical_boxed_2595_; lean_object* v_res_2596_; 
v_canonical_boxed_2595_ = lean_unbox(v_canonical_2594_);
v_res_2596_ = l_Lean_mkCIdentFromRef(v_m_2590_, v_inst_2591_, v_inst_2592_, v_c_2593_, v_canonical_boxed_2595_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object* v_c_2597_){
_start:
{
lean_object* v___x_2598_; uint8_t v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_box(0);
v___x_2599_ = 0;
v___x_2600_ = l_Lean_mkCIdentFrom(v___x_2598_, v_c_2597_, v___x_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdent(lean_object* v_val_2601_){
_start:
{
lean_object* v___x_2602_; uint8_t v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2602_ = lean_box(2);
v___x_2603_ = 1;
lean_inc(v_val_2601_);
v___x_2604_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2601_, v___x_2603_);
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_string_utf8_byte_size(v___x_2604_);
v___x_2607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2604_);
lean_ctor_set(v___x_2607_, 1, v___x_2605_);
lean_ctor_set(v___x_2607_, 2, v___x_2606_);
v___x_2608_ = lean_box(0);
v___x_2609_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2602_);
lean_ctor_set(v___x_2609_, 1, v___x_2607_);
lean_ctor_set(v___x_2609_, 2, v_val_2601_);
lean_ctor_set(v___x_2609_, 3, v___x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object* v_args_2613_){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = ((lean_object*)(l_Lean_mkGroupNode___closed__1));
v___x_2615_ = lean_box(2);
v___x_2616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
lean_ctor_set(v___x_2616_, 1, v___x_2614_);
lean_ctor_set(v___x_2616_, 2, v_args_2613_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object* v_sep_2617_, lean_object* v_as_2618_, size_t v_sz_2619_, size_t v_i_2620_, lean_object* v_b_2621_){
_start:
{
uint8_t v___x_2622_; 
v___x_2622_ = lean_usize_dec_lt(v_i_2620_, v_sz_2619_);
if (v___x_2622_ == 0)
{
lean_dec(v_sep_2617_);
return v_b_2621_;
}
else
{
lean_object* v_fst_2623_; lean_object* v_snd_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2644_; 
v_fst_2623_ = lean_ctor_get(v_b_2621_, 0);
v_snd_2624_ = lean_ctor_get(v_b_2621_, 1);
v_isSharedCheck_2644_ = !lean_is_exclusive(v_b_2621_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2626_ = v_b_2621_;
v_isShared_2627_ = v_isSharedCheck_2644_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_snd_2624_);
lean_inc(v_fst_2623_);
lean_dec(v_b_2621_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2644_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v_r_2629_; lean_object* v_i_2638_; lean_object* v_a_2639_; uint8_t v___x_2640_; 
v_i_2638_ = lean_unsigned_to_nat(0u);
v_a_2639_ = lean_array_uget_borrowed(v_as_2618_, v_i_2620_);
v___x_2640_ = lean_nat_dec_lt(v_i_2638_, v_fst_2623_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; 
lean_inc(v_a_2639_);
v___x_2641_ = lean_array_push(v_snd_2624_, v_a_2639_);
v_r_2629_ = v___x_2641_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
lean_inc(v_sep_2617_);
v___x_2642_ = lean_array_push(v_snd_2624_, v_sep_2617_);
lean_inc(v_a_2639_);
v___x_2643_ = lean_array_push(v___x_2642_, v_a_2639_);
v_r_2629_ = v___x_2643_;
goto v___jp_2628_;
}
v___jp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2630_ = lean_unsigned_to_nat(1u);
v___x_2631_ = lean_nat_add(v_fst_2623_, v___x_2630_);
lean_dec(v_fst_2623_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 1, v_r_2629_);
lean_ctor_set(v___x_2626_, 0, v___x_2631_);
v___x_2633_ = v___x_2626_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_r_2629_);
v___x_2633_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
size_t v___x_2634_; size_t v___x_2635_; 
v___x_2634_ = ((size_t)1ULL);
v___x_2635_ = lean_usize_add(v_i_2620_, v___x_2634_);
v_i_2620_ = v___x_2635_;
v_b_2621_ = v___x_2633_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object* v_sep_2645_, lean_object* v_as_2646_, lean_object* v_sz_2647_, lean_object* v_i_2648_, lean_object* v_b_2649_){
_start:
{
size_t v_sz_boxed_2650_; size_t v_i_boxed_2651_; lean_object* v_res_2652_; 
v_sz_boxed_2650_ = lean_unbox_usize(v_sz_2647_);
lean_dec(v_sz_2647_);
v_i_boxed_2651_ = lean_unbox_usize(v_i_2648_);
lean_dec(v_i_2648_);
v_res_2652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2645_, v_as_2646_, v_sz_boxed_2650_, v_i_boxed_2651_, v_b_2649_);
lean_dec_ref(v_as_2646_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object* v_as_2658_, lean_object* v_sep_2659_){
_start:
{
lean_object* v___x_2660_; size_t v_sz_2661_; size_t v___x_2662_; lean_object* v___x_2663_; lean_object* v_snd_2664_; 
v___x_2660_ = ((lean_object*)(l_Lean_mkSepArray___closed__1));
v_sz_2661_ = lean_array_size(v_as_2658_);
v___x_2662_ = ((size_t)0ULL);
v___x_2663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2659_, v_as_2658_, v_sz_2661_, v___x_2662_, v___x_2660_);
v_snd_2664_ = lean_ctor_get(v___x_2663_, 1);
lean_inc(v_snd_2664_);
lean_dec_ref(v___x_2663_);
return v_snd_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object* v_as_2665_, lean_object* v_sep_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_mkSepArray(v_as_2665_, v_sep_2666_);
lean_dec_ref(v_as_2665_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object* v_arg_2675_){
_start:
{
if (lean_obj_tag(v_arg_2675_) == 0)
{
lean_object* v___x_2676_; 
v___x_2676_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
return v___x_2676_;
}
else
{
lean_object* v_val_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v_val_2677_ = lean_ctor_get(v_arg_2675_, 0);
lean_inc(v_val_2677_);
lean_dec_ref_known(v_arg_2675_, 1);
v___x_2678_ = lean_unsigned_to_nat(1u);
v___x_2679_ = lean_mk_empty_array_with_capacity(v___x_2678_);
v___x_2680_ = lean_array_push(v___x_2679_, v_val_2677_);
v___x_2681_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2682_ = lean_box(2);
v___x_2683_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
lean_ctor_set(v___x_2683_, 1, v___x_2681_);
lean_ctor_set(v___x_2683_, 2, v___x_2680_);
return v___x_2683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object* v_ref_2690_, uint8_t v_canonical_2691_){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2692_ = ((lean_object*)(l_Lean_mkHole___closed__1));
v___x_2693_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_2694_ = l_Lean_mkAtomFrom(v_ref_2690_, v___x_2693_, v_canonical_2691_);
v___x_2695_ = lean_unsigned_to_nat(1u);
v___x_2696_ = lean_mk_empty_array_with_capacity(v___x_2695_);
v___x_2697_ = lean_array_push(v___x_2696_, v___x_2694_);
v___x_2698_ = lean_box(2);
v___x_2699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
lean_ctor_set(v___x_2699_, 1, v___x_2692_);
lean_ctor_set(v___x_2699_, 2, v___x_2697_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object* v_ref_2700_, lean_object* v_canonical_2701_){
_start:
{
uint8_t v_canonical_boxed_2702_; lean_object* v_res_2703_; 
v_canonical_boxed_2702_ = lean_unbox(v_canonical_2701_);
v_res_2703_ = l_Lean_mkHole(v_ref_2700_, v_canonical_boxed_2702_);
lean_dec(v_ref_2700_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object* v_a_2704_, lean_object* v_sep_2705_){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2706_ = l_Lean_mkSepArray(v_a_2704_, v_sep_2705_);
v___x_2707_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2708_ = lean_box(2);
v___x_2709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
lean_ctor_set(v___x_2709_, 1, v___x_2707_);
lean_ctor_set(v___x_2709_, 2, v___x_2706_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object* v_a_2710_, lean_object* v_sep_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lean_Syntax_mkSep(v_a_2710_, v_sep_2711_);
lean_dec_ref(v_a_2710_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object* v_sep_2719_, lean_object* v_elems_2720_){
_start:
{
uint8_t v___x_2721_; 
lean_inc_ref(v_sep_2719_);
v___x_2721_ = lean_string_isempty(v_sep_2719_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = l_Lean_mkAtom(v_sep_2719_);
v___x_2723_ = l_Lean_mkSepArray(v_elems_2720_, v___x_2722_);
return v___x_2723_;
}
else
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_dec_ref(v_sep_2719_);
v___x_2724_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___x_2725_ = l_Lean_mkSepArray(v_elems_2720_, v___x_2724_);
return v___x_2725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object* v_sep_2726_, lean_object* v_elems_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2726_, v_elems_2727_);
lean_dec_ref(v_elems_2727_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object* v_elems_2729_, lean_object* v_toPure_2730_, lean_object* v_sep_2731_, lean_object* v_ref_2732_){
_start:
{
lean_object* v___y_2734_; uint8_t v___x_2737_; 
lean_inc_ref(v_sep_2731_);
v___x_2737_ = lean_string_isempty(v_sep_2731_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Lean_mkAtomFrom(v_ref_2732_, v_sep_2731_, v___x_2737_);
v___y_2734_ = v___x_2738_;
goto v___jp_2733_;
}
else
{
lean_object* v___x_2739_; 
lean_dec_ref(v_sep_2731_);
v___x_2739_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___y_2734_ = v___x_2739_;
goto v___jp_2733_;
}
v___jp_2733_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = l_Lean_mkSepArray(v_elems_2729_, v___y_2734_);
v___x_2736_ = lean_apply_2(v_toPure_2730_, lean_box(0), v___x_2735_);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object* v_elems_2740_, lean_object* v_toPure_2741_, lean_object* v_sep_2742_, lean_object* v_ref_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(v_elems_2740_, v_toPure_2741_, v_sep_2742_, v_ref_2743_);
lean_dec(v_ref_2743_);
lean_dec_ref(v_elems_2740_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object* v_inst_2745_, lean_object* v_inst_2746_, lean_object* v_sep_2747_, lean_object* v_elems_2748_){
_start:
{
lean_object* v_toApplicative_2749_; lean_object* v_toBind_2750_; lean_object* v_getRef_2751_; lean_object* v_toPure_2752_; lean_object* v___f_2753_; lean_object* v___x_2754_; 
v_toApplicative_2749_ = lean_ctor_get(v_inst_2745_, 0);
lean_inc_ref(v_toApplicative_2749_);
v_toBind_2750_ = lean_ctor_get(v_inst_2745_, 1);
lean_inc(v_toBind_2750_);
lean_dec_ref(v_inst_2745_);
v_getRef_2751_ = lean_ctor_get(v_inst_2746_, 0);
lean_inc(v_getRef_2751_);
lean_dec_ref(v_inst_2746_);
v_toPure_2752_ = lean_ctor_get(v_toApplicative_2749_, 1);
lean_inc(v_toPure_2752_);
lean_dec_ref(v_toApplicative_2749_);
v___f_2753_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2753_, 0, v_elems_2748_);
lean_closure_set(v___f_2753_, 1, v_toPure_2752_);
lean_closure_set(v___f_2753_, 2, v_sep_2747_);
v___x_2754_ = lean_apply_4(v_toBind_2750_, lean_box(0), lean_box(0), v_getRef_2751_, v___f_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object* v_m_2755_, lean_object* v_inst_2756_, lean_object* v_inst_2757_, lean_object* v_sep_2758_, lean_object* v_elems_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(v_inst_2756_, v_inst_2757_, v_sep_2758_, v_elems_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* v_sep_2761_, lean_object* v_elems_2762_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2761_, v_elems_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* v_sep_2764_, lean_object* v_elems_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_Syntax_TSepArray_ofElems___redArg(v_sep_2764_, v_elems_2765_);
lean_dec_ref(v_elems_2765_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* v_k_2767_, lean_object* v_sep_2768_, lean_object* v_elems_2769_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2768_, v_elems_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* v_k_2771_, lean_object* v_sep_2772_, lean_object* v_elems_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Lean_Syntax_TSepArray_ofElems(v_k_2771_, v_sep_2772_, v_elems_2773_);
lean_dec_ref(v_elems_2773_);
lean_dec(v_k_2771_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* v_k_2775_, lean_object* v_sep_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(v___x_2777_, 0, v_k_2775_);
lean_closure_set(v___x_2777_, 1, v_sep_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* v_fn_2784_, lean_object* v_x_2785_){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
v___x_2786_ = lean_array_get_size(v_x_2785_);
v___x_2787_ = lean_unsigned_to_nat(0u);
v___x_2788_ = lean_nat_dec_eq(v___x_2786_, v___x_2787_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2789_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_2790_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2791_ = lean_box(2);
v___x_2792_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
lean_ctor_set(v___x_2792_, 1, v___x_2790_);
lean_ctor_set(v___x_2792_, 2, v_x_2785_);
v___x_2793_ = lean_unsigned_to_nat(2u);
v___x_2794_ = lean_mk_empty_array_with_capacity(v___x_2793_);
v___x_2795_ = lean_array_push(v___x_2794_, v_fn_2784_);
v___x_2796_ = lean_array_push(v___x_2795_, v___x_2792_);
v___x_2797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2791_);
lean_ctor_set(v___x_2797_, 1, v___x_2789_);
lean_ctor_set(v___x_2797_, 2, v___x_2796_);
return v___x_2797_;
}
else
{
lean_dec_ref(v_x_2785_);
return v_fn_2784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* v_fn_2798_, lean_object* v_args_2799_){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = l_Lean_mkCIdent(v_fn_2798_);
v___x_2801_ = l_Lean_Syntax_mkApp(v___x_2800_, v_args_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* v_kind_2802_, lean_object* v_val_2803_, lean_object* v_info_2804_){
_start:
{
lean_object* v_atom_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v_atom_2805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2805_, 0, v_info_2804_);
lean_ctor_set(v_atom_2805_, 1, v_val_2803_);
v___x_2806_ = lean_unsigned_to_nat(1u);
v___x_2807_ = lean_mk_empty_array_with_capacity(v___x_2806_);
v___x_2808_ = lean_array_push(v___x_2807_, v_atom_2805_);
v___x_2809_ = lean_box(2);
v___x_2810_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2809_);
lean_ctor_set(v___x_2810_, 1, v_kind_2802_);
lean_ctor_set(v___x_2810_, 2, v___x_2808_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t v_val_2814_, lean_object* v_info_2815_){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2816_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_2817_ = l_Char_quote(v_val_2814_);
v___x_2818_ = l_Lean_Syntax_mkLit(v___x_2816_, v___x_2817_, v_info_2815_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* v_val_2819_, lean_object* v_info_2820_){
_start:
{
uint32_t v_val_boxed_2821_; lean_object* v_res_2822_; 
v_val_boxed_2821_ = lean_unbox_uint32(v_val_2819_);
lean_dec(v_val_2819_);
v_res_2822_ = l_Lean_Syntax_mkCharLit(v_val_boxed_2821_, v_info_2820_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* v_val_2826_, lean_object* v_info_2827_){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2828_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_2829_ = l_String_quote(v_val_2826_);
v___x_2830_ = l_Lean_Syntax_mkLit(v___x_2828_, v___x_2829_, v_info_2827_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* v_val_2834_, lean_object* v_info_2835_){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2837_ = l_Lean_Syntax_mkLit(v___x_2836_, v_val_2834_, v_info_2835_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* v_val_2838_, lean_object* v_info_2839_){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2840_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2841_ = l_Nat_reprFast(v_val_2838_);
v___x_2842_ = l_Lean_Syntax_mkLit(v___x_2840_, v___x_2841_, v_info_2839_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* v_val_2846_, lean_object* v_info_2847_){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_2849_ = l_Lean_Syntax_mkLit(v___x_2848_, v_val_2846_, v_info_2847_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* v_val_2853_, lean_object* v_info_2854_){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_2856_ = l_Lean_Syntax_mkLit(v___x_2855_, v_val_2853_, v_info_2854_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* v_s_2857_, lean_object* v_i_2858_, lean_object* v_val_2859_){
_start:
{
uint8_t v___x_2860_; 
v___x_2860_ = lean_string_utf8_at_end(v_s_2857_, v_i_2858_);
if (v___x_2860_ == 0)
{
uint32_t v_c_2861_; uint32_t v___x_2862_; uint8_t v___x_2863_; 
v_c_2861_ = lean_string_utf8_get(v_s_2857_, v_i_2858_);
v___x_2862_ = 48;
v___x_2863_ = lean_uint32_dec_eq(v_c_2861_, v___x_2862_);
if (v___x_2863_ == 0)
{
uint32_t v___x_2864_; uint8_t v___x_2865_; 
v___x_2864_ = 49;
v___x_2865_ = lean_uint32_dec_eq(v_c_2861_, v___x_2864_);
if (v___x_2865_ == 0)
{
uint32_t v___x_2866_; uint8_t v___x_2867_; 
v___x_2866_ = 95;
v___x_2867_ = lean_uint32_dec_eq(v_c_2861_, v___x_2866_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; 
lean_dec(v_val_2859_);
lean_dec(v_i_2858_);
v___x_2868_ = lean_box(0);
return v___x_2868_;
}
else
{
lean_object* v___x_2869_; 
v___x_2869_ = lean_string_utf8_next(v_s_2857_, v_i_2858_);
lean_dec(v_i_2858_);
v_i_2858_ = v___x_2869_;
goto _start;
}
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2871_ = lean_string_utf8_next(v_s_2857_, v_i_2858_);
lean_dec(v_i_2858_);
v___x_2872_ = lean_unsigned_to_nat(2u);
v___x_2873_ = lean_nat_mul(v___x_2872_, v_val_2859_);
lean_dec(v_val_2859_);
v___x_2874_ = lean_unsigned_to_nat(1u);
v___x_2875_ = lean_nat_add(v___x_2873_, v___x_2874_);
lean_dec(v___x_2873_);
v_i_2858_ = v___x_2871_;
v_val_2859_ = v___x_2875_;
goto _start;
}
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = lean_string_utf8_next(v_s_2857_, v_i_2858_);
lean_dec(v_i_2858_);
v___x_2878_ = lean_unsigned_to_nat(2u);
v___x_2879_ = lean_nat_mul(v___x_2878_, v_val_2859_);
lean_dec(v_val_2859_);
v_i_2858_ = v___x_2877_;
v_val_2859_ = v___x_2879_;
goto _start;
}
}
else
{
lean_object* v___x_2881_; 
lean_dec(v_i_2858_);
v___x_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2881_, 0, v_val_2859_);
return v___x_2881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* v_s_2882_, lean_object* v_i_2883_, lean_object* v_val_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2882_, v_i_2883_, v_val_2884_);
lean_dec_ref(v_s_2882_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* v_s_2886_, lean_object* v_i_2887_, lean_object* v_val_2888_){
_start:
{
uint8_t v___x_2889_; 
v___x_2889_ = lean_string_utf8_at_end(v_s_2886_, v_i_2887_);
if (v___x_2889_ == 0)
{
uint32_t v_c_2890_; uint32_t v___x_2897_; uint8_t v___x_2898_; 
v_c_2890_ = lean_string_utf8_get(v_s_2886_, v_i_2887_);
v___x_2897_ = 48;
v___x_2898_ = lean_uint32_dec_le(v___x_2897_, v_c_2890_);
if (v___x_2898_ == 0)
{
goto v___jp_2891_;
}
else
{
uint32_t v___x_2899_; uint8_t v___x_2900_; 
v___x_2899_ = 55;
v___x_2900_ = lean_uint32_dec_le(v_c_2890_, v___x_2899_);
if (v___x_2900_ == 0)
{
goto v___jp_2891_;
}
else
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2901_ = lean_string_utf8_next(v_s_2886_, v_i_2887_);
lean_dec(v_i_2887_);
v___x_2902_ = lean_unsigned_to_nat(8u);
v___x_2903_ = lean_nat_mul(v___x_2902_, v_val_2888_);
lean_dec(v_val_2888_);
v___x_2904_ = lean_uint32_to_nat(v_c_2890_);
v___x_2905_ = lean_nat_add(v___x_2903_, v___x_2904_);
lean_dec(v___x_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_unsigned_to_nat(48u);
v___x_2907_ = lean_nat_sub(v___x_2905_, v___x_2906_);
lean_dec(v___x_2905_);
v_i_2887_ = v___x_2901_;
v_val_2888_ = v___x_2907_;
goto _start;
}
}
v___jp_2891_:
{
uint32_t v___x_2892_; uint8_t v___x_2893_; 
v___x_2892_ = 95;
v___x_2893_ = lean_uint32_dec_eq(v_c_2890_, v___x_2892_);
if (v___x_2893_ == 0)
{
lean_object* v___x_2894_; 
lean_dec(v_val_2888_);
lean_dec(v_i_2887_);
v___x_2894_ = lean_box(0);
return v___x_2894_;
}
else
{
lean_object* v___x_2895_; 
v___x_2895_ = lean_string_utf8_next(v_s_2886_, v_i_2887_);
lean_dec(v_i_2887_);
v_i_2887_ = v___x_2895_;
goto _start;
}
}
}
else
{
lean_object* v___x_2909_; 
lean_dec(v_i_2887_);
v___x_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2909_, 0, v_val_2888_);
return v___x_2909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* v_s_2910_, lean_object* v_i_2911_, lean_object* v_val_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2910_, v_i_2911_, v_val_2912_);
lean_dec_ref(v_s_2910_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object* v_s_2914_, lean_object* v_i_2915_){
_start:
{
uint32_t v_c_2916_; lean_object* v_i_2917_; uint32_t v___x_2944_; uint8_t v___x_2945_; 
v_c_2916_ = lean_string_utf8_get(v_s_2914_, v_i_2915_);
v_i_2917_ = lean_string_utf8_next(v_s_2914_, v_i_2915_);
v___x_2944_ = 48;
v___x_2945_ = lean_uint32_dec_le(v___x_2944_, v_c_2916_);
if (v___x_2945_ == 0)
{
goto v___jp_2932_;
}
else
{
uint32_t v___x_2946_; uint8_t v___x_2947_; 
v___x_2946_ = 57;
v___x_2947_ = lean_uint32_dec_le(v_c_2916_, v___x_2946_);
if (v___x_2947_ == 0)
{
goto v___jp_2932_;
}
else
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2948_ = lean_uint32_to_nat(v_c_2916_);
v___x_2949_ = lean_unsigned_to_nat(48u);
v___x_2950_ = lean_nat_sub(v___x_2948_, v___x_2949_);
lean_dec(v___x_2948_);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v_i_2917_);
v___x_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
return v___x_2952_;
}
}
v___jp_2918_:
{
uint32_t v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = 65;
v___x_2920_ = lean_uint32_dec_le(v___x_2919_, v_c_2916_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; 
lean_dec(v_i_2917_);
v___x_2921_ = lean_box(0);
return v___x_2921_;
}
else
{
uint32_t v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = 70;
v___x_2923_ = lean_uint32_dec_le(v_c_2916_, v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; 
lean_dec(v_i_2917_);
v___x_2924_ = lean_box(0);
return v___x_2924_;
}
else
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2925_ = lean_unsigned_to_nat(10u);
v___x_2926_ = lean_uint32_to_nat(v_c_2916_);
v___x_2927_ = lean_nat_add(v___x_2925_, v___x_2926_);
lean_dec(v___x_2926_);
v___x_2928_ = lean_unsigned_to_nat(65u);
v___x_2929_ = lean_nat_sub(v___x_2927_, v___x_2928_);
lean_dec(v___x_2927_);
v___x_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
lean_ctor_set(v___x_2930_, 1, v_i_2917_);
v___x_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
return v___x_2931_;
}
}
}
v___jp_2932_:
{
uint32_t v___x_2933_; uint8_t v___x_2934_; 
v___x_2933_ = 97;
v___x_2934_ = lean_uint32_dec_le(v___x_2933_, v_c_2916_);
if (v___x_2934_ == 0)
{
goto v___jp_2918_;
}
else
{
uint32_t v___x_2935_; uint8_t v___x_2936_; 
v___x_2935_ = 102;
v___x_2936_ = lean_uint32_dec_le(v_c_2916_, v___x_2935_);
if (v___x_2936_ == 0)
{
goto v___jp_2918_;
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2937_ = lean_unsigned_to_nat(10u);
v___x_2938_ = lean_uint32_to_nat(v_c_2916_);
v___x_2939_ = lean_nat_add(v___x_2937_, v___x_2938_);
lean_dec(v___x_2938_);
v___x_2940_ = lean_unsigned_to_nat(97u);
v___x_2941_ = lean_nat_sub(v___x_2939_, v___x_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v_i_2917_);
v___x_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
return v___x_2943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* v_s_2953_, lean_object* v_i_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2953_, v_i_2954_);
lean_dec(v_i_2954_);
lean_dec_ref(v_s_2953_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object* v_s_2956_, lean_object* v_i_2957_, lean_object* v_val_2958_){
_start:
{
uint8_t v___x_2959_; 
v___x_2959_ = lean_string_utf8_at_end(v_s_2956_, v_i_2957_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; 
v___x_2960_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2956_, v_i_2957_);
if (lean_obj_tag(v___x_2960_) == 0)
{
uint32_t v___x_2961_; uint32_t v___x_2962_; uint8_t v___x_2963_; 
v___x_2961_ = lean_string_utf8_get(v_s_2956_, v_i_2957_);
v___x_2962_ = 95;
v___x_2963_ = lean_uint32_dec_eq(v___x_2961_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; 
lean_dec(v_val_2958_);
lean_dec(v_i_2957_);
v___x_2964_ = lean_box(0);
return v___x_2964_;
}
else
{
lean_object* v___x_2965_; 
v___x_2965_ = lean_string_utf8_next(v_s_2956_, v_i_2957_);
lean_dec(v_i_2957_);
v_i_2957_ = v___x_2965_;
goto _start;
}
}
else
{
lean_object* v_val_2967_; lean_object* v_fst_2968_; lean_object* v_snd_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
lean_dec(v_i_2957_);
v_val_2967_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_val_2967_);
lean_dec_ref_known(v___x_2960_, 1);
v_fst_2968_ = lean_ctor_get(v_val_2967_, 0);
lean_inc(v_fst_2968_);
v_snd_2969_ = lean_ctor_get(v_val_2967_, 1);
lean_inc(v_snd_2969_);
lean_dec(v_val_2967_);
v___x_2970_ = lean_unsigned_to_nat(16u);
v___x_2971_ = lean_nat_mul(v___x_2970_, v_val_2958_);
lean_dec(v_val_2958_);
v___x_2972_ = lean_nat_add(v___x_2971_, v_fst_2968_);
lean_dec(v_fst_2968_);
lean_dec(v___x_2971_);
v_i_2957_ = v_snd_2969_;
v_val_2958_ = v___x_2972_;
goto _start;
}
}
else
{
lean_object* v___x_2974_; 
lean_dec(v_i_2957_);
v___x_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2974_, 0, v_val_2958_);
return v___x_2974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* v_s_2975_, lean_object* v_i_2976_, lean_object* v_val_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_2975_, v_i_2976_, v_val_2977_);
lean_dec_ref(v_s_2975_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object* v_s_2979_, lean_object* v_i_2980_, lean_object* v_val_2981_){
_start:
{
uint8_t v___x_2982_; 
v___x_2982_ = lean_string_utf8_at_end(v_s_2979_, v_i_2980_);
if (v___x_2982_ == 0)
{
uint32_t v_c_2983_; uint32_t v___x_2990_; uint8_t v___x_2991_; 
v_c_2983_ = lean_string_utf8_get(v_s_2979_, v_i_2980_);
v___x_2990_ = 48;
v___x_2991_ = lean_uint32_dec_le(v___x_2990_, v_c_2983_);
if (v___x_2991_ == 0)
{
goto v___jp_2984_;
}
else
{
uint32_t v___x_2992_; uint8_t v___x_2993_; 
v___x_2992_ = 57;
v___x_2993_ = lean_uint32_dec_le(v_c_2983_, v___x_2992_);
if (v___x_2993_ == 0)
{
goto v___jp_2984_;
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2994_ = lean_string_utf8_next(v_s_2979_, v_i_2980_);
lean_dec(v_i_2980_);
v___x_2995_ = lean_unsigned_to_nat(10u);
v___x_2996_ = lean_nat_mul(v___x_2995_, v_val_2981_);
lean_dec(v_val_2981_);
v___x_2997_ = lean_uint32_to_nat(v_c_2983_);
v___x_2998_ = lean_nat_add(v___x_2996_, v___x_2997_);
lean_dec(v___x_2997_);
lean_dec(v___x_2996_);
v___x_2999_ = lean_unsigned_to_nat(48u);
v___x_3000_ = lean_nat_sub(v___x_2998_, v___x_2999_);
lean_dec(v___x_2998_);
v_i_2980_ = v___x_2994_;
v_val_2981_ = v___x_3000_;
goto _start;
}
}
v___jp_2984_:
{
uint32_t v___x_2985_; uint8_t v___x_2986_; 
v___x_2985_ = 95;
v___x_2986_ = lean_uint32_dec_eq(v_c_2983_, v___x_2985_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; 
lean_dec(v_val_2981_);
lean_dec(v_i_2980_);
v___x_2987_ = lean_box(0);
return v___x_2987_;
}
else
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_string_utf8_next(v_s_2979_, v_i_2980_);
lean_dec(v_i_2980_);
v_i_2980_ = v___x_2988_;
goto _start;
}
}
}
else
{
lean_object* v___x_3002_; 
lean_dec(v_i_2980_);
v___x_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3002_, 0, v_val_2981_);
return v___x_3002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* v_s_3003_, lean_object* v_i_3004_, lean_object* v_val_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3003_, v_i_3004_, v_val_3005_);
lean_dec_ref(v_s_3003_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* v_s_3009_){
_start:
{
lean_object* v_len_3010_; lean_object* v___x_3011_; uint8_t v___x_3021_; 
v_len_3010_ = lean_string_length(v_s_3009_);
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3021_ = lean_nat_dec_eq(v_len_3010_, v___x_3011_);
if (v___x_3021_ == 0)
{
uint32_t v_c_3022_; uint32_t v___x_3023_; uint8_t v___x_3024_; 
v_c_3022_ = lean_string_utf8_get(v_s_3009_, v___x_3011_);
v___x_3023_ = 48;
v___x_3024_ = lean_uint32_dec_eq(v_c_3022_, v___x_3023_);
if (v___x_3024_ == 0)
{
uint8_t v___x_3025_; 
lean_dec(v_len_3010_);
v___x_3025_ = lean_uint32_dec_le(v___x_3023_, v_c_3022_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_box(0);
return v___x_3026_;
}
else
{
uint32_t v___x_3027_; uint8_t v___x_3028_; 
v___x_3027_ = 57;
v___x_3028_ = lean_uint32_dec_le(v_c_3022_, v___x_3027_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_box(0);
return v___x_3029_;
}
else
{
lean_object* v___x_3030_; 
v___x_3030_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3009_, v___x_3011_, v___x_3011_);
return v___x_3030_;
}
}
}
else
{
lean_object* v___x_3031_; uint8_t v___x_3032_; 
v___x_3031_ = lean_unsigned_to_nat(1u);
v___x_3032_ = lean_nat_dec_eq(v_len_3010_, v___x_3031_);
lean_dec(v_len_3010_);
if (v___x_3032_ == 0)
{
uint32_t v_c_3033_; uint32_t v___x_3034_; uint8_t v___x_3035_; 
v_c_3033_ = lean_string_utf8_get(v_s_3009_, v___x_3031_);
v___x_3034_ = 120;
v___x_3035_ = lean_uint32_dec_eq(v_c_3033_, v___x_3034_);
if (v___x_3035_ == 0)
{
uint32_t v___x_3036_; uint8_t v___x_3037_; 
v___x_3036_ = 88;
v___x_3037_ = lean_uint32_dec_eq(v_c_3033_, v___x_3036_);
if (v___x_3037_ == 0)
{
uint32_t v___x_3038_; uint8_t v___x_3039_; 
v___x_3038_ = 98;
v___x_3039_ = lean_uint32_dec_eq(v_c_3033_, v___x_3038_);
if (v___x_3039_ == 0)
{
uint32_t v___x_3040_; uint8_t v___x_3041_; 
v___x_3040_ = 66;
v___x_3041_ = lean_uint32_dec_eq(v_c_3033_, v___x_3040_);
if (v___x_3041_ == 0)
{
uint32_t v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = 111;
v___x_3043_ = lean_uint32_dec_eq(v_c_3033_, v___x_3042_);
if (v___x_3043_ == 0)
{
uint32_t v___x_3044_; uint8_t v___x_3045_; 
v___x_3044_ = 79;
v___x_3045_ = lean_uint32_dec_eq(v_c_3033_, v___x_3044_);
if (v___x_3045_ == 0)
{
uint8_t v___x_3046_; 
v___x_3046_ = lean_uint32_dec_le(v___x_3023_, v_c_3033_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; 
v___x_3047_ = lean_box(0);
return v___x_3047_;
}
else
{
uint32_t v___x_3048_; uint8_t v___x_3049_; 
v___x_3048_ = 57;
v___x_3049_ = lean_uint32_dec_le(v_c_3033_, v___x_3048_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_box(0);
return v___x_3050_;
}
else
{
lean_object* v___x_3051_; 
v___x_3051_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_3009_, v___x_3011_, v___x_3011_);
return v___x_3051_;
}
}
}
else
{
goto v___jp_3012_;
}
}
else
{
goto v___jp_3012_;
}
}
else
{
goto v___jp_3015_;
}
}
else
{
goto v___jp_3015_;
}
}
else
{
goto v___jp_3018_;
}
}
else
{
goto v___jp_3018_;
}
}
else
{
lean_object* v___x_3052_; 
v___x_3052_ = ((lean_object*)(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0));
return v___x_3052_;
}
}
}
else
{
lean_object* v___x_3053_; 
lean_dec(v_len_3010_);
v___x_3053_ = lean_box(0);
return v___x_3053_;
}
v___jp_3012_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = lean_unsigned_to_nat(2u);
v___x_3014_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_3009_, v___x_3013_, v___x_3011_);
return v___x_3014_;
}
v___jp_3015_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_unsigned_to_nat(2u);
v___x_3017_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_3009_, v___x_3016_, v___x_3011_);
return v___x_3017_;
}
v___jp_3018_:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = lean_unsigned_to_nat(2u);
v___x_3020_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_3009_, v___x_3019_, v___x_3011_);
return v___x_3020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* v_s_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_s_3054_);
lean_dec_ref(v_s_3054_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* v_litKind_3056_, lean_object* v_stx_3057_){
_start:
{
if (lean_obj_tag(v_stx_3057_) == 1)
{
lean_object* v_kind_3058_; lean_object* v_args_3059_; uint8_t v___x_3060_; 
v_kind_3058_ = lean_ctor_get(v_stx_3057_, 1);
v_args_3059_ = lean_ctor_get(v_stx_3057_, 2);
v___x_3060_ = lean_name_eq(v_kind_3058_, v_litKind_3056_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; 
v___x_3061_ = lean_box(0);
return v___x_3061_;
}
else
{
lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; 
v___x_3062_ = lean_array_get_size(v_args_3059_);
v___x_3063_ = lean_unsigned_to_nat(1u);
v___x_3064_ = lean_nat_dec_eq(v___x_3062_, v___x_3063_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; 
v___x_3065_ = lean_box(0);
return v___x_3065_;
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = lean_unsigned_to_nat(0u);
v___x_3067_ = lean_array_fget_borrowed(v_args_3059_, v___x_3066_);
if (lean_obj_tag(v___x_3067_) == 2)
{
lean_object* v_val_3068_; lean_object* v___x_3069_; 
v_val_3068_ = lean_ctor_get(v___x_3067_, 1);
lean_inc_ref(v_val_3068_);
v___x_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3069_, 0, v_val_3068_);
return v___x_3069_;
}
else
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_box(0);
return v___x_3070_;
}
}
}
}
else
{
lean_object* v___x_3071_; 
v___x_3071_ = lean_box(0);
return v___x_3071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* v_litKind_3072_, lean_object* v_stx_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_Syntax_isLit_x3f(v_litKind_3072_, v_stx_3073_);
lean_dec(v_stx_3073_);
lean_dec(v_litKind_3072_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object* v_litKind_3075_, lean_object* v_stx_3076_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Lean_Syntax_isLit_x3f(v_litKind_3075_, v_stx_3076_);
if (lean_obj_tag(v___x_3077_) == 1)
{
lean_object* v_val_3078_; lean_object* v___x_3079_; 
v_val_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_val_3078_);
lean_dec_ref_known(v___x_3077_, 1);
v___x_3079_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_val_3078_);
lean_dec(v_val_3078_);
return v___x_3079_;
}
else
{
lean_object* v___x_3080_; 
lean_dec(v___x_3077_);
v___x_3080_ = lean_box(0);
return v___x_3080_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object* v_litKind_3081_, lean_object* v_stx_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v_litKind_3081_, v_stx_3082_);
lean_dec(v_stx_3082_);
lean_dec(v_litKind_3081_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* v_s_3084_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_3086_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3085_, v_s_3084_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* v_s_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_Syntax_isNatLit_x3f(v_s_3087_);
lean_dec(v_s_3087_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* v_s_3092_){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = ((lean_object*)(l_Lean_Syntax_isFieldIdx_x3f___closed__1));
v___x_3094_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3093_, v_s_3092_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* v_s_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Lean_Syntax_isFieldIdx_x3f(v_s_3095_);
lean_dec(v_s_3095_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* v_s_3097_, lean_object* v_i_3098_, lean_object* v_val_3099_, lean_object* v_e_3100_, uint8_t v_sign_3101_, lean_object* v_exp_3102_){
_start:
{
uint8_t v___x_3103_; 
v___x_3103_ = lean_string_utf8_at_end(v_s_3097_, v_i_3098_);
if (v___x_3103_ == 0)
{
uint32_t v_c_3104_; uint32_t v___x_3111_; uint8_t v___x_3112_; 
v_c_3104_ = lean_string_utf8_get(v_s_3097_, v_i_3098_);
v___x_3111_ = 48;
v___x_3112_ = lean_uint32_dec_le(v___x_3111_, v_c_3104_);
if (v___x_3112_ == 0)
{
goto v___jp_3105_;
}
else
{
uint32_t v___x_3113_; uint8_t v___x_3114_; 
v___x_3113_ = 57;
v___x_3114_ = lean_uint32_dec_le(v_c_3104_, v___x_3113_);
if (v___x_3114_ == 0)
{
goto v___jp_3105_;
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3115_ = lean_string_utf8_next(v_s_3097_, v_i_3098_);
lean_dec(v_i_3098_);
v___x_3116_ = lean_unsigned_to_nat(10u);
v___x_3117_ = lean_nat_mul(v___x_3116_, v_exp_3102_);
lean_dec(v_exp_3102_);
v___x_3118_ = lean_uint32_to_nat(v_c_3104_);
v___x_3119_ = lean_nat_add(v___x_3117_, v___x_3118_);
lean_dec(v___x_3118_);
lean_dec(v___x_3117_);
v___x_3120_ = lean_unsigned_to_nat(48u);
v___x_3121_ = lean_nat_sub(v___x_3119_, v___x_3120_);
lean_dec(v___x_3119_);
v_i_3098_ = v___x_3115_;
v_exp_3102_ = v___x_3121_;
goto _start;
}
}
v___jp_3105_:
{
uint32_t v___x_3106_; uint8_t v___x_3107_; 
v___x_3106_ = 95;
v___x_3107_ = lean_uint32_dec_eq(v_c_3104_, v___x_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; 
lean_dec(v_exp_3102_);
lean_dec(v_val_3099_);
lean_dec(v_i_3098_);
v___x_3108_ = lean_box(0);
return v___x_3108_;
}
else
{
lean_object* v___x_3109_; 
v___x_3109_ = lean_string_utf8_next(v_s_3097_, v_i_3098_);
lean_dec(v_i_3098_);
v_i_3098_ = v___x_3109_;
goto _start;
}
}
}
else
{
lean_dec(v_i_3098_);
if (v_sign_3101_ == 0)
{
uint8_t v___x_3123_; 
v___x_3123_ = lean_nat_dec_le(v_e_3100_, v_exp_3102_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3124_ = lean_nat_sub(v_e_3100_, v_exp_3102_);
lean_dec(v_exp_3102_);
v___x_3125_ = lean_box(v___x_3103_);
v___x_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
lean_ctor_set(v___x_3126_, 1, v___x_3124_);
v___x_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3127_, 0, v_val_3099_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
v___x_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
return v___x_3128_;
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3129_ = lean_nat_sub(v_exp_3102_, v_e_3100_);
lean_dec(v_exp_3102_);
v___x_3130_ = lean_box(v_sign_3101_);
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
lean_ctor_set(v___x_3131_, 1, v___x_3129_);
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v_val_3099_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
return v___x_3133_;
}
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3134_ = lean_nat_add(v_exp_3102_, v_e_3100_);
lean_dec(v_exp_3102_);
v___x_3135_ = lean_box(v_sign_3101_);
v___x_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
lean_ctor_set(v___x_3136_, 1, v___x_3134_);
v___x_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3137_, 0, v_val_3099_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v___x_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
return v___x_3138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* v_s_3139_, lean_object* v_i_3140_, lean_object* v_val_3141_, lean_object* v_e_3142_, lean_object* v_sign_3143_, lean_object* v_exp_3144_){
_start:
{
uint8_t v_sign_boxed_3145_; lean_object* v_res_3146_; 
v_sign_boxed_3145_ = lean_unbox(v_sign_3143_);
v_res_3146_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3139_, v_i_3140_, v_val_3141_, v_e_3142_, v_sign_boxed_3145_, v_exp_3144_);
lean_dec(v_e_3142_);
lean_dec_ref(v_s_3139_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* v_s_3147_, lean_object* v_i_3148_, lean_object* v_val_3149_, lean_object* v_e_3150_){
_start:
{
uint8_t v___x_3151_; 
v___x_3151_ = lean_string_utf8_at_end(v_s_3147_, v_i_3148_);
if (v___x_3151_ == 0)
{
uint32_t v_c_3152_; uint32_t v___x_3153_; uint8_t v___x_3154_; 
v_c_3152_ = lean_string_utf8_get(v_s_3147_, v_i_3148_);
v___x_3153_ = 45;
v___x_3154_ = lean_uint32_dec_eq(v_c_3152_, v___x_3153_);
if (v___x_3154_ == 0)
{
uint32_t v___x_3155_; uint8_t v___x_3156_; 
v___x_3155_ = 43;
v___x_3156_ = lean_uint32_dec_eq(v_c_3152_, v___x_3155_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_unsigned_to_nat(0u);
v___x_3158_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3147_, v_i_3148_, v_val_3149_, v_e_3150_, v___x_3156_, v___x_3157_);
return v___x_3158_;
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = lean_string_utf8_next(v_s_3147_, v_i_3148_);
lean_dec(v_i_3148_);
v___x_3160_ = lean_unsigned_to_nat(0u);
v___x_3161_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3147_, v___x_3159_, v_val_3149_, v_e_3150_, v___x_3154_, v___x_3160_);
return v___x_3161_;
}
}
else
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3162_ = lean_string_utf8_next(v_s_3147_, v_i_3148_);
lean_dec(v_i_3148_);
v___x_3163_ = lean_unsigned_to_nat(0u);
v___x_3164_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3147_, v___x_3162_, v_val_3149_, v_e_3150_, v___x_3154_, v___x_3163_);
return v___x_3164_;
}
}
else
{
lean_object* v___x_3165_; 
lean_dec(v_val_3149_);
lean_dec(v_i_3148_);
v___x_3165_ = lean_box(0);
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* v_s_3166_, lean_object* v_i_3167_, lean_object* v_val_3168_, lean_object* v_e_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3166_, v_i_3167_, v_val_3168_, v_e_3169_);
lean_dec(v_e_3169_);
lean_dec_ref(v_s_3166_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* v_s_3171_, lean_object* v_i_3172_, lean_object* v_val_3173_, lean_object* v_e_3174_){
_start:
{
uint8_t v___x_3178_; 
v___x_3178_ = lean_string_utf8_at_end(v_s_3171_, v_i_3172_);
if (v___x_3178_ == 0)
{
uint32_t v_c_3179_; uint32_t v___x_3190_; uint8_t v___x_3191_; 
v_c_3179_ = lean_string_utf8_get(v_s_3171_, v_i_3172_);
v___x_3190_ = 48;
v___x_3191_ = lean_uint32_dec_le(v___x_3190_, v_c_3179_);
if (v___x_3191_ == 0)
{
goto v___jp_3180_;
}
else
{
uint32_t v___x_3192_; uint8_t v___x_3193_; 
v___x_3192_ = 57;
v___x_3193_ = lean_uint32_dec_le(v_c_3179_, v___x_3192_);
if (v___x_3193_ == 0)
{
goto v___jp_3180_;
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3194_ = lean_string_utf8_next(v_s_3171_, v_i_3172_);
lean_dec(v_i_3172_);
v___x_3195_ = lean_unsigned_to_nat(10u);
v___x_3196_ = lean_nat_mul(v___x_3195_, v_val_3173_);
lean_dec(v_val_3173_);
v___x_3197_ = lean_uint32_to_nat(v_c_3179_);
v___x_3198_ = lean_nat_add(v___x_3196_, v___x_3197_);
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_unsigned_to_nat(48u);
v___x_3200_ = lean_nat_sub(v___x_3198_, v___x_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_unsigned_to_nat(1u);
v___x_3202_ = lean_nat_add(v_e_3174_, v___x_3201_);
lean_dec(v_e_3174_);
v_i_3172_ = v___x_3194_;
v_val_3173_ = v___x_3200_;
v_e_3174_ = v___x_3202_;
goto _start;
}
}
v___jp_3180_:
{
uint32_t v___x_3181_; uint8_t v___x_3182_; 
v___x_3181_ = 95;
v___x_3182_ = lean_uint32_dec_eq(v_c_3179_, v___x_3181_);
if (v___x_3182_ == 0)
{
uint32_t v___x_3183_; uint8_t v___x_3184_; 
v___x_3183_ = 101;
v___x_3184_ = lean_uint32_dec_eq(v_c_3179_, v___x_3183_);
if (v___x_3184_ == 0)
{
uint32_t v___x_3185_; uint8_t v___x_3186_; 
v___x_3185_ = 69;
v___x_3186_ = lean_uint32_dec_eq(v_c_3179_, v___x_3185_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; 
lean_dec(v_e_3174_);
lean_dec(v_val_3173_);
lean_dec(v_i_3172_);
v___x_3187_ = lean_box(0);
return v___x_3187_;
}
else
{
goto v___jp_3175_;
}
}
else
{
goto v___jp_3175_;
}
}
else
{
lean_object* v___x_3188_; 
v___x_3188_ = lean_string_utf8_next(v_s_3171_, v_i_3172_);
lean_dec(v_i_3172_);
v_i_3172_ = v___x_3188_;
goto _start;
}
}
}
else
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
lean_dec(v_i_3172_);
v___x_3204_ = lean_box(v___x_3178_);
v___x_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
lean_ctor_set(v___x_3205_, 1, v_e_3174_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_val_3173_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
return v___x_3207_;
}
v___jp_3175_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = lean_string_utf8_next(v_s_3171_, v_i_3172_);
lean_dec(v_i_3172_);
v___x_3177_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3171_, v___x_3176_, v_val_3173_, v_e_3174_);
lean_dec(v_e_3174_);
return v___x_3177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* v_s_3208_, lean_object* v_i_3209_, lean_object* v_val_3210_, lean_object* v_e_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3208_, v_i_3209_, v_val_3210_, v_e_3211_);
lean_dec_ref(v_s_3208_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* v_s_3213_, lean_object* v_i_3214_, lean_object* v_val_3215_){
_start:
{
uint8_t v___x_3220_; 
v___x_3220_ = lean_string_utf8_at_end(v_s_3213_, v_i_3214_);
if (v___x_3220_ == 0)
{
uint32_t v_c_3221_; uint32_t v___x_3237_; uint8_t v___x_3238_; 
v_c_3221_ = lean_string_utf8_get(v_s_3213_, v_i_3214_);
v___x_3237_ = 48;
v___x_3238_ = lean_uint32_dec_le(v___x_3237_, v_c_3221_);
if (v___x_3238_ == 0)
{
goto v___jp_3222_;
}
else
{
uint32_t v___x_3239_; uint8_t v___x_3240_; 
v___x_3239_ = 57;
v___x_3240_ = lean_uint32_dec_le(v_c_3221_, v___x_3239_);
if (v___x_3240_ == 0)
{
goto v___jp_3222_;
}
else
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3241_ = lean_string_utf8_next(v_s_3213_, v_i_3214_);
lean_dec(v_i_3214_);
v___x_3242_ = lean_unsigned_to_nat(10u);
v___x_3243_ = lean_nat_mul(v___x_3242_, v_val_3215_);
lean_dec(v_val_3215_);
v___x_3244_ = lean_uint32_to_nat(v_c_3221_);
v___x_3245_ = lean_nat_add(v___x_3243_, v___x_3244_);
lean_dec(v___x_3244_);
lean_dec(v___x_3243_);
v___x_3246_ = lean_unsigned_to_nat(48u);
v___x_3247_ = lean_nat_sub(v___x_3245_, v___x_3246_);
lean_dec(v___x_3245_);
v_i_3214_ = v___x_3241_;
v_val_3215_ = v___x_3247_;
goto _start;
}
}
v___jp_3222_:
{
uint32_t v___x_3223_; uint8_t v___x_3224_; 
v___x_3223_ = 95;
v___x_3224_ = lean_uint32_dec_eq(v_c_3221_, v___x_3223_);
if (v___x_3224_ == 0)
{
uint32_t v___x_3225_; uint8_t v___x_3226_; 
v___x_3225_ = 46;
v___x_3226_ = lean_uint32_dec_eq(v_c_3221_, v___x_3225_);
if (v___x_3226_ == 0)
{
uint32_t v___x_3227_; uint8_t v___x_3228_; 
v___x_3227_ = 101;
v___x_3228_ = lean_uint32_dec_eq(v_c_3221_, v___x_3227_);
if (v___x_3228_ == 0)
{
uint32_t v___x_3229_; uint8_t v___x_3230_; 
v___x_3229_ = 69;
v___x_3230_ = lean_uint32_dec_eq(v_c_3221_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; 
lean_dec(v_val_3215_);
lean_dec(v_i_3214_);
v___x_3231_ = lean_box(0);
return v___x_3231_;
}
else
{
goto v___jp_3216_;
}
}
else
{
goto v___jp_3216_;
}
}
else
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = lean_string_utf8_next(v_s_3213_, v_i_3214_);
lean_dec(v_i_3214_);
v___x_3233_ = lean_unsigned_to_nat(0u);
v___x_3234_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3213_, v___x_3232_, v_val_3215_, v___x_3233_);
return v___x_3234_;
}
}
else
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_string_utf8_next(v_s_3213_, v_i_3214_);
lean_dec(v_i_3214_);
v_i_3214_ = v___x_3235_;
goto _start;
}
}
}
else
{
lean_object* v___x_3249_; 
lean_dec(v_val_3215_);
lean_dec(v_i_3214_);
v___x_3249_ = lean_box(0);
return v___x_3249_;
}
v___jp_3216_:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3217_ = lean_string_utf8_next(v_s_3213_, v_i_3214_);
lean_dec(v_i_3214_);
v___x_3218_ = lean_unsigned_to_nat(0u);
v___x_3219_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3213_, v___x_3217_, v_val_3215_, v___x_3218_);
return v___x_3219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* v_s_3250_, lean_object* v_i_3251_, lean_object* v_val_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3250_, v_i_3251_, v_val_3252_);
lean_dec_ref(v_s_3250_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* v_s_3254_){
_start:
{
lean_object* v_len_3255_; lean_object* v___x_3256_; uint8_t v___x_3257_; 
v_len_3255_ = lean_string_length(v_s_3254_);
v___x_3256_ = lean_unsigned_to_nat(0u);
v___x_3257_ = lean_nat_dec_eq(v_len_3255_, v___x_3256_);
lean_dec(v_len_3255_);
if (v___x_3257_ == 0)
{
uint32_t v_c_3258_; uint32_t v___x_3259_; uint8_t v___x_3260_; 
v_c_3258_ = lean_string_utf8_get(v_s_3254_, v___x_3256_);
v___x_3259_ = 48;
v___x_3260_ = lean_uint32_dec_le(v___x_3259_, v_c_3258_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_box(0);
return v___x_3261_;
}
else
{
uint32_t v___x_3262_; uint8_t v___x_3263_; 
v___x_3262_ = 57;
v___x_3263_ = lean_uint32_dec_le(v_c_3258_, v___x_3262_);
if (v___x_3263_ == 0)
{
lean_object* v___x_3264_; 
v___x_3264_ = lean_box(0);
return v___x_3264_;
}
else
{
lean_object* v___x_3265_; 
v___x_3265_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3254_, v___x_3256_, v___x_3256_);
return v___x_3265_;
}
}
}
else
{
lean_object* v___x_3266_; 
v___x_3266_ = lean_box(0);
return v___x_3266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* v_s_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_s_3267_);
lean_dec_ref(v_s_3267_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* v_stx_3269_){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_3271_ = l_Lean_Syntax_isLit_x3f(v___x_3270_, v_stx_3269_);
if (lean_obj_tag(v___x_3271_) == 1)
{
lean_object* v_val_3272_; lean_object* v___x_3273_; 
v_val_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_val_3272_);
lean_dec_ref_known(v___x_3271_, 1);
v___x_3273_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_val_3272_);
lean_dec(v_val_3272_);
return v___x_3273_;
}
else
{
lean_object* v___x_3274_; 
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
return v___x_3274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* v_stx_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Lean_Syntax_isScientificLit_x3f(v_stx_3275_);
lean_dec(v_stx_3275_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* v_x_3277_){
_start:
{
switch(lean_obj_tag(v_x_3277_))
{
case 2:
{
lean_object* v_val_3278_; lean_object* v___x_3279_; 
v_val_3278_ = lean_ctor_get(v_x_3277_, 1);
lean_inc_ref(v_val_3278_);
lean_dec_ref_known(v_x_3277_, 2);
v___x_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3279_, 0, v_val_3278_);
return v___x_3279_;
}
case 3:
{
lean_object* v_rawVal_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_rawVal_3280_ = lean_ctor_get(v_x_3277_, 1);
lean_inc_ref(v_rawVal_3280_);
lean_dec_ref_known(v_x_3277_, 4);
v___x_3281_ = lean_substring_tostring(v_rawVal_3280_);
v___x_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
return v___x_3282_;
}
default: 
{
lean_object* v___x_3283_; 
lean_dec(v_x_3277_);
v___x_3283_ = lean_box(0);
return v___x_3283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* v_stx_3284_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Lean_Syntax_isNatLit_x3f(v_stx_3284_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_unsigned_to_nat(0u);
return v___x_3286_;
}
else
{
lean_object* v_val_3287_; 
v_val_3287_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_val_3287_);
lean_dec_ref_known(v___x_3285_, 1);
return v_val_3287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* v_stx_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Lean_Syntax_toNat(v_stx_3288_);
lean_dec(v_stx_3288_);
return v_res_3289_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = 9;
v___x_3291_ = lean_box_uint32(v___x_3290_);
return v___x_3291_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = 10;
v___x_3293_ = lean_box_uint32(v___x_3292_);
return v___x_3293_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = 13;
v___x_3295_ = lean_box_uint32(v___x_3294_);
return v___x_3295_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = 39;
v___x_3297_ = lean_box_uint32(v___x_3296_);
return v___x_3297_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = 34;
v___x_3299_ = lean_box_uint32(v___x_3298_);
return v___x_3299_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = 92;
v___x_3301_ = lean_box_uint32(v___x_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* v_s_3302_, lean_object* v_i_3303_){
_start:
{
uint32_t v_c_3304_; lean_object* v_i_3305_; uint32_t v___x_3306_; uint8_t v___x_3307_; 
v_c_3304_ = lean_string_utf8_get(v_s_3302_, v_i_3303_);
v_i_3305_ = lean_string_utf8_next(v_s_3302_, v_i_3303_);
v___x_3306_ = 92;
v___x_3307_ = lean_uint32_dec_eq(v_c_3304_, v___x_3306_);
if (v___x_3307_ == 0)
{
uint32_t v___x_3308_; uint8_t v___x_3309_; 
v___x_3308_ = 34;
v___x_3309_ = lean_uint32_dec_eq(v_c_3304_, v___x_3308_);
if (v___x_3309_ == 0)
{
uint32_t v___x_3310_; uint8_t v___x_3311_; 
v___x_3310_ = 39;
v___x_3311_ = lean_uint32_dec_eq(v_c_3304_, v___x_3310_);
if (v___x_3311_ == 0)
{
uint32_t v___x_3312_; uint8_t v___x_3313_; 
v___x_3312_ = 114;
v___x_3313_ = lean_uint32_dec_eq(v_c_3304_, v___x_3312_);
if (v___x_3313_ == 0)
{
uint32_t v___x_3314_; uint8_t v___x_3315_; 
v___x_3314_ = 110;
v___x_3315_ = lean_uint32_dec_eq(v_c_3304_, v___x_3314_);
if (v___x_3315_ == 0)
{
uint32_t v___x_3316_; uint8_t v___x_3317_; 
v___x_3316_ = 116;
v___x_3317_ = lean_uint32_dec_eq(v_c_3304_, v___x_3316_);
if (v___x_3317_ == 0)
{
uint32_t v___x_3318_; uint8_t v___x_3319_; 
v___x_3318_ = 120;
v___x_3319_ = lean_uint32_dec_eq(v_c_3304_, v___x_3318_);
if (v___x_3319_ == 0)
{
uint32_t v___x_3320_; uint8_t v___x_3321_; 
v___x_3320_ = 117;
v___x_3321_ = lean_uint32_dec_eq(v_c_3304_, v___x_3320_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; 
lean_dec(v_i_3305_);
v___x_3322_ = lean_box(0);
return v___x_3322_;
}
else
{
lean_object* v___x_3323_; 
v___x_3323_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3302_, v_i_3305_);
lean_dec(v_i_3305_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v___x_3324_; 
v___x_3324_ = lean_box(0);
return v___x_3324_;
}
else
{
lean_object* v_val_3325_; lean_object* v_fst_3326_; lean_object* v_snd_3327_; lean_object* v___x_3328_; 
v_val_3325_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_val_3325_);
lean_dec_ref_known(v___x_3323_, 1);
v_fst_3326_ = lean_ctor_get(v_val_3325_, 0);
lean_inc(v_fst_3326_);
v_snd_3327_ = lean_ctor_get(v_val_3325_, 1);
lean_inc(v_snd_3327_);
lean_dec(v_val_3325_);
v___x_3328_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3302_, v_snd_3327_);
lean_dec(v_snd_3327_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v___x_3329_; 
lean_dec(v_fst_3326_);
v___x_3329_ = lean_box(0);
return v___x_3329_;
}
else
{
lean_object* v_val_3330_; lean_object* v_fst_3331_; lean_object* v_snd_3332_; lean_object* v___x_3333_; 
v_val_3330_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_val_3330_);
lean_dec_ref_known(v___x_3328_, 1);
v_fst_3331_ = lean_ctor_get(v_val_3330_, 0);
lean_inc(v_fst_3331_);
v_snd_3332_ = lean_ctor_get(v_val_3330_, 1);
lean_inc(v_snd_3332_);
lean_dec(v_val_3330_);
v___x_3333_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3302_, v_snd_3332_);
lean_dec(v_snd_3332_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v___x_3334_; 
lean_dec(v_fst_3331_);
lean_dec(v_fst_3326_);
v___x_3334_ = lean_box(0);
return v___x_3334_;
}
else
{
lean_object* v_val_3335_; lean_object* v_fst_3336_; lean_object* v_snd_3337_; lean_object* v___x_3338_; 
v_val_3335_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_val_3335_);
lean_dec_ref_known(v___x_3333_, 1);
v_fst_3336_ = lean_ctor_get(v_val_3335_, 0);
lean_inc(v_fst_3336_);
v_snd_3337_ = lean_ctor_get(v_val_3335_, 1);
lean_inc(v_snd_3337_);
lean_dec(v_val_3335_);
v___x_3338_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3302_, v_snd_3337_);
lean_dec(v_snd_3337_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v___x_3339_; 
lean_dec(v_fst_3336_);
lean_dec(v_fst_3331_);
lean_dec(v_fst_3326_);
v___x_3339_ = lean_box(0);
return v___x_3339_;
}
else
{
lean_object* v_val_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3365_; 
v_val_3340_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3342_ = v___x_3338_;
v_isShared_3343_ = v_isSharedCheck_3365_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_val_3340_);
lean_dec(v___x_3338_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3365_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v_fst_3344_; lean_object* v_snd_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3364_; 
v_fst_3344_ = lean_ctor_get(v_val_3340_, 0);
v_snd_3345_ = lean_ctor_get(v_val_3340_, 1);
v_isSharedCheck_3364_ = !lean_is_exclusive(v_val_3340_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3347_ = v_val_3340_;
v_isShared_3348_ = v_isSharedCheck_3364_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_snd_3345_);
lean_inc(v_fst_3344_);
lean_dec(v_val_3340_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3364_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; uint32_t v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3359_; 
v___x_3349_ = lean_unsigned_to_nat(16u);
v___x_3350_ = lean_nat_mul(v___x_3349_, v_fst_3326_);
lean_dec(v_fst_3326_);
v___x_3351_ = lean_nat_add(v___x_3350_, v_fst_3331_);
lean_dec(v_fst_3331_);
lean_dec(v___x_3350_);
v___x_3352_ = lean_nat_mul(v___x_3349_, v___x_3351_);
lean_dec(v___x_3351_);
v___x_3353_ = lean_nat_add(v___x_3352_, v_fst_3336_);
lean_dec(v_fst_3336_);
lean_dec(v___x_3352_);
v___x_3354_ = lean_nat_mul(v___x_3349_, v___x_3353_);
lean_dec(v___x_3353_);
v___x_3355_ = lean_nat_add(v___x_3354_, v_fst_3344_);
lean_dec(v_fst_3344_);
lean_dec(v___x_3354_);
v___x_3356_ = l_Char_ofNat(v___x_3355_);
lean_dec(v___x_3355_);
v___x_3357_ = lean_box_uint32(v___x_3356_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 0, v___x_3357_);
v___x_3359_ = v___x_3347_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_snd_3345_);
v___x_3359_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3361_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 0, v___x_3359_);
v___x_3361_ = v___x_3342_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3359_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
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
lean_object* v___x_3366_; 
v___x_3366_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3302_, v_i_3305_);
lean_dec(v_i_3305_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v___x_3367_; 
v___x_3367_ = lean_box(0);
return v___x_3367_;
}
else
{
lean_object* v_val_3368_; lean_object* v_fst_3369_; lean_object* v_snd_3370_; lean_object* v___x_3371_; 
v_val_3368_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_val_3368_);
lean_dec_ref_known(v___x_3366_, 1);
v_fst_3369_ = lean_ctor_get(v_val_3368_, 0);
lean_inc(v_fst_3369_);
v_snd_3370_ = lean_ctor_get(v_val_3368_, 1);
lean_inc(v_snd_3370_);
lean_dec(v_val_3368_);
v___x_3371_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3302_, v_snd_3370_);
lean_dec(v_snd_3370_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v___x_3372_; 
lean_dec(v_fst_3369_);
v___x_3372_ = lean_box(0);
return v___x_3372_;
}
else
{
lean_object* v_val_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3394_; 
v_val_3373_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3375_ = v___x_3371_;
v_isShared_3376_ = v_isSharedCheck_3394_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_val_3373_);
lean_dec(v___x_3371_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3394_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v_fst_3377_; lean_object* v_snd_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3393_; 
v_fst_3377_ = lean_ctor_get(v_val_3373_, 0);
v_snd_3378_ = lean_ctor_get(v_val_3373_, 1);
v_isSharedCheck_3393_ = !lean_is_exclusive(v_val_3373_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3380_ = v_val_3373_;
v_isShared_3381_ = v_isSharedCheck_3393_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_snd_3378_);
lean_inc(v_fst_3377_);
lean_dec(v_val_3373_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3393_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; uint32_t v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3382_ = lean_unsigned_to_nat(16u);
v___x_3383_ = lean_nat_mul(v___x_3382_, v_fst_3369_);
lean_dec(v_fst_3369_);
v___x_3384_ = lean_nat_add(v___x_3383_, v_fst_3377_);
lean_dec(v_fst_3377_);
lean_dec(v___x_3383_);
v___x_3385_ = l_Char_ofNat(v___x_3384_);
lean_dec(v___x_3384_);
v___x_3386_ = lean_box_uint32(v___x_3385_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v___x_3386_);
v___x_3388_ = v___x_3380_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_snd_3378_);
v___x_3388_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
lean_object* v___x_3390_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3388_);
v___x_3390_ = v___x_3375_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3388_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
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
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3395_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
lean_ctor_set(v___x_3396_, 1, v_i_3305_);
v___x_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
return v___x_3397_;
}
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3398_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
v___x_3399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
lean_ctor_set(v___x_3399_, 1, v_i_3305_);
v___x_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
return v___x_3400_;
}
}
else
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3401_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
v___x_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_ctor_set(v___x_3402_, 1, v_i_3305_);
v___x_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
return v___x_3403_;
}
}
else
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3404_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
v___x_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
lean_ctor_set(v___x_3405_, 1, v_i_3305_);
v___x_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
return v___x_3406_;
}
}
else
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3407_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
v___x_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
lean_ctor_set(v___x_3408_, 1, v_i_3305_);
v___x_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3408_);
return v___x_3409_;
}
}
else
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3410_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
v___x_3411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
lean_ctor_set(v___x_3411_, 1, v_i_3305_);
v___x_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
return v___x_3412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* v_s_3413_, lean_object* v_i_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_Lean_Syntax_decodeQuotedChar(v_s_3413_, v_i_3414_);
lean_dec(v_i_3414_);
lean_dec_ref(v_s_3413_);
return v_res_3415_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t v___y_3416_){
_start:
{
uint32_t v___x_3417_; uint8_t v___x_3418_; 
v___x_3417_ = 32;
v___x_3418_ = lean_uint32_dec_eq(v___y_3416_, v___x_3417_);
if (v___x_3418_ == 0)
{
uint32_t v___x_3419_; uint8_t v___x_3420_; 
v___x_3419_ = 9;
v___x_3420_ = lean_uint32_dec_eq(v___y_3416_, v___x_3419_);
if (v___x_3420_ == 0)
{
uint32_t v___x_3421_; uint8_t v___x_3422_; 
v___x_3421_ = 13;
v___x_3422_ = lean_uint32_dec_eq(v___y_3416_, v___x_3421_);
if (v___x_3422_ == 0)
{
uint32_t v___x_3423_; uint8_t v___x_3424_; 
v___x_3423_ = 10;
v___x_3424_ = lean_uint32_dec_eq(v___y_3416_, v___x_3423_);
return v___x_3424_;
}
else
{
return v___x_3422_;
}
}
else
{
return v___x_3420_;
}
}
else
{
return v___x_3418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* v___y_3425_){
_start:
{
uint32_t v___y_270__boxed_3426_; uint8_t v_res_3427_; lean_object* v_r_3428_; 
v___y_270__boxed_3426_ = lean_unbox_uint32(v___y_3425_);
lean_dec(v___y_3425_);
v_res_3427_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_270__boxed_3426_);
v_r_3428_ = lean_box(v_res_3427_);
return v_r_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* v_s_3430_, lean_object* v_i_3431_){
_start:
{
lean_object* v___f_3432_; uint32_t v___x_3437_; uint32_t v___x_3438_; uint8_t v___x_3439_; 
v___f_3432_ = ((lean_object*)(l_Lean_Syntax_decodeStringGap___closed__0));
v___x_3437_ = lean_string_utf8_get(v_s_3430_, v_i_3431_);
v___x_3438_ = 32;
v___x_3439_ = lean_uint32_dec_eq(v___x_3437_, v___x_3438_);
if (v___x_3439_ == 0)
{
uint32_t v___x_3440_; uint8_t v___x_3441_; 
v___x_3440_ = 9;
v___x_3441_ = lean_uint32_dec_eq(v___x_3437_, v___x_3440_);
if (v___x_3441_ == 0)
{
uint32_t v___x_3442_; uint8_t v___x_3443_; 
v___x_3442_ = 13;
v___x_3443_ = lean_uint32_dec_eq(v___x_3437_, v___x_3442_);
if (v___x_3443_ == 0)
{
uint32_t v___x_3444_; uint8_t v___x_3445_; 
v___x_3444_ = 10;
v___x_3445_ = lean_uint32_dec_eq(v___x_3437_, v___x_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; 
lean_dec_ref(v_s_3430_);
v___x_3446_ = lean_box(0);
return v___x_3446_;
}
else
{
goto v___jp_3433_;
}
}
else
{
goto v___jp_3433_;
}
}
else
{
goto v___jp_3433_;
}
}
else
{
goto v___jp_3433_;
}
v___jp_3433_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3434_ = lean_string_utf8_next(v_s_3430_, v_i_3431_);
v___x_3435_ = lean_string_nextwhile(v_s_3430_, v___f_3432_, v___x_3434_);
v___x_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
return v___x_3436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* v_s_3447_, lean_object* v_i_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_Syntax_decodeStringGap(v_s_3447_, v_i_3448_);
lean_dec(v_i_3448_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* v_s_3450_, lean_object* v_i_3451_, lean_object* v_acc_3452_){
_start:
{
uint32_t v_c_3453_; uint32_t v___x_3454_; uint8_t v___x_3455_; 
v_c_3453_ = lean_string_utf8_get(v_s_3450_, v_i_3451_);
v___x_3454_ = 34;
v___x_3455_ = lean_uint32_dec_eq(v_c_3453_, v___x_3454_);
if (v___x_3455_ == 0)
{
lean_object* v_i_3456_; uint8_t v___x_3457_; 
v_i_3456_ = lean_string_utf8_next(v_s_3450_, v_i_3451_);
lean_dec(v_i_3451_);
v___x_3457_ = lean_string_utf8_at_end(v_s_3450_, v_i_3456_);
if (v___x_3457_ == 0)
{
uint32_t v___x_3458_; uint8_t v___x_3459_; 
v___x_3458_ = 92;
v___x_3459_ = lean_uint32_dec_eq(v_c_3453_, v___x_3458_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_string_push(v_acc_3452_, v_c_3453_);
v_i_3451_ = v_i_3456_;
v_acc_3452_ = v___x_3460_;
goto _start;
}
else
{
lean_object* v___x_3462_; 
v___x_3462_ = l_Lean_Syntax_decodeQuotedChar(v_s_3450_, v_i_3456_);
if (lean_obj_tag(v___x_3462_) == 1)
{
lean_object* v_val_3463_; lean_object* v_fst_3464_; lean_object* v_snd_3465_; uint32_t v___x_3466_; lean_object* v___x_3467_; 
lean_dec(v_i_3456_);
v_val_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_val_3463_);
lean_dec_ref_known(v___x_3462_, 1);
v_fst_3464_ = lean_ctor_get(v_val_3463_, 0);
lean_inc(v_fst_3464_);
v_snd_3465_ = lean_ctor_get(v_val_3463_, 1);
lean_inc(v_snd_3465_);
lean_dec(v_val_3463_);
v___x_3466_ = lean_unbox_uint32(v_fst_3464_);
lean_dec(v_fst_3464_);
v___x_3467_ = lean_string_push(v_acc_3452_, v___x_3466_);
v_i_3451_ = v_snd_3465_;
v_acc_3452_ = v___x_3467_;
goto _start;
}
else
{
lean_object* v___x_3469_; 
lean_dec(v___x_3462_);
lean_inc_ref(v_s_3450_);
v___x_3469_ = l_Lean_Syntax_decodeStringGap(v_s_3450_, v_i_3456_);
lean_dec(v_i_3456_);
if (lean_obj_tag(v___x_3469_) == 1)
{
lean_object* v_val_3470_; 
v_val_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_val_3470_);
lean_dec_ref_known(v___x_3469_, 1);
v_i_3451_ = v_val_3470_;
goto _start;
}
else
{
lean_object* v___x_3472_; 
lean_dec(v___x_3469_);
lean_dec_ref(v_acc_3452_);
lean_dec_ref(v_s_3450_);
v___x_3472_ = lean_box(0);
return v___x_3472_;
}
}
}
}
else
{
lean_object* v___x_3473_; 
lean_dec(v_i_3456_);
lean_dec_ref(v_acc_3452_);
lean_dec_ref(v_s_3450_);
v___x_3473_ = lean_box(0);
return v___x_3473_;
}
}
else
{
lean_object* v___x_3474_; 
lean_dec(v_i_3451_);
lean_dec_ref(v_s_3450_);
v___x_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3474_, 0, v_acc_3452_);
return v___x_3474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* v_s_3475_, lean_object* v_i_3476_, lean_object* v_num_3477_){
_start:
{
uint32_t v_c_3478_; lean_object* v_i_3479_; uint32_t v___x_3480_; uint8_t v___x_3481_; 
v_c_3478_ = lean_string_utf8_get(v_s_3475_, v_i_3476_);
v_i_3479_ = lean_string_utf8_next(v_s_3475_, v_i_3476_);
lean_dec(v_i_3476_);
v___x_3480_ = 35;
v___x_3481_ = lean_uint32_dec_eq(v_c_3478_, v___x_3480_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3482_ = lean_string_utf8_byte_size(v_s_3475_);
v___x_3483_ = lean_unsigned_to_nat(1u);
v___x_3484_ = lean_nat_add(v_num_3477_, v___x_3483_);
lean_dec(v_num_3477_);
v___x_3485_ = lean_nat_sub(v___x_3482_, v___x_3484_);
lean_dec(v___x_3484_);
v___x_3486_ = lean_string_utf8_extract(v_s_3475_, v_i_3479_, v___x_3485_);
lean_dec(v___x_3485_);
lean_dec(v_i_3479_);
return v___x_3486_;
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = lean_unsigned_to_nat(1u);
v___x_3488_ = lean_nat_add(v_num_3477_, v___x_3487_);
lean_dec(v_num_3477_);
v_i_3476_ = v_i_3479_;
v_num_3477_ = v___x_3488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* v_s_3490_, lean_object* v_i_3491_, lean_object* v_num_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3490_, v_i_3491_, v_num_3492_);
lean_dec_ref(v_s_3490_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* v_s_3494_){
_start:
{
lean_object* v___x_3495_; uint32_t v___x_3496_; uint32_t v___x_3497_; uint8_t v___x_3498_; 
v___x_3495_ = lean_unsigned_to_nat(0u);
v___x_3496_ = lean_string_utf8_get(v_s_3494_, v___x_3495_);
v___x_3497_ = 114;
v___x_3498_ = lean_uint32_dec_eq(v___x_3496_, v___x_3497_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3499_ = lean_unsigned_to_nat(1u);
v___x_3500_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_3501_ = l_Lean_Syntax_decodeStrLitAux(v_s_3494_, v___x_3499_, v___x_3500_);
return v___x_3501_;
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3502_ = lean_unsigned_to_nat(1u);
v___x_3503_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3494_, v___x_3502_, v___x_3495_);
lean_dec_ref(v_s_3494_);
v___x_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
return v___x_3504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* v_stx_3505_){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_3507_ = l_Lean_Syntax_isLit_x3f(v___x_3506_, v_stx_3505_);
if (lean_obj_tag(v___x_3507_) == 1)
{
lean_object* v_val_3508_; lean_object* v___x_3509_; 
v_val_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_val_3508_);
lean_dec_ref_known(v___x_3507_, 1);
v___x_3509_ = l_Lean_Syntax_decodeStrLit(v_val_3508_);
return v___x_3509_;
}
else
{
lean_object* v___x_3510_; 
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
return v___x_3510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* v_stx_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_Syntax_isStrLit_x3f(v_stx_3511_);
lean_dec(v_stx_3511_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* v_s_3513_){
_start:
{
lean_object* v___x_3514_; uint32_t v_c_3515_; uint32_t v___x_3516_; uint8_t v___x_3517_; 
v___x_3514_ = lean_unsigned_to_nat(1u);
v_c_3515_ = lean_string_utf8_get(v_s_3513_, v___x_3514_);
v___x_3516_ = 92;
v___x_3517_ = lean_uint32_dec_eq(v_c_3515_, v___x_3516_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = lean_box_uint32(v_c_3515_);
v___x_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
return v___x_3519_;
}
else
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = lean_unsigned_to_nat(2u);
v___x_3521_ = l_Lean_Syntax_decodeQuotedChar(v_s_3513_, v___x_3520_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v___x_3522_; 
v___x_3522_ = lean_box(0);
return v___x_3522_;
}
else
{
lean_object* v_val_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3531_; 
v_val_3523_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3525_ = v___x_3521_;
v_isShared_3526_ = v_isSharedCheck_3531_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_val_3523_);
lean_dec(v___x_3521_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3531_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v_fst_3527_; lean_object* v___x_3529_; 
v_fst_3527_ = lean_ctor_get(v_val_3523_, 0);
lean_inc(v_fst_3527_);
lean_dec(v_val_3523_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v_fst_3527_);
v___x_3529_ = v___x_3525_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_fst_3527_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* v_s_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_Syntax_decodeCharLit(v_s_3532_);
lean_dec_ref(v_s_3532_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* v_stx_3534_){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_3536_ = l_Lean_Syntax_isLit_x3f(v___x_3535_, v_stx_3534_);
if (lean_obj_tag(v___x_3536_) == 1)
{
lean_object* v_val_3537_; lean_object* v___x_3538_; 
v_val_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_val_3537_);
lean_dec_ref_known(v___x_3536_, 1);
v___x_3538_ = l_Lean_Syntax_decodeCharLit(v_val_3537_);
lean_dec(v_val_3537_);
return v___x_3538_;
}
else
{
lean_object* v___x_3539_; 
lean_dec(v___x_3536_);
v___x_3539_ = lean_box(0);
return v___x_3539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* v_stx_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_Syntax_isCharLit_x3f(v_stx_3540_);
lean_dec(v_stx_3540_);
return v_res_3541_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t v___y_3542_){
_start:
{
uint32_t v___x_3564_; uint8_t v___x_3565_; 
v___x_3564_ = 65;
v___x_3565_ = lean_uint32_dec_le(v___x_3564_, v___y_3542_);
if (v___x_3565_ == 0)
{
goto v___jp_3559_;
}
else
{
uint32_t v___x_3566_; uint8_t v___x_3567_; 
v___x_3566_ = 90;
v___x_3567_ = lean_uint32_dec_le(v___y_3542_, v___x_3566_);
if (v___x_3567_ == 0)
{
goto v___jp_3559_;
}
else
{
return v___x_3567_;
}
}
v___jp_3543_:
{
uint32_t v___x_3544_; uint8_t v___x_3545_; 
v___x_3544_ = 95;
v___x_3545_ = lean_uint32_dec_eq(v___y_3542_, v___x_3544_);
if (v___x_3545_ == 0)
{
uint32_t v___x_3546_; uint8_t v___x_3547_; 
v___x_3546_ = 39;
v___x_3547_ = lean_uint32_dec_eq(v___y_3542_, v___x_3546_);
if (v___x_3547_ == 0)
{
uint32_t v___x_3548_; uint8_t v___x_3549_; 
v___x_3548_ = 33;
v___x_3549_ = lean_uint32_dec_eq(v___y_3542_, v___x_3548_);
if (v___x_3549_ == 0)
{
uint32_t v___x_3550_; uint8_t v___x_3551_; 
v___x_3550_ = 63;
v___x_3551_ = lean_uint32_dec_eq(v___y_3542_, v___x_3550_);
if (v___x_3551_ == 0)
{
uint8_t v___x_3552_; 
v___x_3552_ = l_Lean_isLetterLike(v___y_3542_);
if (v___x_3552_ == 0)
{
uint8_t v___x_3553_; 
v___x_3553_ = l_Lean_isSubScriptAlnum(v___y_3542_);
return v___x_3553_;
}
else
{
return v___x_3552_;
}
}
else
{
return v___x_3551_;
}
}
else
{
return v___x_3549_;
}
}
else
{
return v___x_3547_;
}
}
else
{
return v___x_3545_;
}
}
v___jp_3554_:
{
uint32_t v___x_3555_; uint8_t v___x_3556_; 
v___x_3555_ = 48;
v___x_3556_ = lean_uint32_dec_le(v___x_3555_, v___y_3542_);
if (v___x_3556_ == 0)
{
goto v___jp_3543_;
}
else
{
uint32_t v___x_3557_; uint8_t v___x_3558_; 
v___x_3557_ = 57;
v___x_3558_ = lean_uint32_dec_le(v___y_3542_, v___x_3557_);
if (v___x_3558_ == 0)
{
goto v___jp_3543_;
}
else
{
return v___x_3558_;
}
}
}
v___jp_3559_:
{
uint32_t v___x_3560_; uint8_t v___x_3561_; 
v___x_3560_ = 97;
v___x_3561_ = lean_uint32_dec_le(v___x_3560_, v___y_3542_);
if (v___x_3561_ == 0)
{
goto v___jp_3554_;
}
else
{
uint32_t v___x_3562_; uint8_t v___x_3563_; 
v___x_3562_ = 122;
v___x_3563_ = lean_uint32_dec_le(v___y_3542_, v___x_3562_);
if (v___x_3563_ == 0)
{
goto v___jp_3554_;
}
else
{
return v___x_3563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* v___y_3568_){
_start:
{
uint32_t v___y_513__boxed_3569_; uint8_t v_res_3570_; lean_object* v_r_3571_; 
v___y_513__boxed_3569_ = lean_unbox_uint32(v___y_3568_);
lean_dec(v___y_3568_);
v_res_3570_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_513__boxed_3569_);
v_r_3571_ = lean_box(v_res_3570_);
return v_r_3571_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t v___x_3572_, uint32_t v___x_3573_, uint32_t v___y_3574_){
_start:
{
uint8_t v___x_3575_; 
v___x_3575_ = lean_uint32_dec_le(v___x_3572_, v___y_3574_);
if (v___x_3575_ == 0)
{
return v___x_3575_;
}
else
{
uint8_t v___x_3576_; 
v___x_3576_ = lean_uint32_dec_le(v___y_3574_, v___x_3573_);
return v___x_3576_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* v___x_3577_, lean_object* v___x_3578_, lean_object* v___y_3579_){
_start:
{
uint32_t v___x_566__boxed_3580_; uint32_t v___x_567__boxed_3581_; uint32_t v___y_568__boxed_3582_; uint8_t v_res_3583_; lean_object* v_r_3584_; 
v___x_566__boxed_3580_ = lean_unbox_uint32(v___x_3577_);
lean_dec(v___x_3577_);
v___x_567__boxed_3581_ = lean_unbox_uint32(v___x_3578_);
lean_dec(v___x_3578_);
v___y_568__boxed_3582_ = lean_unbox_uint32(v___y_3579_);
lean_dec(v___y_3579_);
v_res_3583_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___x_566__boxed_3580_, v___x_567__boxed_3581_, v___y_568__boxed_3582_);
v_r_3584_ = lean_box(v_res_3583_);
return v_r_3584_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t v___x_3585_, uint8_t v___x_3586_, uint32_t v_x_3587_){
_start:
{
uint32_t v___x_3588_; uint8_t v___x_3589_; 
v___x_3588_ = 187;
v___x_3589_ = lean_uint32_dec_eq(v_x_3587_, v___x_3588_);
if (v___x_3589_ == 0)
{
return v___x_3585_;
}
else
{
return v___x_3586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* v___x_3590_, lean_object* v___x_3591_, lean_object* v_x_3592_){
_start:
{
uint8_t v___x_579__boxed_3593_; uint8_t v___x_580__boxed_3594_; uint32_t v_x_581__boxed_3595_; uint8_t v_res_3596_; lean_object* v_r_3597_; 
v___x_579__boxed_3593_ = lean_unbox(v___x_3590_);
v___x_580__boxed_3594_ = lean_unbox(v___x_3591_);
v_x_581__boxed_3595_ = lean_unbox_uint32(v_x_3592_);
lean_dec(v_x_3592_);
v_res_3596_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v___x_579__boxed_3593_, v___x_580__boxed_3594_, v_x_581__boxed_3595_);
v_r_3597_ = lean_box(v_res_3596_);
return v_r_3597_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = 48;
v___x_3600_ = lean_box_uint32(v___x_3599_);
return v___x_3600_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2(void){
_start:
{
uint32_t v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = 57;
v___x_3602_ = lean_box_uint32(v___x_3601_);
return v___x_3602_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1(void){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___f_3605_; 
v___x_3603_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1;
v___x_3604_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2;
v___f_3605_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3605_, 0, v___x_3603_);
lean_closure_set(v___f_3605_, 1, v___x_3604_);
return v___f_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* v_ss_3606_, lean_object* v_acc_3607_){
_start:
{
lean_object* v_ss_3609_; lean_object* v_acc_3610_; uint8_t v___x_3619_; 
lean_inc_ref(v_ss_3606_);
v___x_3619_ = lean_substring_isempty(v_ss_3606_);
if (v___x_3619_ == 0)
{
uint32_t v_curr_3620_; uint32_t v___x_3621_; uint8_t v___x_3622_; 
lean_inc_ref(v_ss_3606_);
v_curr_3620_ = lean_substring_front(v_ss_3606_);
v___x_3621_ = 171;
v___x_3622_ = lean_uint32_dec_eq(v_curr_3620_, v___x_3621_);
if (v___x_3622_ == 0)
{
lean_object* v___f_3623_; uint32_t v___x_3659_; uint8_t v___x_3660_; 
v___f_3623_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0));
v___x_3659_ = 65;
v___x_3660_ = lean_uint32_dec_le(v___x_3659_, v_curr_3620_);
if (v___x_3660_ == 0)
{
goto v___jp_3654_;
}
else
{
uint32_t v___x_3661_; uint8_t v___x_3662_; 
v___x_3661_ = 90;
v___x_3662_ = lean_uint32_dec_le(v_curr_3620_, v___x_3661_);
if (v___x_3662_ == 0)
{
goto v___jp_3654_;
}
else
{
goto v___jp_3624_;
}
}
v___jp_3624_:
{
lean_object* v_idPart_3625_; lean_object* v_startPos_3626_; lean_object* v_stopPos_3627_; lean_object* v_startPos_3628_; lean_object* v_stopPos_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
lean_inc_ref(v_ss_3606_);
v_idPart_3625_ = lean_substring_takewhile(v_ss_3606_, v___f_3623_);
v_startPos_3626_ = lean_ctor_get(v_idPart_3625_, 1);
v_stopPos_3627_ = lean_ctor_get(v_idPart_3625_, 2);
v_startPos_3628_ = lean_ctor_get(v_ss_3606_, 1);
v_stopPos_3629_ = lean_ctor_get(v_ss_3606_, 2);
v___x_3630_ = lean_nat_sub(v_stopPos_3627_, v_startPos_3626_);
v___x_3631_ = lean_nat_sub(v_stopPos_3629_, v_startPos_3628_);
v___x_3632_ = lean_substring_extract(v_ss_3606_, v___x_3630_, v___x_3631_);
v___x_3633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3633_, 0, v_idPart_3625_);
lean_ctor_set(v___x_3633_, 1, v_acc_3607_);
v_ss_3609_ = v___x_3632_;
v_acc_3610_ = v___x_3633_;
goto v___jp_3608_;
}
v___jp_3634_:
{
uint32_t v___x_3635_; uint8_t v___x_3636_; 
v___x_3635_ = 95;
v___x_3636_ = lean_uint32_dec_eq(v_curr_3620_, v___x_3635_);
if (v___x_3636_ == 0)
{
uint8_t v___x_3637_; 
v___x_3637_ = l_Lean_isLetterLike(v_curr_3620_);
if (v___x_3637_ == 0)
{
uint32_t v___x_3638_; uint8_t v___x_3639_; 
v___x_3638_ = 48;
v___x_3639_ = lean_uint32_dec_le(v___x_3638_, v_curr_3620_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; 
lean_dec(v_acc_3607_);
lean_dec_ref(v_ss_3606_);
v___x_3640_ = lean_box(0);
return v___x_3640_;
}
else
{
uint32_t v___x_3641_; uint8_t v___x_3642_; 
v___x_3641_ = 57;
v___x_3642_ = lean_uint32_dec_le(v_curr_3620_, v___x_3641_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3643_; 
lean_dec(v_acc_3607_);
lean_dec_ref(v_ss_3606_);
v___x_3643_ = lean_box(0);
return v___x_3643_;
}
else
{
lean_object* v___f_3644_; lean_object* v_idPart_3645_; lean_object* v_startPos_3646_; lean_object* v_stopPos_3647_; lean_object* v_startPos_3648_; lean_object* v_stopPos_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___f_3644_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1, &l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1);
lean_inc_ref(v_ss_3606_);
v_idPart_3645_ = lean_substring_takewhile(v_ss_3606_, v___f_3644_);
v_startPos_3646_ = lean_ctor_get(v_idPart_3645_, 1);
v_stopPos_3647_ = lean_ctor_get(v_idPart_3645_, 2);
v_startPos_3648_ = lean_ctor_get(v_ss_3606_, 1);
v_stopPos_3649_ = lean_ctor_get(v_ss_3606_, 2);
v___x_3650_ = lean_nat_sub(v_stopPos_3647_, v_startPos_3646_);
v___x_3651_ = lean_nat_sub(v_stopPos_3649_, v_startPos_3648_);
v___x_3652_ = lean_substring_extract(v_ss_3606_, v___x_3650_, v___x_3651_);
v___x_3653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3653_, 0, v_idPart_3645_);
lean_ctor_set(v___x_3653_, 1, v_acc_3607_);
v_ss_3609_ = v___x_3652_;
v_acc_3610_ = v___x_3653_;
goto v___jp_3608_;
}
}
}
else
{
goto v___jp_3624_;
}
}
else
{
goto v___jp_3624_;
}
}
v___jp_3654_:
{
uint32_t v___x_3655_; uint8_t v___x_3656_; 
v___x_3655_ = 97;
v___x_3656_ = lean_uint32_dec_le(v___x_3655_, v_curr_3620_);
if (v___x_3656_ == 0)
{
goto v___jp_3634_;
}
else
{
uint32_t v___x_3657_; uint8_t v___x_3658_; 
v___x_3657_ = 122;
v___x_3658_ = lean_uint32_dec_le(v_curr_3620_, v___x_3657_);
if (v___x_3658_ == 0)
{
goto v___jp_3634_;
}
else
{
goto v___jp_3624_;
}
}
}
}
else
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___f_3665_; lean_object* v_escapedPart_3666_; lean_object* v_str_3667_; lean_object* v_startPos_3668_; lean_object* v_stopPos_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3689_; 
v___x_3663_ = lean_box(v___x_3622_);
v___x_3664_ = lean_box(v___x_3619_);
v___f_3665_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3665_, 0, v___x_3663_);
lean_closure_set(v___f_3665_, 1, v___x_3664_);
lean_inc_ref(v_ss_3606_);
v_escapedPart_3666_ = lean_substring_takewhile(v_ss_3606_, v___f_3665_);
v_str_3667_ = lean_ctor_get(v_escapedPart_3666_, 0);
v_startPos_3668_ = lean_ctor_get(v_escapedPart_3666_, 1);
v_stopPos_3669_ = lean_ctor_get(v_escapedPart_3666_, 2);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_escapedPart_3666_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3671_ = v_escapedPart_3666_;
v_isShared_3672_ = v_isSharedCheck_3689_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_stopPos_3669_);
lean_inc(v_startPos_3668_);
lean_inc(v_str_3667_);
lean_dec(v_escapedPart_3666_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3689_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v_startPos_3673_; lean_object* v_stopPos_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v_escapedPart_3678_; 
v_startPos_3673_ = lean_ctor_get(v_ss_3606_, 1);
v_stopPos_3674_ = lean_ctor_get(v_ss_3606_, 2);
v___x_3675_ = lean_string_utf8_next(v_str_3667_, v_stopPos_3669_);
lean_dec(v_stopPos_3669_);
lean_inc(v_stopPos_3674_);
v___x_3676_ = lean_string_pos_min(v_stopPos_3674_, v___x_3675_);
lean_inc(v___x_3676_);
lean_inc(v_startPos_3668_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 2, v___x_3676_);
v_escapedPart_3678_ = v___x_3671_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_str_3667_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_startPos_3668_);
lean_ctor_set(v_reuseFailAlloc_3688_, 2, v___x_3676_);
v_escapedPart_3678_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; uint32_t v___x_3681_; uint32_t v___x_3682_; uint8_t v___x_3683_; 
v___x_3679_ = lean_nat_sub(v___x_3676_, v_startPos_3668_);
lean_dec(v_startPos_3668_);
lean_dec(v___x_3676_);
lean_inc(v___x_3679_);
lean_inc_ref_n(v_escapedPart_3678_, 2);
v___x_3680_ = lean_substring_prev(v_escapedPart_3678_, v___x_3679_);
v___x_3681_ = lean_substring_get(v_escapedPart_3678_, v___x_3680_);
v___x_3682_ = 187;
v___x_3683_ = lean_uint32_dec_eq(v___x_3681_, v___x_3682_);
if (v___x_3683_ == 0)
{
lean_object* v___x_3684_; 
lean_dec(v___x_3679_);
lean_dec_ref(v_escapedPart_3678_);
lean_dec(v_acc_3607_);
lean_dec_ref(v_ss_3606_);
v___x_3684_ = lean_box(0);
return v___x_3684_;
}
else
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3685_ = lean_nat_sub(v_stopPos_3674_, v_startPos_3673_);
v___x_3686_ = lean_substring_extract(v_ss_3606_, v___x_3679_, v___x_3685_);
v___x_3687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3687_, 0, v_escapedPart_3678_);
lean_ctor_set(v___x_3687_, 1, v_acc_3607_);
v_ss_3609_ = v___x_3686_;
v_acc_3610_ = v___x_3687_;
goto v___jp_3608_;
}
}
}
}
}
else
{
lean_object* v___x_3690_; 
lean_dec(v_acc_3607_);
lean_dec_ref(v_ss_3606_);
v___x_3690_ = lean_box(0);
return v___x_3690_;
}
v___jp_3608_:
{
uint32_t v___x_3611_; uint32_t v___x_3612_; uint8_t v___x_3613_; 
lean_inc_ref(v_ss_3609_);
v___x_3611_ = lean_substring_front(v_ss_3609_);
v___x_3612_ = 46;
v___x_3613_ = lean_uint32_dec_eq(v___x_3611_, v___x_3612_);
if (v___x_3613_ == 0)
{
uint8_t v___x_3614_; 
v___x_3614_ = lean_substring_isempty(v_ss_3609_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; 
lean_dec(v_acc_3610_);
v___x_3615_ = lean_box(0);
return v___x_3615_;
}
else
{
return v_acc_3610_;
}
}
else
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3616_ = lean_unsigned_to_nat(1u);
v___x_3617_ = lean_substring_drop(v_ss_3609_, v___x_3616_);
v_ss_3606_ = v___x_3617_;
v_acc_3607_ = v_acc_3610_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* v_ss_3691_){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3692_ = lean_box(0);
v___x_3693_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_ss_3691_, v___x_3692_);
v___x_3694_ = l_List_reverse___redArg(v___x_3693_);
return v___x_3694_;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3698_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3699_ = lean_unsigned_to_nat(10u);
v___x_3700_ = lean_unsigned_to_nat(1257u);
v___x_3701_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3702_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3703_ = l_mkPanicMessageWithDecl(v___x_3702_, v___x_3701_, v___x_3700_, v___x_3699_, v___x_3698_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object* v_init_3704_, lean_object* v_x_3705_){
_start:
{
if (lean_obj_tag(v_x_3705_) == 0)
{
lean_inc(v_init_3704_);
return v_init_3704_;
}
else
{
lean_object* v_head_3706_; lean_object* v_tail_3707_; lean_object* v___x_3708_; lean_object* v_comp_3709_; uint32_t v___x_3710_; uint32_t v___x_3711_; uint8_t v___x_3712_; 
v_head_3706_ = lean_ctor_get(v_x_3705_, 0);
lean_inc(v_head_3706_);
v_tail_3707_ = lean_ctor_get(v_x_3705_, 1);
lean_inc(v_tail_3707_);
lean_dec_ref_known(v_x_3705_, 2);
v___x_3708_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3704_, v_tail_3707_);
v_comp_3709_ = lean_substring_tostring(v_head_3706_);
lean_inc_ref(v_comp_3709_);
v___x_3710_ = lean_string_front(v_comp_3709_);
v___x_3711_ = 171;
v___x_3712_ = lean_uint32_dec_eq(v___x_3710_, v___x_3711_);
if (v___x_3712_ == 0)
{
uint32_t v___x_3713_; uint8_t v___x_3714_; 
v___x_3713_ = 48;
v___x_3714_ = lean_uint32_dec_le(v___x_3713_, v___x_3710_);
if (v___x_3714_ == 0)
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_Name_str___override(v___x_3708_, v_comp_3709_);
return v___x_3715_;
}
else
{
uint32_t v___x_3716_; uint8_t v___x_3717_; 
v___x_3716_ = 57;
v___x_3717_ = lean_uint32_dec_le(v___x_3710_, v___x_3716_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lean_Name_str___override(v___x_3708_, v_comp_3709_);
return v___x_3718_;
}
else
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3709_);
lean_dec_ref(v_comp_3709_);
if (lean_obj_tag(v___x_3719_) == 1)
{
lean_object* v_val_3720_; lean_object* v___x_3721_; 
v_val_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_val_3720_);
lean_dec_ref_known(v___x_3719_, 1);
v___x_3721_ = l_Lean_Name_num___override(v___x_3708_, v_val_3720_);
return v___x_3721_;
}
else
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
lean_dec(v___x_3719_);
lean_dec(v___x_3708_);
v___x_3722_ = lean_obj_once(&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3, &l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3723_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3722_);
return v___x_3723_;
}
}
}
}
else
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3724_ = lean_unsigned_to_nat(1u);
v___x_3725_ = lean_string_drop(v_comp_3709_, v___x_3724_);
v___x_3726_ = lean_string_dropright(v___x_3725_, v___x_3724_);
v___x_3727_ = l_Lean_Name_str___override(v___x_3708_, v___x_3726_);
return v___x_3727_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_init_3728_, lean_object* v_x_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3728_, v_x_3729_);
lean_dec(v_init_3728_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3731_){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = lean_box(0);
v___x_3733_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3731_, v___x_3732_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_box(0);
return v___x_3734_;
}
else
{
lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3735_ = lean_box(0);
v___x_3736_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v___x_3735_, v___x_3733_);
return v___x_3736_;
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3737_){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3738_ = lean_unsigned_to_nat(0u);
v___x_3739_ = lean_string_utf8_byte_size(v_s_3737_);
v___x_3740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3740_, 0, v_s_3737_);
lean_ctor_set(v___x_3740_, 1, v___x_3738_);
lean_ctor_set(v___x_3740_, 2, v___x_3739_);
v___x_3741_ = l_Substring_Raw_toName(v___x_3740_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3742_){
_start:
{
lean_object* v___x_3743_; uint32_t v___x_3744_; uint32_t v___x_3745_; uint8_t v___x_3746_; 
v___x_3743_ = lean_unsigned_to_nat(0u);
v___x_3744_ = lean_string_utf8_get(v_s_3742_, v___x_3743_);
v___x_3745_ = 96;
v___x_3746_ = lean_uint32_dec_eq(v___x_3744_, v___x_3745_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3747_; 
lean_dec_ref(v_s_3742_);
v___x_3747_ = lean_box(0);
return v___x_3747_;
}
else
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3748_ = lean_string_utf8_byte_size(v_s_3742_);
v___x_3749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3749_, 0, v_s_3742_);
lean_ctor_set(v___x_3749_, 1, v___x_3743_);
lean_ctor_set(v___x_3749_, 2, v___x_3748_);
v___x_3750_ = lean_unsigned_to_nat(1u);
v___x_3751_ = lean_substring_drop(v___x_3749_, v___x_3750_);
v___x_3752_ = l_Substring_Raw_toName(v___x_3751_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v___x_3753_; 
v___x_3753_ = lean_box(0);
return v___x_3753_;
}
else
{
lean_object* v___x_3754_; 
v___x_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3752_);
return v___x_3754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3755_){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3756_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3757_ = l_Lean_Syntax_isLit_x3f(v___x_3756_, v_stx_3755_);
if (lean_obj_tag(v___x_3757_) == 1)
{
lean_object* v_val_3758_; lean_object* v___x_3759_; 
v_val_3758_ = lean_ctor_get(v___x_3757_, 0);
lean_inc(v_val_3758_);
lean_dec_ref_known(v___x_3757_, 1);
v___x_3759_ = l_Lean_Syntax_decodeNameLit(v_val_3758_);
return v___x_3759_;
}
else
{
lean_object* v___x_3760_; 
lean_dec(v___x_3757_);
v___x_3760_ = lean_box(0);
return v___x_3760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3761_);
lean_dec(v_stx_3761_);
return v_res_3762_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3763_){
_start:
{
if (lean_obj_tag(v_x_3763_) == 1)
{
lean_object* v_args_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; uint8_t v___x_3767_; 
v_args_3764_ = lean_ctor_get(v_x_3763_, 2);
v___x_3765_ = lean_unsigned_to_nat(0u);
v___x_3766_ = lean_array_get_size(v_args_3764_);
v___x_3767_ = lean_nat_dec_lt(v___x_3765_, v___x_3766_);
return v___x_3767_;
}
else
{
uint8_t v___x_3768_; 
v___x_3768_ = 0;
return v___x_3768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3769_){
_start:
{
uint8_t v_res_3770_; lean_object* v_r_3771_; 
v_res_3770_ = l_Lean_Syntax_hasArgs(v_x_3769_);
lean_dec(v_x_3769_);
v_r_3771_ = lean_box(v_res_3770_);
return v_r_3771_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3772_){
_start:
{
if (lean_obj_tag(v_x_3772_) == 2)
{
uint8_t v___x_3773_; 
v___x_3773_ = 1;
return v___x_3773_;
}
else
{
uint8_t v___x_3774_; 
v___x_3774_ = 0;
return v___x_3774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3775_){
_start:
{
uint8_t v_res_3776_; lean_object* v_r_3777_; 
v_res_3776_ = l_Lean_Syntax_isAtom(v_x_3775_);
lean_dec(v_x_3775_);
v_r_3777_ = lean_box(v_res_3776_);
return v_r_3777_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3778_, lean_object* v_x_3779_){
_start:
{
if (lean_obj_tag(v_x_3779_) == 2)
{
lean_object* v_val_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v_val_3780_ = lean_ctor_get(v_x_3779_, 1);
lean_inc_ref(v_val_3780_);
lean_dec_ref_known(v_x_3779_, 2);
v___x_3781_ = lean_string_trim(v_val_3780_);
v___x_3782_ = lean_string_trim(v_token_3778_);
v___x_3783_ = lean_string_dec_eq(v___x_3781_, v___x_3782_);
lean_dec_ref(v___x_3782_);
lean_dec_ref(v___x_3781_);
return v___x_3783_;
}
else
{
uint8_t v___x_3784_; 
lean_dec(v_x_3779_);
lean_dec_ref(v_token_3778_);
v___x_3784_ = 0;
return v___x_3784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3785_, lean_object* v_x_3786_){
_start:
{
uint8_t v_res_3787_; lean_object* v_r_3788_; 
v_res_3787_ = l_Lean_Syntax_isToken(v_token_3785_, v_x_3786_);
v_r_3788_ = lean_box(v_res_3787_);
return v_r_3788_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3789_){
_start:
{
switch(lean_obj_tag(v_stx_3789_))
{
case 1:
{
lean_object* v_kind_3790_; lean_object* v_args_3791_; lean_object* v___x_3792_; uint8_t v___x_3793_; 
v_kind_3790_ = lean_ctor_get(v_stx_3789_, 1);
v_args_3791_ = lean_ctor_get(v_stx_3789_, 2);
v___x_3792_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3793_ = lean_name_eq(v_kind_3790_, v___x_3792_);
if (v___x_3793_ == 0)
{
return v___x_3793_;
}
else
{
lean_object* v___x_3794_; lean_object* v___x_3795_; uint8_t v___x_3796_; 
v___x_3794_ = lean_array_get_size(v_args_3791_);
v___x_3795_ = lean_unsigned_to_nat(0u);
v___x_3796_ = lean_nat_dec_eq(v___x_3794_, v___x_3795_);
return v___x_3796_;
}
}
case 0:
{
uint8_t v___x_3797_; 
v___x_3797_ = 1;
return v___x_3797_;
}
default: 
{
uint8_t v___x_3798_; 
v___x_3798_ = 0;
return v___x_3798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3799_){
_start:
{
uint8_t v_res_3800_; lean_object* v_r_3801_; 
v_res_3800_ = l_Lean_Syntax_isNone(v_stx_3799_);
lean_dec(v_stx_3799_);
v_r_3801_ = lean_box(v_res_3800_);
return v_r_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3802_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Lean_Syntax_getOptional_x3f(v_stx_3802_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v___x_3804_; 
v___x_3804_ = lean_box(0);
return v___x_3804_;
}
else
{
lean_object* v_val_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3813_; 
v_val_3805_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3807_ = v___x_3803_;
v_isShared_3808_ = v_isSharedCheck_3813_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_val_3805_);
lean_dec(v___x_3803_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3813_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3809_; lean_object* v___x_3811_; 
v___x_3809_ = l_Lean_Syntax_getId(v_val_3805_);
lean_dec(v_val_3805_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3809_);
v___x_3811_ = v___x_3807_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3809_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3814_);
lean_dec(v_stx_3814_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3816_, lean_object* v_x_3817_){
_start:
{
if (lean_obj_tag(v_x_3817_) == 1)
{
lean_object* v_args_3818_; lean_object* v___x_3819_; uint8_t v___x_3820_; 
v_args_3818_ = lean_ctor_get(v_x_3817_, 2);
lean_inc_ref(v_p_3816_);
lean_inc_ref(v_x_3817_);
v___x_3819_ = lean_apply_1(v_p_3816_, v_x_3817_);
v___x_3820_ = lean_unbox(v___x_3819_);
if (v___x_3820_ == 0)
{
lean_object* v___x_3821_; lean_object* v___x_3822_; size_t v_sz_3823_; size_t v___x_3824_; lean_object* v___x_3825_; lean_object* v_fst_3826_; 
lean_inc_ref(v_args_3818_);
lean_dec_ref_known(v_x_3817_, 3);
v___x_3821_ = lean_box(0);
v___x_3822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3823_ = lean_array_size(v_args_3818_);
v___x_3824_ = ((size_t)0ULL);
v___x_3825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3816_, v_args_3818_, v_sz_3823_, v___x_3824_, v___x_3822_);
lean_dec_ref(v_args_3818_);
v_fst_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_fst_3826_);
lean_dec_ref(v___x_3825_);
if (lean_obj_tag(v_fst_3826_) == 0)
{
return v___x_3821_;
}
else
{
lean_object* v_val_3827_; 
v_val_3827_ = lean_ctor_get(v_fst_3826_, 0);
lean_inc(v_val_3827_);
lean_dec_ref_known(v_fst_3826_, 1);
return v_val_3827_;
}
}
else
{
lean_object* v___x_3828_; 
lean_dec_ref(v_p_3816_);
v___x_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3828_, 0, v_x_3817_);
return v___x_3828_;
}
}
else
{
lean_object* v___x_3829_; uint8_t v___x_3830_; 
lean_inc(v_x_3817_);
v___x_3829_ = lean_apply_1(v_p_3816_, v_x_3817_);
v___x_3830_ = lean_unbox(v___x_3829_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; 
lean_dec(v_x_3817_);
v___x_3831_ = lean_box(0);
return v___x_3831_;
}
else
{
lean_object* v___x_3832_; 
v___x_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3832_, 0, v_x_3817_);
return v___x_3832_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3833_, lean_object* v_as_3834_, size_t v_sz_3835_, size_t v_i_3836_, lean_object* v_b_3837_){
_start:
{
uint8_t v___x_3838_; 
v___x_3838_ = lean_usize_dec_lt(v_i_3836_, v_sz_3835_);
if (v___x_3838_ == 0)
{
lean_dec_ref(v_p_3833_);
lean_inc_ref(v_b_3837_);
return v_b_3837_;
}
else
{
lean_object* v___x_3839_; lean_object* v_a_3840_; lean_object* v___x_3841_; 
v___x_3839_ = lean_box(0);
v_a_3840_ = lean_array_uget_borrowed(v_as_3834_, v_i_3836_);
lean_inc(v_a_3840_);
lean_inc_ref(v_p_3833_);
v___x_3841_ = l_Lean_Syntax_findAux(v_p_3833_, v_a_3840_);
if (lean_obj_tag(v___x_3841_) == 1)
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
lean_dec_ref(v_p_3833_);
v___x_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3841_);
v___x_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
lean_ctor_set(v___x_3843_, 1, v___x_3839_);
return v___x_3843_;
}
else
{
lean_object* v___x_3844_; size_t v___x_3845_; size_t v___x_3846_; 
lean_dec(v___x_3841_);
v___x_3844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3845_ = ((size_t)1ULL);
v___x_3846_ = lean_usize_add(v_i_3836_, v___x_3845_);
v_i_3836_ = v___x_3846_;
v_b_3837_ = v___x_3844_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3848_, lean_object* v_as_3849_, lean_object* v_sz_3850_, lean_object* v_i_3851_, lean_object* v_b_3852_){
_start:
{
size_t v_sz_boxed_3853_; size_t v_i_boxed_3854_; lean_object* v_res_3855_; 
v_sz_boxed_3853_ = lean_unbox_usize(v_sz_3850_);
lean_dec(v_sz_3850_);
v_i_boxed_3854_ = lean_unbox_usize(v_i_3851_);
lean_dec(v_i_3851_);
v_res_3855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3848_, v_as_3849_, v_sz_boxed_3853_, v_i_boxed_3854_, v_b_3852_);
lean_dec_ref(v_b_3852_);
lean_dec_ref(v_as_3849_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3856_, lean_object* v_p_3857_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_Syntax_findAux(v_p_3857_, v_stx_3856_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3859_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l_Lean_Syntax_isNatLit_x3f(v_s_3859_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_unsigned_to_nat(0u);
return v___x_3861_;
}
else
{
lean_object* v_val_3862_; 
v_val_3862_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_val_3862_);
lean_dec_ref_known(v___x_3860_, 1);
return v_val_3862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Lean_TSyntax_getNat(v_s_3863_);
lean_dec(v_s_3863_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3868_){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3870_ = l_Lean_Syntax_isLit_x3f(v___x_3869_, v_stx_3868_);
if (lean_obj_tag(v___x_3870_) == 1)
{
lean_object* v_val_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v_val_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_val_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v___x_3872_ = lean_unsigned_to_nat(0u);
v___x_3873_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3871_, v___x_3872_, v___x_3872_);
lean_dec(v_val_3871_);
return v___x_3873_;
}
else
{
lean_object* v___x_3874_; 
lean_dec(v___x_3870_);
v___x_3874_ = lean_box(0);
return v___x_3874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3875_);
lean_dec(v_stx_3875_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3877_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3877_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v___x_3879_; 
v___x_3879_ = lean_unsigned_to_nat(0u);
return v___x_3879_;
}
else
{
lean_object* v_val_3880_; 
v_val_3880_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_val_3880_);
lean_dec_ref_known(v___x_3878_, 1);
return v_val_3880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_Lean_TSyntax_getHexNumVal(v_s_3881_);
lean_dec(v_s_3881_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3883_, lean_object* v_p_3884_, lean_object* v_n_3885_){
_start:
{
uint8_t v___x_3886_; 
v___x_3886_ = lean_string_utf8_at_end(v_s_3883_, v_p_3884_);
if (v___x_3886_ == 0)
{
lean_object* v___x_3887_; uint32_t v___x_3888_; uint32_t v___x_3889_; uint8_t v___x_3890_; 
v___x_3887_ = lean_string_utf8_next(v_s_3883_, v_p_3884_);
v___x_3888_ = lean_string_utf8_get(v_s_3883_, v_p_3884_);
lean_dec(v_p_3884_);
v___x_3889_ = 95;
v___x_3890_ = lean_uint32_dec_eq(v___x_3888_, v___x_3889_);
if (v___x_3890_ == 0)
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = lean_unsigned_to_nat(1u);
v___x_3892_ = lean_nat_add(v_n_3885_, v___x_3891_);
lean_dec(v_n_3885_);
v_p_3884_ = v___x_3887_;
v_n_3885_ = v___x_3892_;
goto _start;
}
else
{
v_p_3884_ = v___x_3887_;
goto _start;
}
}
else
{
lean_dec(v_p_3884_);
return v_n_3885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3895_, lean_object* v_p_3896_, lean_object* v_n_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3895_, v_p_3896_, v_n_3897_);
lean_dec_ref(v_s_3895_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3899_){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3901_ = l_Lean_Syntax_isLit_x3f(v___x_3900_, v_s_3899_);
if (lean_obj_tag(v___x_3901_) == 1)
{
lean_object* v_val_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v_val_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_val_3902_);
lean_dec_ref_known(v___x_3901_, 1);
v___x_3903_ = lean_unsigned_to_nat(0u);
v___x_3904_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3902_, v___x_3903_, v___x_3903_);
lean_dec(v_val_3902_);
return v___x_3904_;
}
else
{
lean_object* v___x_3905_; 
lean_dec(v___x_3901_);
v___x_3905_ = lean_unsigned_to_nat(0u);
return v___x_3905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lean_TSyntax_getHexNumSize(v_s_3906_);
lean_dec(v_s_3906_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3908_){
_start:
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Lean_Syntax_getId(v_s_3908_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_TSyntax_getId(v_s_3910_);
lean_dec(v_s_3910_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_3919_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Lean_Syntax_isScientificLit_x3f(v_s_3919_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v___x_3921_; 
v___x_3921_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
return v___x_3921_;
}
else
{
lean_object* v_val_3922_; 
v_val_3922_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_val_3922_);
lean_dec_ref_known(v___x_3920_, 1);
return v_val_3922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l_Lean_TSyntax_getScientific(v_s_3923_);
lean_dec(v_s_3923_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_3925_){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l_Lean_Syntax_isStrLit_x3f(v_s_3925_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v___x_3927_; 
v___x_3927_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_3927_;
}
else
{
lean_object* v_val_3928_; 
v_val_3928_ = lean_ctor_get(v___x_3926_, 0);
lean_inc(v_val_3928_);
lean_dec_ref_known(v___x_3926_, 1);
return v_val_3928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l_Lean_TSyntax_getString(v_s_3929_);
lean_dec(v_s_3929_);
return v_res_3930_;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_3931_){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = l_Lean_Syntax_isCharLit_x3f(v_s_3931_);
if (lean_obj_tag(v___x_3932_) == 0)
{
uint32_t v___x_3933_; 
v___x_3933_ = 65;
return v___x_3933_;
}
else
{
lean_object* v_val_3934_; uint32_t v___x_3935_; 
v_val_3934_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_val_3934_);
lean_dec_ref_known(v___x_3932_, 1);
v___x_3935_ = lean_unbox_uint32(v_val_3934_);
lean_dec(v_val_3934_);
return v___x_3935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_3936_){
_start:
{
uint32_t v_res_3937_; lean_object* v_r_3938_; 
v_res_3937_ = l_Lean_TSyntax_getChar(v_s_3936_);
lean_dec(v_s_3936_);
v_r_3938_ = lean_box_uint32(v_res_3937_);
return v_r_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_3939_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l_Lean_Syntax_isNameLit_x3f(v_s_3939_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v___x_3941_; 
v___x_3941_ = lean_box(0);
return v___x_3941_;
}
else
{
lean_object* v_val_3942_; 
v_val_3942_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_val_3942_);
lean_dec_ref_known(v___x_3940_, 1);
return v_val_3942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_Lean_TSyntax_getName(v_s_3943_);
lean_dec(v_s_3943_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_3945_){
_start:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3946_ = lean_unsigned_to_nat(0u);
v___x_3947_ = l_Lean_Syntax_getArg(v_s_3945_, v___x_3946_);
v___x_3948_ = l_Lean_Syntax_getId(v___x_3947_);
lean_dec(v___x_3947_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l_Lean_TSyntax_getHygieneInfo(v_s_3949_);
lean_dec(v_s_3949_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_3951_, lean_object* v_a_3952_){
_start:
{
lean_object* v___x_3953_; 
v___x_3953_ = l_Lean_Syntax_SepArray_ofElems(v_sep_3951_, v_a_3952_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_3954_, lean_object* v_a_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_3954_, v_a_3955_);
lean_dec_ref(v_a_3955_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_3957_){
_start:
{
lean_object* v___f_3958_; 
v___f_3958_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3958_, 0, v_sep_3957_);
return v___f_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_3959_, lean_object* v_sep_3960_){
_start:
{
lean_object* v___f_3961_; 
v___f_3961_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3961_, 0, v_sep_3960_);
return v___f_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_3962_, lean_object* v_sep_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_3962_, v_sep_3963_);
lean_dec(v_k_3962_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_3965_, lean_object* v_val_3966_, uint8_t v_canonical_3967_){
_start:
{
lean_object* v___x_3968_; lean_object* v_src_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v_imported_3972_; lean_object* v_ctx_3973_; lean_object* v_scopes_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3990_; 
v___x_3968_ = lean_unsigned_to_nat(0u);
v_src_3969_ = l_Lean_Syntax_getArg(v_s_3965_, v___x_3968_);
v___x_3970_ = l_Lean_Syntax_getId(v_src_3969_);
v___x_3971_ = l_Lean_extractMacroScopes(v___x_3970_);
v_imported_3972_ = lean_ctor_get(v___x_3971_, 1);
v_ctx_3973_ = lean_ctor_get(v___x_3971_, 2);
v_scopes_3974_ = lean_ctor_get(v___x_3971_, 3);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_3990_ == 0)
{
lean_object* v_unused_3991_; 
v_unused_3991_ = lean_ctor_get(v___x_3971_, 0);
lean_dec(v_unused_3991_);
v___x_3976_ = v___x_3971_;
v_isShared_3977_ = v_isSharedCheck_3990_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_scopes_3974_);
lean_inc(v_ctx_3973_);
lean_inc(v_imported_3972_);
lean_dec(v___x_3971_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3990_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3978_; lean_object* v___x_3980_; 
v___x_3978_ = l_Lean_Name_eraseMacroScopes(v_val_3966_);
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 0, v___x_3978_);
v___x_3980_ = v___x_3976_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3978_);
lean_ctor_set(v_reuseFailAlloc_3989_, 1, v_imported_3972_);
lean_ctor_set(v_reuseFailAlloc_3989_, 2, v_ctx_3973_);
lean_ctor_set(v_reuseFailAlloc_3989_, 3, v_scopes_3974_);
v___x_3980_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
lean_object* v_id_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v_id_3981_ = l_Lean_MacroScopesView_review(v___x_3980_);
v___x_3982_ = l_Lean_SourceInfo_fromRef(v_src_3969_, v_canonical_3967_);
lean_dec(v_src_3969_);
v___x_3983_ = 1;
v___x_3984_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_3966_, v___x_3983_);
v___x_3985_ = lean_string_utf8_byte_size(v___x_3984_);
v___x_3986_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3984_);
lean_ctor_set(v___x_3986_, 1, v___x_3968_);
lean_ctor_set(v___x_3986_, 2, v___x_3985_);
v___x_3987_ = lean_box(0);
v___x_3988_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3982_);
lean_ctor_set(v___x_3988_, 1, v___x_3986_);
lean_ctor_set(v___x_3988_, 2, v_id_3981_);
lean_ctor_set(v___x_3988_, 3, v___x_3987_);
return v___x_3988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_3992_, lean_object* v_val_3993_, lean_object* v_canonical_3994_){
_start:
{
uint8_t v_canonical_boxed_3995_; lean_object* v_res_3996_; 
v_canonical_boxed_3995_ = lean_unbox(v_canonical_3994_);
v_res_3996_ = l_Lean_HygieneInfo_mkIdent(v_s_3992_, v_val_3993_, v_canonical_boxed_3995_);
lean_dec(v_s_3992_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_3997_, lean_object* v_inst_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_4000_ = lean_apply_1(v_inst_3997_, v_a_3999_);
v___x_4001_ = lean_apply_1(v_inst_3998_, v___x_4000_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_4002_, lean_object* v_inst_4003_){
_start:
{
lean_object* v___f_4004_; 
v___f_4004_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4004_, 0, v_inst_4002_);
lean_closure_set(v___f_4004_, 1, v_inst_4003_);
return v___f_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_4005_, lean_object* v_k_4006_, lean_object* v_k_x27_4007_, lean_object* v_inst_4008_, lean_object* v_inst_4009_){
_start:
{
lean_object* v___f_4010_; 
v___f_4010_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4010_, 0, v_inst_4008_);
lean_closure_set(v___f_4010_, 1, v_inst_4009_);
return v___f_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_4011_, lean_object* v_k_4012_, lean_object* v_k_x27_4013_, lean_object* v_inst_4014_, lean_object* v_inst_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_4011_, v_k_4012_, v_k_x27_4013_, v_inst_4014_, v_inst_4015_);
lean_dec(v_k_x27_4013_);
lean_dec(v_k_4012_);
return v_res_4016_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4025_ = l_Lean_mkCIdent(v___x_4024_);
return v___x_4025_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4030_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4031_ = l_Lean_mkCIdent(v___x_4030_);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4032_){
_start:
{
if (v_x_4032_ == 0)
{
lean_object* v___x_4033_; 
v___x_4033_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4033_;
}
else
{
lean_object* v___x_4034_; 
v___x_4034_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4035_){
_start:
{
uint8_t v_x_85__boxed_4036_; lean_object* v_res_4037_; 
v_x_85__boxed_4036_ = lean_unbox(v_x_4035_);
v_res_4037_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4036_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4040_){
_start:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = lean_box(2);
v___x_4042_ = l_Lean_Syntax_mkCharLit(v_val_4040_, v___x_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4043_){
_start:
{
uint32_t v_val_boxed_4044_; lean_object* v_res_4045_; 
v_val_boxed_4044_ = lean_unbox_uint32(v_val_4043_);
lean_dec(v_val_4043_);
v_res_4045_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4044_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4048_){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4049_ = lean_box(2);
v___x_4050_ = l_Lean_Syntax_mkStrLit(v_val_4048_, v___x_4049_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4053_){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4054_ = l_Nat_reprFast(v_n_4053_);
v___x_4055_ = lean_box(2);
v___x_4056_ = l_Lean_Syntax_mkNumLit(v___x_4054_, v___x_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4064_){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4065_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4066_ = lean_substring_tostring(v_s_4064_);
v___x_4067_ = lean_box(2);
v___x_4068_ = l_Lean_Syntax_mkStrLit(v___x_4066_, v___x_4067_);
v___x_4069_ = lean_unsigned_to_nat(1u);
v___x_4070_ = lean_mk_empty_array_with_capacity(v___x_4069_);
v___x_4071_ = lean_array_push(v___x_4070_, v___x_4068_);
v___x_4072_ = l_Lean_Syntax_mkCApp(v___x_4065_, v___x_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4075_, lean_object* v_x_4076_){
_start:
{
switch(lean_obj_tag(v_x_4076_))
{
case 0:
{
uint8_t v___x_4077_; 
v___x_4077_ = l_List_isEmpty___redArg(v_acc_4075_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4078_; 
v___x_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4078_, 0, v_acc_4075_);
return v___x_4078_;
}
else
{
lean_object* v___x_4079_; 
lean_dec(v_acc_4075_);
v___x_4079_ = lean_box(0);
return v___x_4079_;
}
}
case 1:
{
lean_object* v_pre_4080_; lean_object* v_str_4081_; lean_object* v_val_4083_; lean_object* v___x_4086_; lean_object* v___x_4087_; uint8_t v___x_4088_; 
v_pre_4080_ = lean_ctor_get(v_x_4076_, 0);
lean_inc(v_pre_4080_);
v_str_4081_ = lean_ctor_get(v_x_4076_, 1);
lean_inc_ref(v_str_4081_);
lean_dec_ref_known(v_x_4076_, 2);
v___x_4086_ = lean_unsigned_to_nat(0u);
v___x_4087_ = lean_string_utf8_byte_size(v_str_4081_);
v___x_4088_ = lean_nat_dec_lt(v___x_4086_, v___x_4087_);
if (v___x_4088_ == 0)
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4089_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_4090_ = lean_string_append(v___x_4089_, v_str_4081_);
lean_dec_ref(v_str_4081_);
v___x_4091_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_4092_ = lean_string_append(v___x_4090_, v___x_4091_);
v_val_4083_ = v___x_4092_;
goto v___jp_4082_;
}
else
{
lean_object* v___f_4093_; lean_object* v___f_4101_; uint32_t v___y_4108_; uint32_t v___y_4113_; uint8_t v_c_4127_; uint8_t v___x_4136_; uint8_t v___x_4137_; 
v___f_4093_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v___f_4101_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_4127_ = lean_string_get_byte_fast(v_str_4081_, v___x_4086_);
v___x_4136_ = 97;
v___x_4137_ = lean_uint8_dec_le(v___x_4136_, v_c_4127_);
if (v___x_4137_ == 0)
{
goto v___jp_4131_;
}
else
{
uint8_t v___x_4138_; uint8_t v___x_4139_; 
v___x_4138_ = 122;
v___x_4139_ = lean_uint8_dec_le(v_c_4127_, v___x_4138_);
if (v___x_4139_ == 0)
{
goto v___jp_4131_;
}
else
{
goto v___jp_4124_;
}
}
v___jp_4094_:
{
uint8_t v___x_4095_; 
lean_inc_ref(v_str_4081_);
v___x_4095_ = lean_string_any(v_str_4081_, v___f_4093_);
if (v___x_4095_ == 0)
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4096_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0));
v___x_4097_ = lean_string_append(v___x_4096_, v_str_4081_);
lean_dec_ref(v_str_4081_);
v___x_4098_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1));
v___x_4099_ = lean_string_append(v___x_4097_, v___x_4098_);
v_val_4083_ = v___x_4099_;
goto v___jp_4082_;
}
else
{
lean_object* v___x_4100_; 
lean_dec_ref(v_str_4081_);
lean_dec(v_pre_4080_);
lean_dec(v_acc_4075_);
v___x_4100_ = lean_box(0);
return v___x_4100_;
}
}
v___jp_4102_:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; uint8_t v___x_4106_; 
lean_inc_ref(v_str_4081_);
v___x_4103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4103_, 0, v_str_4081_);
lean_ctor_set(v___x_4103_, 1, v___x_4086_);
lean_ctor_set(v___x_4103_, 2, v___x_4087_);
v___x_4104_ = lean_unsigned_to_nat(1u);
v___x_4105_ = lean_substring_drop(v___x_4103_, v___x_4104_);
v___x_4106_ = lean_substring_all(v___x_4105_, v___f_4101_);
if (v___x_4106_ == 0)
{
goto v___jp_4094_;
}
else
{
v_val_4083_ = v_str_4081_;
goto v___jp_4082_;
}
}
v___jp_4107_:
{
uint32_t v___x_4109_; uint8_t v___x_4110_; 
v___x_4109_ = 95;
v___x_4110_ = lean_uint32_dec_eq(v___y_4108_, v___x_4109_);
if (v___x_4110_ == 0)
{
uint8_t v___x_4111_; 
v___x_4111_ = l_Lean_isLetterLike(v___y_4108_);
if (v___x_4111_ == 0)
{
goto v___jp_4094_;
}
else
{
goto v___jp_4102_;
}
}
else
{
goto v___jp_4102_;
}
}
v___jp_4112_:
{
uint32_t v___x_4114_; uint8_t v___x_4115_; 
v___x_4114_ = 97;
v___x_4115_ = lean_uint32_dec_le(v___x_4114_, v___y_4113_);
if (v___x_4115_ == 0)
{
v___y_4108_ = v___y_4113_;
goto v___jp_4107_;
}
else
{
uint32_t v___x_4116_; uint8_t v___x_4117_; 
v___x_4116_ = 122;
v___x_4117_ = lean_uint32_dec_le(v___y_4113_, v___x_4116_);
if (v___x_4117_ == 0)
{
v___y_4108_ = v___y_4113_;
goto v___jp_4107_;
}
else
{
goto v___jp_4102_;
}
}
}
v___jp_4118_:
{
uint32_t v___x_4119_; uint32_t v___x_4120_; uint8_t v___x_4121_; 
v___x_4119_ = lean_string_utf8_get(v_str_4081_, v___x_4086_);
v___x_4120_ = 65;
v___x_4121_ = lean_uint32_dec_le(v___x_4120_, v___x_4119_);
if (v___x_4121_ == 0)
{
v___y_4113_ = v___x_4119_;
goto v___jp_4112_;
}
else
{
uint32_t v___x_4122_; uint8_t v___x_4123_; 
v___x_4122_ = 90;
v___x_4123_ = lean_uint32_dec_le(v___x_4119_, v___x_4122_);
if (v___x_4123_ == 0)
{
v___y_4113_ = v___x_4119_;
goto v___jp_4112_;
}
else
{
goto v___jp_4102_;
}
}
}
v___jp_4124_:
{
lean_object* v___x_4125_; uint8_t v___x_4126_; 
v___x_4125_ = lean_unsigned_to_nat(1u);
v___x_4126_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4081_, v___x_4125_);
if (v___x_4126_ == 0)
{
goto v___jp_4118_;
}
else
{
v_val_4083_ = v_str_4081_;
goto v___jp_4082_;
}
}
v___jp_4128_:
{
uint8_t v___x_4129_; uint8_t v___x_4130_; 
v___x_4129_ = 95;
v___x_4130_ = lean_uint8_dec_eq(v_c_4127_, v___x_4129_);
if (v___x_4130_ == 0)
{
goto v___jp_4118_;
}
else
{
goto v___jp_4124_;
}
}
v___jp_4131_:
{
uint8_t v___x_4132_; uint8_t v___x_4133_; 
v___x_4132_ = 65;
v___x_4133_ = lean_uint8_dec_le(v___x_4132_, v_c_4127_);
if (v___x_4133_ == 0)
{
goto v___jp_4128_;
}
else
{
uint8_t v___x_4134_; uint8_t v___x_4135_; 
v___x_4134_ = 90;
v___x_4135_ = lean_uint8_dec_le(v_c_4127_, v___x_4134_);
if (v___x_4135_ == 0)
{
goto v___jp_4128_;
}
else
{
goto v___jp_4124_;
}
}
}
}
v___jp_4082_:
{
lean_object* v___x_4084_; 
v___x_4084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4084_, 0, v_val_4083_);
lean_ctor_set(v___x_4084_, 1, v_acc_4075_);
v_acc_4075_ = v___x_4084_;
v_x_4076_ = v_pre_4080_;
goto _start;
}
}
default: 
{
lean_object* v___x_4140_; 
lean_dec_ref_known(v_x_4076_, 2);
lean_dec(v_acc_4075_);
v___x_4140_ = lean_box(0);
return v___x_4140_;
}
}
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__3(void){
_start:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4147_ = ((lean_object*)(l_Lean_quoteNameMk___closed__2));
v___x_4148_ = l_Lean_mkCIdent(v___x_4147_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object* v_x_4159_){
_start:
{
switch(lean_obj_tag(v_x_4159_))
{
case 0:
{
lean_object* v___x_4160_; 
v___x_4160_ = lean_obj_once(&l_Lean_quoteNameMk___closed__3, &l_Lean_quoteNameMk___closed__3_once, _init_l_Lean_quoteNameMk___closed__3);
return v___x_4160_;
}
case 1:
{
lean_object* v_pre_4161_; lean_object* v_str_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v_pre_4161_ = lean_ctor_get(v_x_4159_, 0);
lean_inc(v_pre_4161_);
v_str_4162_ = lean_ctor_get(v_x_4159_, 1);
lean_inc_ref(v_str_4162_);
lean_dec_ref_known(v_x_4159_, 2);
v___x_4163_ = ((lean_object*)(l_Lean_quoteNameMk___closed__5));
v___x_4164_ = l_Lean_quoteNameMk(v_pre_4161_);
v___x_4165_ = lean_box(2);
v___x_4166_ = l_Lean_Syntax_mkStrLit(v_str_4162_, v___x_4165_);
v___x_4167_ = lean_unsigned_to_nat(2u);
v___x_4168_ = lean_mk_empty_array_with_capacity(v___x_4167_);
v___x_4169_ = lean_array_push(v___x_4168_, v___x_4164_);
v___x_4170_ = lean_array_push(v___x_4169_, v___x_4166_);
v___x_4171_ = l_Lean_Syntax_mkCApp(v___x_4163_, v___x_4170_);
return v___x_4171_;
}
default: 
{
lean_object* v_pre_4172_; lean_object* v_i_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v_pre_4172_ = lean_ctor_get(v_x_4159_, 0);
lean_inc(v_pre_4172_);
v_i_4173_ = lean_ctor_get(v_x_4159_, 1);
lean_inc(v_i_4173_);
lean_dec_ref_known(v_x_4159_, 2);
v___x_4174_ = ((lean_object*)(l_Lean_quoteNameMk___closed__7));
v___x_4175_ = l_Lean_quoteNameMk(v_pre_4172_);
v___x_4176_ = l_Nat_reprFast(v_i_4173_);
v___x_4177_ = lean_box(2);
v___x_4178_ = l_Lean_Syntax_mkNumLit(v___x_4176_, v___x_4177_);
v___x_4179_ = lean_unsigned_to_nat(2u);
v___x_4180_ = lean_mk_empty_array_with_capacity(v___x_4179_);
v___x_4181_ = lean_array_push(v___x_4180_, v___x_4175_);
v___x_4182_ = lean_array_push(v___x_4181_, v___x_4178_);
v___x_4183_ = l_Lean_Syntax_mkCApp(v___x_4174_, v___x_4182_);
return v___x_4183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object* v_n_4190_){
_start:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4191_ = lean_box(0);
lean_inc(v_n_4190_);
v___x_4192_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4191_, v_n_4190_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v___x_4193_; 
v___x_4193_ = l_Lean_quoteNameMk(v_n_4190_);
return v___x_4193_;
}
else
{
lean_object* v_val_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_dec(v_n_4190_);
v_val_4194_ = lean_ctor_get(v___x_4192_, 0);
lean_inc(v_val_4194_);
lean_dec_ref_known(v___x_4192_, 1);
v___x_4195_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4196_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4197_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4198_ = lean_string_intercalate(v___x_4197_, v_val_4194_);
v___x_4199_ = lean_string_append(v___x_4196_, v___x_4198_);
lean_dec_ref(v___x_4198_);
v___x_4200_ = lean_box(2);
v___x_4201_ = l_Lean_Syntax_mkNameLit(v___x_4199_, v___x_4200_);
v___x_4202_ = lean_unsigned_to_nat(1u);
v___x_4203_ = lean_mk_empty_array_with_capacity(v___x_4202_);
v___x_4204_ = lean_array_push(v___x_4203_, v___x_4201_);
v___x_4205_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4200_);
lean_ctor_set(v___x_4205_, 1, v___x_4195_);
lean_ctor_set(v___x_4205_, 2, v___x_4204_);
return v___x_4205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object* v_n_4206_){
_start:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4207_ = lean_box(0);
lean_inc(v_n_4206_);
v___x_4208_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4207_, v_n_4206_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v___x_4209_; 
v___x_4209_ = l_Lean_quoteNameMk(v_n_4206_);
return v___x_4209_;
}
else
{
lean_object* v_val_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
lean_dec(v_n_4206_);
v_val_4210_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_val_4210_);
lean_dec_ref_known(v___x_4208_, 1);
v___x_4211_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4212_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4213_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4214_ = lean_string_intercalate(v___x_4213_, v_val_4210_);
v___x_4215_ = lean_string_append(v___x_4212_, v___x_4214_);
lean_dec_ref(v___x_4214_);
v___x_4216_ = lean_box(2);
v___x_4217_ = l_Lean_Syntax_mkNameLit(v___x_4215_, v___x_4216_);
v___x_4218_ = lean_unsigned_to_nat(1u);
v___x_4219_ = lean_mk_empty_array_with_capacity(v___x_4218_);
v___x_4220_ = lean_array_push(v___x_4219_, v___x_4217_);
v___x_4221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4216_);
lean_ctor_set(v___x_4221_, 1, v___x_4211_);
lean_ctor_set(v___x_4221_, 2, v___x_4220_);
return v___x_4221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object* v_inst_4229_, lean_object* v_inst_4230_, lean_object* v_x_4231_){
_start:
{
lean_object* v_fst_4232_; lean_object* v_snd_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v_fst_4232_ = lean_ctor_get(v_x_4231_, 0);
lean_inc(v_fst_4232_);
v_snd_4233_ = lean_ctor_get(v_x_4231_, 1);
lean_inc(v_snd_4233_);
lean_dec_ref(v_x_4231_);
v___x_4234_ = ((lean_object*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2));
v___x_4235_ = lean_apply_1(v_inst_4229_, v_fst_4232_);
v___x_4236_ = lean_apply_1(v_inst_4230_, v_snd_4233_);
v___x_4237_ = lean_unsigned_to_nat(2u);
v___x_4238_ = lean_mk_empty_array_with_capacity(v___x_4237_);
v___x_4239_ = lean_array_push(v___x_4238_, v___x_4235_);
v___x_4240_ = lean_array_push(v___x_4239_, v___x_4236_);
v___x_4241_ = l_Lean_Syntax_mkCApp(v___x_4234_, v___x_4240_);
return v___x_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object* v_inst_4242_, lean_object* v_inst_4243_){
_start:
{
lean_object* v___f_4244_; 
v___f_4244_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4244_, 0, v_inst_4242_);
lean_closure_set(v___f_4244_, 1, v_inst_4243_);
return v___f_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object* v_00_u03b1_4245_, lean_object* v_00_u03b2_4246_, lean_object* v_inst_4247_, lean_object* v_inst_4248_){
_start:
{
lean_object* v___f_4249_; 
v___f_4249_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4249_, 0, v_inst_4247_);
lean_closure_set(v___f_4249_, 1, v_inst_4248_);
return v___f_4249_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3(void){
_start:
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4255_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2));
v___x_4256_ = l_Lean_mkCIdent(v___x_4255_);
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object* v_inst_4261_, lean_object* v_x_4262_){
_start:
{
if (lean_obj_tag(v_x_4262_) == 0)
{
lean_object* v___x_4263_; 
lean_dec_ref(v_inst_4261_);
v___x_4263_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3);
return v___x_4263_;
}
else
{
lean_object* v_head_4264_; lean_object* v_tail_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v_head_4264_ = lean_ctor_get(v_x_4262_, 0);
lean_inc(v_head_4264_);
v_tail_4265_ = lean_ctor_get(v_x_4262_, 1);
lean_inc(v_tail_4265_);
lean_dec_ref_known(v_x_4262_, 2);
v___x_4266_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5));
lean_inc_ref(v_inst_4261_);
v___x_4267_ = lean_apply_1(v_inst_4261_, v_head_4264_);
v___x_4268_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4261_, v_tail_4265_);
v___x_4269_ = lean_unsigned_to_nat(2u);
v___x_4270_ = lean_mk_empty_array_with_capacity(v___x_4269_);
v___x_4271_ = lean_array_push(v___x_4270_, v___x_4267_);
v___x_4272_ = lean_array_push(v___x_4271_, v___x_4268_);
v___x_4273_ = l_Lean_Syntax_mkCApp(v___x_4266_, v___x_4272_);
return v___x_4273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object* v_00_u03b1_4274_, lean_object* v_inst_4275_, lean_object* v_x_4276_){
_start:
{
lean_object* v___x_4277_; 
v___x_4277_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4275_, v_x_4276_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object* v_inst_4278_, lean_object* v_a_4279_){
_start:
{
lean_object* v___x_4280_; 
v___x_4280_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4278_, v_a_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object* v_00_u03b1_4281_, lean_object* v_inst_4282_, lean_object* v_a_4283_){
_start:
{
lean_object* v___x_4284_; 
v___x_4284_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4282_, v_a_4283_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object* v_inst_4285_){
_start:
{
lean_object* v___x_4286_; 
v___x_4286_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4286_, 0, lean_box(0));
lean_closure_set(v___x_4286_, 1, v_inst_4285_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object* v_00_u03b1_4287_, lean_object* v_inst_4288_){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4289_, 0, lean_box(0));
lean_closure_set(v___x_4289_, 1, v_inst_4288_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object* v_inst_4292_, lean_object* v_xs_4293_, lean_object* v_i_4294_, lean_object* v_args_4295_){
_start:
{
lean_object* v___x_4296_; uint8_t v___x_4297_; 
v___x_4296_ = lean_array_get_size(v_xs_4293_);
v___x_4297_ = lean_nat_dec_lt(v_i_4294_, v___x_4296_);
if (v___x_4297_ == 0)
{
lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; 
lean_dec(v_i_4294_);
lean_dec_ref(v_inst_4292_);
v___x_4298_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0));
v___x_4299_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1));
v___x_4300_ = l_Nat_reprFast(v___x_4296_);
v___x_4301_ = lean_string_append(v___x_4299_, v___x_4300_);
lean_dec_ref(v___x_4300_);
v___x_4302_ = l_Lean_Name_mkStr2(v___x_4298_, v___x_4301_);
v___x_4303_ = l_Lean_Syntax_mkCApp(v___x_4302_, v_args_4295_);
return v___x_4303_;
}
else
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4304_ = lean_unsigned_to_nat(1u);
v___x_4305_ = lean_nat_add(v_i_4294_, v___x_4304_);
v___x_4306_ = lean_array_fget_borrowed(v_xs_4293_, v_i_4294_);
lean_dec(v_i_4294_);
lean_inc_ref(v_inst_4292_);
lean_inc(v___x_4306_);
v___x_4307_ = lean_apply_1(v_inst_4292_, v___x_4306_);
v___x_4308_ = lean_array_push(v_args_4295_, v___x_4307_);
v_i_4294_ = v___x_4305_;
v_args_4295_ = v___x_4308_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object* v_inst_4310_, lean_object* v_xs_4311_, lean_object* v_i_4312_, lean_object* v_args_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4310_, v_xs_4311_, v_i_4312_, v_args_4313_);
lean_dec_ref(v_xs_4311_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object* v_00_u03b1_4315_, lean_object* v_inst_4316_, lean_object* v_xs_4317_, lean_object* v_i_4318_, lean_object* v_args_4319_){
_start:
{
lean_object* v___x_4320_; 
v___x_4320_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4316_, v_xs_4317_, v_i_4318_, v_args_4319_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object* v_00_u03b1_4321_, lean_object* v_inst_4322_, lean_object* v_xs_4323_, lean_object* v_i_4324_, lean_object* v_args_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go(v_00_u03b1_4321_, v_inst_4322_, v_xs_4323_, v_i_4324_, v_args_4325_);
lean_dec_ref(v_xs_4323_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object* v_inst_4331_, lean_object* v_xs_4332_){
_start:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; uint8_t v___x_4335_; 
v___x_4333_ = lean_array_get_size(v_xs_4332_);
v___x_4334_ = lean_unsigned_to_nat(8u);
v___x_4335_ = lean_nat_dec_le(v___x_4333_, v___x_4334_);
if (v___x_4335_ == 0)
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4336_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1));
v___x_4337_ = lean_array_to_list(v_xs_4332_);
v___x_4338_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4331_, v___x_4337_);
v___x_4339_ = lean_unsigned_to_nat(1u);
v___x_4340_ = lean_mk_empty_array_with_capacity(v___x_4339_);
v___x_4341_ = lean_array_push(v___x_4340_, v___x_4338_);
v___x_4342_ = l_Lean_Syntax_mkCApp(v___x_4336_, v___x_4341_);
return v___x_4342_;
}
else
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4343_ = lean_unsigned_to_nat(0u);
v___x_4344_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4345_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4331_, v_xs_4332_, v___x_4343_, v___x_4344_);
lean_dec_ref(v_xs_4332_);
return v___x_4345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object* v_00_u03b1_4346_, lean_object* v_inst_4347_, lean_object* v_xs_4348_){
_start:
{
lean_object* v___x_4349_; 
v___x_4349_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4347_, v_xs_4348_);
return v___x_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object* v_inst_4350_, lean_object* v_xs_4351_){
_start:
{
lean_object* v___x_4352_; 
v___x_4352_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4350_, v_xs_4351_);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object* v_00_u03b1_4353_, lean_object* v_inst_4354_, lean_object* v_xs_4355_){
_start:
{
lean_object* v___x_4356_; 
v___x_4356_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4354_, v_xs_4355_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object* v_inst_4357_){
_start:
{
lean_object* v___x_4358_; 
v___x_4358_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4358_, 0, lean_box(0));
lean_closure_set(v___x_4358_, 1, v_inst_4357_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object* v_00_u03b1_4359_, lean_object* v_inst_4360_){
_start:
{
lean_object* v___x_4361_; 
v___x_4361_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4361_, 0, lean_box(0));
lean_closure_set(v___x_4361_, 1, v_inst_4360_);
return v___x_4361_;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4367_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__2));
v___x_4368_ = l_Lean_mkIdent(v___x_4367_);
return v___x_4368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object* v_inst_4373_, lean_object* v_x_4374_){
_start:
{
if (lean_obj_tag(v_x_4374_) == 0)
{
lean_object* v___x_4375_; 
lean_dec_ref(v_inst_4373_);
v___x_4375_ = lean_obj_once(&l_Lean_Option_hasQuote___redArg___lam__0___closed__3, &l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once, _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3);
return v___x_4375_;
}
else
{
lean_object* v_val_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v_val_4376_ = lean_ctor_get(v_x_4374_, 0);
lean_inc(v_val_4376_);
lean_dec_ref_known(v_x_4374_, 1);
v___x_4377_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__5));
v___x_4378_ = lean_apply_1(v_inst_4373_, v_val_4376_);
v___x_4379_ = lean_unsigned_to_nat(1u);
v___x_4380_ = lean_mk_empty_array_with_capacity(v___x_4379_);
v___x_4381_ = lean_array_push(v___x_4380_, v___x_4378_);
v___x_4382_ = l_Lean_Syntax_mkCApp(v___x_4377_, v___x_4381_);
return v___x_4382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object* v_inst_4383_){
_start:
{
lean_object* v___f_4384_; 
v___f_4384_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4384_, 0, v_inst_4383_);
return v___f_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object* v_00_u03b1_4385_, lean_object* v_inst_4386_){
_start:
{
lean_object* v___f_4387_; 
v___f_4387_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4387_, 0, v_inst_4386_);
return v___f_4387_;
}
}
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(lean_object* v_k_4388_){
_start:
{
lean_object* v___x_4389_; uint8_t v___x_4390_; 
v___x_4389_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_4390_ = lean_name_eq(v_k_4388_, v___x_4389_);
if (v___x_4390_ == 0)
{
uint8_t v___x_4391_; 
v___x_4391_ = 1;
return v___x_4391_;
}
else
{
uint8_t v___x_4392_; 
v___x_4392_ = 0;
return v___x_4392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v_k_4393_){
_start:
{
uint8_t v_res_4394_; lean_object* v_r_4395_; 
v_res_4394_ = l_Lean_evalPrec___lam__0(v_k_4393_);
lean_dec(v_k_4393_);
v_r_4395_ = lean_box(v_res_4394_);
return v_r_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_){
_start:
{
lean_object* v_methods_4401_; lean_object* v_quotContext_4402_; lean_object* v_currMacroScope_4403_; lean_object* v_currRecDepth_4404_; lean_object* v_maxRecDepth_4405_; lean_object* v_ref_4406_; lean_object* v___f_4407_; lean_object* v_methods_4409_; lean_object* v_quotContext_4410_; lean_object* v_currMacroScope_4411_; lean_object* v_currRecDepth_4412_; lean_object* v_maxRecDepth_4413_; lean_object* v_ref_4414_; lean_object* v___y_4415_; lean_object* v___x_4443_; uint8_t v___x_4444_; 
v_methods_4401_ = lean_ctor_get(v_a_4399_, 0);
v_quotContext_4402_ = lean_ctor_get(v_a_4399_, 1);
v_currMacroScope_4403_ = lean_ctor_get(v_a_4399_, 2);
v_currRecDepth_4404_ = lean_ctor_get(v_a_4399_, 3);
v_maxRecDepth_4405_ = lean_ctor_get(v_a_4399_, 4);
v_ref_4406_ = lean_ctor_get(v_a_4399_, 5);
v___f_4407_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4443_ = lean_unsigned_to_nat(0u);
v___x_4444_ = lean_nat_dec_eq(v_maxRecDepth_4405_, v___x_4443_);
if (v___x_4444_ == 0)
{
uint8_t v___x_4445_; 
v___x_4445_ = lean_nat_dec_eq(v_currRecDepth_4404_, v_maxRecDepth_4405_);
if (v___x_4445_ == 0)
{
v_methods_4409_ = v_methods_4401_;
v_quotContext_4410_ = v_quotContext_4402_;
v_currMacroScope_4411_ = v_currMacroScope_4403_;
v_currRecDepth_4412_ = v_currRecDepth_4404_;
v_maxRecDepth_4413_ = v_maxRecDepth_4405_;
v_ref_4414_ = v_ref_4406_;
v___y_4415_ = v_a_4400_;
goto v___jp_4408_;
}
else
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___x_4446_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4447_, 0, v_stx_4398_);
lean_ctor_set(v___x_4447_, 1, v___x_4446_);
v___x_4448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4447_);
lean_ctor_set(v___x_4448_, 1, v_a_4400_);
return v___x_4448_;
}
}
else
{
v_methods_4409_ = v_methods_4401_;
v_quotContext_4410_ = v_quotContext_4402_;
v_currMacroScope_4411_ = v_currMacroScope_4403_;
v_currRecDepth_4412_ = v_currRecDepth_4404_;
v_maxRecDepth_4413_ = v_maxRecDepth_4405_;
v_ref_4414_ = v_ref_4406_;
v___y_4415_ = v_a_4400_;
goto v___jp_4408_;
}
v___jp_4408_:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4416_ = lean_unsigned_to_nat(1u);
v___x_4417_ = lean_nat_add(v_currRecDepth_4412_, v___x_4416_);
lean_inc(v_ref_4414_);
lean_inc(v_maxRecDepth_4413_);
lean_inc(v_currMacroScope_4411_);
lean_inc(v_quotContext_4410_);
lean_inc(v_methods_4409_);
v___x_4418_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4418_, 0, v_methods_4409_);
lean_ctor_set(v___x_4418_, 1, v_quotContext_4410_);
lean_ctor_set(v___x_4418_, 2, v_currMacroScope_4411_);
lean_ctor_set(v___x_4418_, 3, v___x_4417_);
lean_ctor_set(v___x_4418_, 4, v_maxRecDepth_4413_);
lean_ctor_set(v___x_4418_, 5, v_ref_4414_);
lean_inc_ref(v___x_4418_);
v___x_4419_ = l_Lean_expandMacros(v_stx_4398_, v___f_4407_, v___x_4418_, v___y_4415_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4433_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
v_a_4421_ = lean_ctor_get(v___x_4419_, 1);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4423_ = v___x_4419_;
v_isShared_4424_ = v_isSharedCheck_4433_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_inc(v_a_4420_);
lean_dec(v___x_4419_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4433_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4425_; uint8_t v___x_4426_; 
v___x_4425_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4420_);
v___x_4426_ = l_Lean_Syntax_isOfKind(v_a_4420_, v___x_4425_);
if (v___x_4426_ == 0)
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
lean_del_object(v___x_4423_);
v___x_4427_ = ((lean_object*)(l_Lean_evalPrec___closed__1));
v___x_4428_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4420_, v___x_4427_, v___x_4418_, v_a_4421_);
lean_dec_ref_known(v___x_4418_, 6);
lean_dec(v_a_4420_);
return v___x_4428_;
}
else
{
lean_object* v___x_4429_; lean_object* v___x_4431_; 
lean_dec_ref_known(v___x_4418_, 6);
v___x_4429_ = l_Lean_TSyntax_getNat(v_a_4420_);
lean_dec(v_a_4420_);
if (v_isShared_4424_ == 0)
{
lean_ctor_set(v___x_4423_, 0, v___x_4429_);
v___x_4431_ = v___x_4423_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4429_);
lean_ctor_set(v_reuseFailAlloc_4432_, 1, v_a_4421_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
}
else
{
lean_object* v_a_4434_; lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
lean_dec_ref_known(v___x_4418_, 6);
v_a_4434_ = lean_ctor_get(v___x_4419_, 0);
v_a_4435_ = lean_ctor_get(v___x_4419_, 1);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4437_ = v___x_4419_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_inc(v_a_4434_);
lean_dec(v___x_4419_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4434_);
lean_ctor_set(v_reuseFailAlloc_4441_, 1, v_a_4435_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object* v_stx_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l_Lean_evalPrec(v_stx_4449_, v_a_4450_, v_a_4451_);
lean_dec_ref(v_a_4450_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_){
_start:
{
lean_object* v_methods_4457_; lean_object* v_quotContext_4458_; lean_object* v_currMacroScope_4459_; lean_object* v_currRecDepth_4460_; lean_object* v_maxRecDepth_4461_; lean_object* v_ref_4462_; lean_object* v___f_4463_; lean_object* v_methods_4465_; lean_object* v_quotContext_4466_; lean_object* v_currMacroScope_4467_; lean_object* v_currRecDepth_4468_; lean_object* v_maxRecDepth_4469_; lean_object* v_ref_4470_; lean_object* v___y_4471_; lean_object* v___x_4499_; uint8_t v___x_4500_; 
v_methods_4457_ = lean_ctor_get(v_a_4455_, 0);
v_quotContext_4458_ = lean_ctor_get(v_a_4455_, 1);
v_currMacroScope_4459_ = lean_ctor_get(v_a_4455_, 2);
v_currRecDepth_4460_ = lean_ctor_get(v_a_4455_, 3);
v_maxRecDepth_4461_ = lean_ctor_get(v_a_4455_, 4);
v_ref_4462_ = lean_ctor_get(v_a_4455_, 5);
v___f_4463_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4499_ = lean_unsigned_to_nat(0u);
v___x_4500_ = lean_nat_dec_eq(v_maxRecDepth_4461_, v___x_4499_);
if (v___x_4500_ == 0)
{
uint8_t v___x_4501_; 
v___x_4501_ = lean_nat_dec_eq(v_currRecDepth_4460_, v_maxRecDepth_4461_);
if (v___x_4501_ == 0)
{
v_methods_4465_ = v_methods_4457_;
v_quotContext_4466_ = v_quotContext_4458_;
v_currMacroScope_4467_ = v_currMacroScope_4459_;
v_currRecDepth_4468_ = v_currRecDepth_4460_;
v_maxRecDepth_4469_ = v_maxRecDepth_4461_;
v_ref_4470_ = v_ref_4462_;
v___y_4471_ = v_a_4456_;
goto v___jp_4464_;
}
else
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4502_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4503_, 0, v_stx_4454_);
lean_ctor_set(v___x_4503_, 1, v___x_4502_);
v___x_4504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4503_);
lean_ctor_set(v___x_4504_, 1, v_a_4456_);
return v___x_4504_;
}
}
else
{
v_methods_4465_ = v_methods_4457_;
v_quotContext_4466_ = v_quotContext_4458_;
v_currMacroScope_4467_ = v_currMacroScope_4459_;
v_currRecDepth_4468_ = v_currRecDepth_4460_;
v_maxRecDepth_4469_ = v_maxRecDepth_4461_;
v_ref_4470_ = v_ref_4462_;
v___y_4471_ = v_a_4456_;
goto v___jp_4464_;
}
v___jp_4464_:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4472_ = lean_unsigned_to_nat(1u);
v___x_4473_ = lean_nat_add(v_currRecDepth_4468_, v___x_4472_);
lean_inc(v_ref_4470_);
lean_inc(v_maxRecDepth_4469_);
lean_inc(v_currMacroScope_4467_);
lean_inc(v_quotContext_4466_);
lean_inc(v_methods_4465_);
v___x_4474_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4474_, 0, v_methods_4465_);
lean_ctor_set(v___x_4474_, 1, v_quotContext_4466_);
lean_ctor_set(v___x_4474_, 2, v_currMacroScope_4467_);
lean_ctor_set(v___x_4474_, 3, v___x_4473_);
lean_ctor_set(v___x_4474_, 4, v_maxRecDepth_4469_);
lean_ctor_set(v___x_4474_, 5, v_ref_4470_);
lean_inc_ref(v___x_4474_);
v___x_4475_ = l_Lean_expandMacros(v_stx_4454_, v___f_4463_, v___x_4474_, v___y_4471_);
if (lean_obj_tag(v___x_4475_) == 0)
{
lean_object* v_a_4476_; lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4489_; 
v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
v_a_4477_ = lean_ctor_get(v___x_4475_, 1);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4475_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4479_ = v___x_4475_;
v_isShared_4480_ = v_isSharedCheck_4489_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_inc(v_a_4476_);
lean_dec(v___x_4475_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4489_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4481_; uint8_t v___x_4482_; 
v___x_4481_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4476_);
v___x_4482_ = l_Lean_Syntax_isOfKind(v_a_4476_, v___x_4481_);
if (v___x_4482_ == 0)
{
lean_object* v___x_4483_; lean_object* v___x_4484_; 
lean_del_object(v___x_4479_);
v___x_4483_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
v___x_4484_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4476_, v___x_4483_, v___x_4474_, v_a_4477_);
lean_dec_ref_known(v___x_4474_, 6);
lean_dec(v_a_4476_);
return v___x_4484_;
}
else
{
lean_object* v___x_4485_; lean_object* v___x_4487_; 
lean_dec_ref_known(v___x_4474_, 6);
v___x_4485_ = l_Lean_TSyntax_getNat(v_a_4476_);
lean_dec(v_a_4476_);
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 0, v___x_4485_);
v___x_4487_ = v___x_4479_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4485_);
lean_ctor_set(v_reuseFailAlloc_4488_, 1, v_a_4477_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
}
else
{
lean_object* v_a_4490_; lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
lean_dec_ref_known(v___x_4474_, 6);
v_a_4490_ = lean_ctor_get(v___x_4475_, 0);
v_a_4491_ = lean_ctor_get(v___x_4475_, 1);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4475_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4493_ = v___x_4475_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_inc(v_a_4490_);
lean_dec(v___x_4475_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4490_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v_a_4491_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object* v_stx_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_Lean_evalPrio(v_stx_4505_, v_a_4506_, v_a_4507_);
lean_dec_ref(v_a_4506_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_){
_start:
{
if (lean_obj_tag(v_x_4509_) == 0)
{
lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4512_ = lean_unsigned_to_nat(1000u);
v___x_4513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4512_);
lean_ctor_set(v___x_4513_, 1, v_a_4511_);
return v___x_4513_;
}
else
{
lean_object* v_val_4514_; lean_object* v___x_4515_; 
v_val_4514_ = lean_ctor_get(v_x_4509_, 0);
lean_inc(v_val_4514_);
lean_dec_ref_known(v_x_4509_, 1);
v___x_4515_ = l_Lean_evalPrio(v_val_4514_, v_a_4510_, v_a_4511_);
return v___x_4515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object* v_x_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l_Lean_evalOptPrio(v_x_4516_, v_a_4517_, v_a_4518_);
lean_dec_ref(v_a_4517_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4520_, lean_object* v_x1_4521_, lean_object* v_x2_4522_){
_start:
{
lean_object* v_fst_4523_; uint8_t v___x_4524_; 
v_fst_4523_ = lean_ctor_get(v_x1_4521_, 0);
v___x_4524_ = lean_unbox(v_fst_4523_);
if (v___x_4524_ == 0)
{
lean_object* v_snd_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4533_; 
lean_dec(v_x2_4522_);
v_snd_4525_ = lean_ctor_get(v_x1_4521_, 1);
v_isSharedCheck_4533_ = !lean_is_exclusive(v_x1_4521_);
if (v_isSharedCheck_4533_ == 0)
{
lean_object* v_unused_4534_; 
v_unused_4534_ = lean_ctor_get(v_x1_4521_, 0);
lean_dec(v_unused_4534_);
v___x_4527_ = v_x1_4521_;
v_isShared_4528_ = v_isSharedCheck_4533_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_snd_4525_);
lean_dec(v_x1_4521_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4533_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4529_; lean_object* v___x_4531_; 
v___x_4529_ = lean_box(v___x_4520_);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 0, v___x_4529_);
v___x_4531_ = v___x_4527_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___x_4529_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v_snd_4525_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
else
{
lean_object* v_snd_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4545_; 
v_snd_4535_ = lean_ctor_get(v_x1_4521_, 1);
v_isSharedCheck_4545_ = !lean_is_exclusive(v_x1_4521_);
if (v_isSharedCheck_4545_ == 0)
{
lean_object* v_unused_4546_; 
v_unused_4546_ = lean_ctor_get(v_x1_4521_, 0);
lean_dec(v_unused_4546_);
v___x_4537_ = v_x1_4521_;
v_isShared_4538_ = v_isSharedCheck_4545_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_snd_4535_);
lean_dec(v_x1_4521_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4545_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
uint8_t v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4543_; 
v___x_4539_ = 0;
v___x_4540_ = lean_array_push(v_snd_4535_, v_x2_4522_);
v___x_4541_ = lean_box(v___x_4539_);
if (v_isShared_4538_ == 0)
{
lean_ctor_set(v___x_4537_, 1, v___x_4540_);
lean_ctor_set(v___x_4537_, 0, v___x_4541_);
v___x_4543_ = v___x_4537_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v___x_4541_);
lean_ctor_set(v_reuseFailAlloc_4544_, 1, v___x_4540_);
v___x_4543_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
return v___x_4543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4547_, lean_object* v_x1_4548_, lean_object* v_x2_4549_){
_start:
{
uint8_t v___x_87__boxed_4550_; lean_object* v_res_4551_; 
v___x_87__boxed_4550_ = lean_unbox(v___x_4547_);
v_res_4551_ = l_Array_getSepElems___redArg___lam__0(v___x_87__boxed_4550_, v_x1_4548_, v_x2_4549_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4573_){
_start:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; 
v___x_4574_ = lean_unsigned_to_nat(0u);
v___x_4575_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4576_ = lean_array_get_size(v_as_4573_);
v___x_4577_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4578_ = lean_nat_dec_lt(v___x_4574_, v___x_4576_);
if (v___x_4578_ == 0)
{
lean_dec_ref(v_as_4573_);
return v___x_4575_;
}
else
{
lean_object* v___x_4579_; lean_object* v___f_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; size_t v___x_4583_; size_t v___x_4584_; lean_object* v___x_4585_; lean_object* v_snd_4586_; 
v___x_4579_ = lean_box(v___x_4578_);
v___f_4580_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4580_, 0, v___x_4579_);
v___x_4581_ = lean_box(v___x_4578_);
v___x_4582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4581_);
lean_ctor_set(v___x_4582_, 1, v___x_4575_);
v___x_4583_ = ((size_t)0ULL);
v___x_4584_ = lean_usize_of_nat(v___x_4576_);
v___x_4585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4577_, v___f_4580_, v_as_4573_, v___x_4583_, v___x_4584_, v___x_4582_);
v_snd_4586_ = lean_ctor_get(v___x_4585_, 1);
lean_inc(v_snd_4586_);
lean_dec(v___x_4585_);
return v_snd_4586_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4587_, lean_object* v_as_4588_){
_start:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; uint8_t v___x_4593_; 
v___x_4589_ = lean_unsigned_to_nat(0u);
v___x_4590_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4591_ = lean_array_get_size(v_as_4588_);
v___x_4592_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4593_ = lean_nat_dec_lt(v___x_4589_, v___x_4591_);
if (v___x_4593_ == 0)
{
lean_dec_ref(v_as_4588_);
return v___x_4590_;
}
else
{
lean_object* v___x_4594_; lean_object* v___f_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; size_t v___x_4598_; size_t v___x_4599_; lean_object* v___x_4600_; lean_object* v_snd_4601_; 
v___x_4594_ = lean_box(v___x_4593_);
v___f_4595_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4595_, 0, v___x_4594_);
v___x_4596_ = lean_box(v___x_4593_);
v___x_4597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
lean_ctor_set(v___x_4597_, 1, v___x_4590_);
v___x_4598_ = ((size_t)0ULL);
v___x_4599_ = lean_usize_of_nat(v___x_4591_);
v___x_4600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4592_, v___f_4595_, v_as_4588_, v___x_4598_, v___x_4599_, v___x_4597_);
v_snd_4601_ = lean_ctor_get(v___x_4600_, 1);
lean_inc(v_snd_4601_);
lean_dec(v___x_4600_);
return v_snd_4601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4602_, lean_object* v_inst_4603_, lean_object* v_a_4604_, lean_object* v_p_4605_, lean_object* v_acc_4606_, lean_object* v_stx_4607_, uint8_t v_____do__lift_4608_){
_start:
{
if (v_____do__lift_4608_ == 0)
{
lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
lean_dec(v_stx_4607_);
v___x_4609_ = lean_unsigned_to_nat(2u);
v___x_4610_ = lean_nat_add(v_i_4602_, v___x_4609_);
v___x_4611_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4603_, v_a_4604_, v_p_4605_, v___x_4610_, v_acc_4606_);
return v___x_4611_;
}
else
{
lean_object* v___x_4612_; lean_object* v___x_4613_; uint8_t v___x_4614_; 
v___x_4612_ = lean_array_get_size(v_acc_4606_);
v___x_4613_ = lean_unsigned_to_nat(0u);
v___x_4614_ = lean_nat_dec_eq(v___x_4612_, v___x_4613_);
if (v___x_4614_ == 0)
{
uint8_t v___x_4615_; 
v___x_4615_ = lean_nat_dec_eq(v_i_4602_, v___x_4613_);
if (v___x_4615_ == 0)
{
lean_object* v___x_4616_; lean_object* v_sepStx_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4616_ = lean_nat_pred(v_i_4602_);
v_sepStx_4617_ = lean_array_fget_borrowed(v_a_4604_, v___x_4616_);
lean_dec(v___x_4616_);
v___x_4618_ = lean_unsigned_to_nat(2u);
v___x_4619_ = lean_nat_add(v_i_4602_, v___x_4618_);
lean_inc(v_sepStx_4617_);
v___x_4620_ = lean_array_push(v_acc_4606_, v_sepStx_4617_);
v___x_4621_ = lean_array_push(v___x_4620_, v_stx_4607_);
v___x_4622_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4603_, v_a_4604_, v_p_4605_, v___x_4619_, v___x_4621_);
return v___x_4622_;
}
else
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4623_ = lean_unsigned_to_nat(2u);
v___x_4624_ = lean_nat_add(v_i_4602_, v___x_4623_);
v___x_4625_ = lean_array_push(v_acc_4606_, v_stx_4607_);
v___x_4626_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4603_, v_a_4604_, v_p_4605_, v___x_4624_, v___x_4625_);
return v___x_4626_;
}
}
else
{
lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4627_ = lean_unsigned_to_nat(2u);
v___x_4628_ = lean_nat_add(v_i_4602_, v___x_4627_);
v___x_4629_ = lean_array_push(v_acc_4606_, v_stx_4607_);
v___x_4630_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4603_, v_a_4604_, v_p_4605_, v___x_4628_, v___x_4629_);
return v___x_4630_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4631_, lean_object* v_inst_4632_, lean_object* v_a_4633_, lean_object* v_p_4634_, lean_object* v_acc_4635_, lean_object* v_stx_4636_, lean_object* v_____do__lift_4637_){
_start:
{
uint8_t v_____do__lift_218__boxed_4638_; lean_object* v_res_4639_; 
v_____do__lift_218__boxed_4638_ = lean_unbox(v_____do__lift_4637_);
v_res_4639_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4631_, v_inst_4632_, v_a_4633_, v_p_4634_, v_acc_4635_, v_stx_4636_, v_____do__lift_218__boxed_4638_);
lean_dec(v_i_4631_);
return v_res_4639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4640_, lean_object* v_a_4641_, lean_object* v_p_4642_, lean_object* v_i_4643_, lean_object* v_acc_4644_){
_start:
{
lean_object* v_toApplicative_4645_; lean_object* v_toBind_4646_; lean_object* v_toPure_4647_; lean_object* v___x_4648_; uint8_t v___x_4649_; 
v_toApplicative_4645_ = lean_ctor_get(v_inst_4640_, 0);
v_toBind_4646_ = lean_ctor_get(v_inst_4640_, 1);
lean_inc(v_toBind_4646_);
v_toPure_4647_ = lean_ctor_get(v_toApplicative_4645_, 1);
v___x_4648_ = lean_array_get_size(v_a_4641_);
v___x_4649_ = lean_nat_dec_lt(v_i_4643_, v___x_4648_);
if (v___x_4649_ == 0)
{
lean_object* v___x_4650_; 
lean_inc(v_toPure_4647_);
lean_dec(v_toBind_4646_);
lean_dec(v_i_4643_);
lean_dec(v_p_4642_);
lean_dec_ref(v_a_4641_);
lean_dec_ref(v_inst_4640_);
v___x_4650_ = lean_apply_2(v_toPure_4647_, lean_box(0), v_acc_4644_);
return v___x_4650_;
}
else
{
lean_object* v_stx_4651_; lean_object* v___f_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; 
v_stx_4651_ = lean_array_fget(v_a_4641_, v_i_4643_);
lean_inc(v_stx_4651_);
lean_inc(v_p_4642_);
v___f_4652_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4652_, 0, v_i_4643_);
lean_closure_set(v___f_4652_, 1, v_inst_4640_);
lean_closure_set(v___f_4652_, 2, v_a_4641_);
lean_closure_set(v___f_4652_, 3, v_p_4642_);
lean_closure_set(v___f_4652_, 4, v_acc_4644_);
lean_closure_set(v___f_4652_, 5, v_stx_4651_);
v___x_4653_ = lean_apply_1(v_p_4642_, v_stx_4651_);
v___x_4654_ = lean_apply_4(v_toBind_4646_, lean_box(0), lean_box(0), v___x_4653_, v___f_4652_);
return v___x_4654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4655_, lean_object* v_inst_4656_, lean_object* v_a_4657_, lean_object* v_p_4658_, lean_object* v_i_4659_, lean_object* v_acc_4660_){
_start:
{
lean_object* v___x_4661_; 
v___x_4661_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4656_, v_a_4657_, v_p_4658_, v_i_4659_, v_acc_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4662_, lean_object* v_a_4663_, lean_object* v_p_4664_){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4665_ = lean_unsigned_to_nat(0u);
v___x_4666_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4667_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4662_, v_a_4663_, v_p_4664_, v___x_4665_, v___x_4666_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4668_, lean_object* v_inst_4669_, lean_object* v_a_4670_, lean_object* v_p_4671_){
_start:
{
lean_object* v___x_4672_; 
v___x_4672_ = l_Array_filterSepElemsM___redArg(v_inst_4669_, v_a_4670_, v_p_4671_);
return v___x_4672_;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4673_, lean_object* v_x_4674_){
_start:
{
lean_object* v___x_4675_; uint8_t v___x_4676_; 
v___x_4675_ = lean_apply_1(v_p_4673_, v_x_4674_);
v___x_4676_ = lean_unbox(v___x_4675_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4677_, lean_object* v_x_4678_){
_start:
{
uint8_t v_res_4679_; lean_object* v_r_4680_; 
v_res_4679_ = l_Array_filterSepElems___lam__0(v_p_4677_, v_x_4678_);
v_r_4680_ = lean_box(v_res_4679_);
return v_r_4680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4681_, lean_object* v_p_4682_, lean_object* v_i_4683_, lean_object* v_acc_4684_){
_start:
{
lean_object* v___x_4685_; uint8_t v___x_4686_; 
v___x_4685_ = lean_array_get_size(v_a_4681_);
v___x_4686_ = lean_nat_dec_lt(v_i_4683_, v___x_4685_);
if (v___x_4686_ == 0)
{
lean_dec(v_i_4683_);
lean_dec_ref(v_p_4682_);
return v_acc_4684_;
}
else
{
lean_object* v_stx_4687_; lean_object* v___x_4688_; uint8_t v___x_4689_; 
v_stx_4687_ = lean_array_fget_borrowed(v_a_4681_, v_i_4683_);
lean_inc_ref(v_p_4682_);
lean_inc(v_stx_4687_);
v___x_4688_ = lean_apply_1(v_p_4682_, v_stx_4687_);
v___x_4689_ = lean_unbox(v___x_4688_);
if (v___x_4689_ == 0)
{
lean_object* v___x_4690_; lean_object* v___x_4691_; 
v___x_4690_ = lean_unsigned_to_nat(2u);
v___x_4691_ = lean_nat_add(v_i_4683_, v___x_4690_);
lean_dec(v_i_4683_);
v_i_4683_ = v___x_4691_;
goto _start;
}
else
{
lean_object* v___x_4693_; lean_object* v___x_4694_; uint8_t v___x_4695_; 
v___x_4693_ = lean_array_get_size(v_acc_4684_);
v___x_4694_ = lean_unsigned_to_nat(0u);
v___x_4695_ = lean_nat_dec_eq(v___x_4693_, v___x_4694_);
if (v___x_4695_ == 0)
{
uint8_t v___x_4696_; 
v___x_4696_ = lean_nat_dec_eq(v_i_4683_, v___x_4694_);
if (v___x_4696_ == 0)
{
lean_object* v___x_4697_; lean_object* v_sepStx_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; 
v___x_4697_ = lean_nat_pred(v_i_4683_);
v_sepStx_4698_ = lean_array_fget_borrowed(v_a_4681_, v___x_4697_);
lean_dec(v___x_4697_);
v___x_4699_ = lean_unsigned_to_nat(2u);
v___x_4700_ = lean_nat_add(v_i_4683_, v___x_4699_);
lean_dec(v_i_4683_);
lean_inc(v_sepStx_4698_);
v___x_4701_ = lean_array_push(v_acc_4684_, v_sepStx_4698_);
lean_inc(v_stx_4687_);
v___x_4702_ = lean_array_push(v___x_4701_, v_stx_4687_);
v_i_4683_ = v___x_4700_;
v_acc_4684_ = v___x_4702_;
goto _start;
}
else
{
lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; 
v___x_4704_ = lean_unsigned_to_nat(2u);
v___x_4705_ = lean_nat_add(v_i_4683_, v___x_4704_);
lean_dec(v_i_4683_);
lean_inc(v_stx_4687_);
v___x_4706_ = lean_array_push(v_acc_4684_, v_stx_4687_);
v_i_4683_ = v___x_4705_;
v_acc_4684_ = v___x_4706_;
goto _start;
}
}
else
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4708_ = lean_unsigned_to_nat(2u);
v___x_4709_ = lean_nat_add(v_i_4683_, v___x_4708_);
lean_dec(v_i_4683_);
lean_inc(v_stx_4687_);
v___x_4710_ = lean_array_push(v_acc_4684_, v_stx_4687_);
v_i_4683_ = v___x_4709_;
v_acc_4684_ = v___x_4710_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4712_, lean_object* v_p_4713_, lean_object* v_i_4714_, lean_object* v_acc_4715_){
_start:
{
lean_object* v_res_4716_; 
v_res_4716_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4712_, v_p_4713_, v_i_4714_, v_acc_4715_);
lean_dec_ref(v_a_4712_);
return v_res_4716_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4717_, lean_object* v_p_4718_){
_start:
{
lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4719_ = lean_unsigned_to_nat(0u);
v___x_4720_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4721_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4717_, v_p_4718_, v___x_4719_, v___x_4720_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4722_, lean_object* v_p_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4722_, v_p_4723_);
lean_dec_ref(v_a_4722_);
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4725_, lean_object* v_p_4726_){
_start:
{
lean_object* v___f_4727_; lean_object* v___x_4728_; 
v___f_4727_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4727_, 0, v_p_4726_);
v___x_4728_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4725_, v___f_4727_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4729_, lean_object* v_p_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l_Array_filterSepElems(v_a_4729_, v_p_4730_);
lean_dec_ref(v_a_4729_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4732_, lean_object* v_acc_4733_, lean_object* v_inst_4734_, lean_object* v_a_4735_, lean_object* v_f_4736_, lean_object* v_stx_4737_){
_start:
{
lean_object* v_res_4738_; 
v_res_4738_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4732_, v_acc_4733_, v_inst_4734_, v_a_4735_, v_f_4736_, v_stx_4737_);
lean_dec(v_i_4732_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4739_, lean_object* v_a_4740_, lean_object* v_f_4741_, lean_object* v_i_4742_, lean_object* v_acc_4743_){
_start:
{
lean_object* v_toApplicative_4744_; lean_object* v_toBind_4745_; lean_object* v_toPure_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; 
v_toApplicative_4744_ = lean_ctor_get(v_inst_4739_, 0);
v_toBind_4745_ = lean_ctor_get(v_inst_4739_, 1);
v_toPure_4746_ = lean_ctor_get(v_toApplicative_4744_, 1);
v___x_4747_ = lean_array_get_size(v_a_4740_);
v___x_4748_ = lean_nat_dec_lt(v_i_4742_, v___x_4747_);
if (v___x_4748_ == 0)
{
lean_object* v___x_4749_; 
lean_inc(v_toPure_4746_);
lean_dec(v_i_4742_);
lean_dec(v_f_4741_);
lean_dec_ref(v_a_4740_);
lean_dec_ref(v_inst_4739_);
v___x_4749_ = lean_apply_2(v_toPure_4746_, lean_box(0), v_acc_4743_);
return v___x_4749_;
}
else
{
lean_object* v_stx_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; uint8_t v___x_4754_; 
v_stx_4750_ = lean_array_fget_borrowed(v_a_4740_, v_i_4742_);
v___x_4751_ = lean_unsigned_to_nat(2u);
v___x_4752_ = lean_nat_mod(v_i_4742_, v___x_4751_);
v___x_4753_ = lean_unsigned_to_nat(0u);
v___x_4754_ = lean_nat_dec_eq(v___x_4752_, v___x_4753_);
lean_dec(v___x_4752_);
if (v___x_4754_ == 0)
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4755_ = lean_unsigned_to_nat(1u);
v___x_4756_ = lean_nat_add(v_i_4742_, v___x_4755_);
lean_dec(v_i_4742_);
lean_inc(v_stx_4750_);
v___x_4757_ = lean_array_push(v_acc_4743_, v_stx_4750_);
v_i_4742_ = v___x_4756_;
v_acc_4743_ = v___x_4757_;
goto _start;
}
else
{
lean_object* v___f_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
lean_inc(v_stx_4750_);
lean_inc(v_toBind_4745_);
lean_inc(v_f_4741_);
v___f_4759_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4759_, 0, v_i_4742_);
lean_closure_set(v___f_4759_, 1, v_acc_4743_);
lean_closure_set(v___f_4759_, 2, v_inst_4739_);
lean_closure_set(v___f_4759_, 3, v_a_4740_);
lean_closure_set(v___f_4759_, 4, v_f_4741_);
v___x_4760_ = lean_apply_1(v_f_4741_, v_stx_4750_);
v___x_4761_ = lean_apply_4(v_toBind_4745_, lean_box(0), lean_box(0), v___x_4760_, v___f_4759_);
return v___x_4761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4762_, lean_object* v_acc_4763_, lean_object* v_inst_4764_, lean_object* v_a_4765_, lean_object* v_f_4766_, lean_object* v_stx_4767_){
_start:
{
lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___x_4768_ = lean_unsigned_to_nat(1u);
v___x_4769_ = lean_nat_add(v_i_4762_, v___x_4768_);
v___x_4770_ = lean_array_push(v_acc_4763_, v_stx_4767_);
v___x_4771_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4764_, v_a_4765_, v_f_4766_, v___x_4769_, v___x_4770_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4772_, lean_object* v_inst_4773_, lean_object* v_a_4774_, lean_object* v_f_4775_, lean_object* v_i_4776_, lean_object* v_acc_4777_){
_start:
{
lean_object* v___x_4778_; 
v___x_4778_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4773_, v_a_4774_, v_f_4775_, v_i_4776_, v_acc_4777_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4779_, lean_object* v_a_4780_, lean_object* v_f_4781_){
_start:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4782_ = lean_unsigned_to_nat(0u);
v___x_4783_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4784_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4779_, v_a_4780_, v_f_4781_, v___x_4782_, v___x_4783_);
return v___x_4784_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4785_, lean_object* v_inst_4786_, lean_object* v_a_4787_, lean_object* v_f_4788_){
_start:
{
lean_object* v___x_4789_; 
v___x_4789_ = l_Array_mapSepElemsM___redArg(v_inst_4786_, v_a_4787_, v_f_4788_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4790_, lean_object* v_x_4791_){
_start:
{
lean_object* v___x_4792_; 
v___x_4792_ = lean_apply_1(v_f_4790_, v_x_4791_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4793_, lean_object* v_f_4794_, lean_object* v_i_4795_, lean_object* v_acc_4796_){
_start:
{
lean_object* v___x_4797_; uint8_t v___x_4798_; 
v___x_4797_ = lean_array_get_size(v_a_4793_);
v___x_4798_ = lean_nat_dec_lt(v_i_4795_, v___x_4797_);
if (v___x_4798_ == 0)
{
lean_dec(v_i_4795_);
lean_dec_ref(v_f_4794_);
return v_acc_4796_;
}
else
{
lean_object* v_stx_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; uint8_t v___x_4803_; 
v_stx_4799_ = lean_array_fget_borrowed(v_a_4793_, v_i_4795_);
v___x_4800_ = lean_unsigned_to_nat(2u);
v___x_4801_ = lean_nat_mod(v_i_4795_, v___x_4800_);
v___x_4802_ = lean_unsigned_to_nat(0u);
v___x_4803_ = lean_nat_dec_eq(v___x_4801_, v___x_4802_);
lean_dec(v___x_4801_);
if (v___x_4803_ == 0)
{
lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4804_ = lean_unsigned_to_nat(1u);
v___x_4805_ = lean_nat_add(v_i_4795_, v___x_4804_);
lean_dec(v_i_4795_);
lean_inc(v_stx_4799_);
v___x_4806_ = lean_array_push(v_acc_4796_, v_stx_4799_);
v_i_4795_ = v___x_4805_;
v_acc_4796_ = v___x_4806_;
goto _start;
}
else
{
lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; 
lean_inc_ref(v_f_4794_);
lean_inc(v_stx_4799_);
v___x_4808_ = lean_apply_1(v_f_4794_, v_stx_4799_);
v___x_4809_ = lean_unsigned_to_nat(1u);
v___x_4810_ = lean_nat_add(v_i_4795_, v___x_4809_);
lean_dec(v_i_4795_);
v___x_4811_ = lean_array_push(v_acc_4796_, v___x_4808_);
v_i_4795_ = v___x_4810_;
v_acc_4796_ = v___x_4811_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4813_, lean_object* v_f_4814_, lean_object* v_i_4815_, lean_object* v_acc_4816_){
_start:
{
lean_object* v_res_4817_; 
v_res_4817_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4813_, v_f_4814_, v_i_4815_, v_acc_4816_);
lean_dec_ref(v_a_4813_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4818_, lean_object* v_f_4819_){
_start:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4820_ = lean_unsigned_to_nat(0u);
v___x_4821_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4822_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4818_, v_f_4819_, v___x_4820_, v___x_4821_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4823_, lean_object* v_f_4824_){
_start:
{
lean_object* v_res_4825_; 
v_res_4825_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4823_, v_f_4824_);
lean_dec_ref(v_a_4823_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4826_, lean_object* v_f_4827_){
_start:
{
lean_object* v___f_4828_; lean_object* v___x_4829_; 
v___f_4828_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4828_, 0, v_f_4827_);
v___x_4829_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4826_, v___f_4828_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4830_, lean_object* v_f_4831_){
_start:
{
lean_object* v_res_4832_; 
v_res_4832_ = l_Array_mapSepElems(v_a_4830_, v_f_4831_);
lean_dec_ref(v_a_4830_);
return v_res_4832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4833_, size_t v_i_4834_, size_t v_stop_4835_, lean_object* v_b_4836_){
_start:
{
lean_object* v___y_4838_; uint8_t v___x_4842_; 
v___x_4842_ = lean_usize_dec_eq(v_i_4834_, v_stop_4835_);
if (v___x_4842_ == 0)
{
lean_object* v_fst_4843_; uint8_t v___x_4844_; 
v_fst_4843_ = lean_ctor_get(v_b_4836_, 0);
v___x_4844_ = lean_unbox(v_fst_4843_);
if (v___x_4844_ == 0)
{
lean_object* v_snd_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4854_; 
v_snd_4845_ = lean_ctor_get(v_b_4836_, 1);
v_isSharedCheck_4854_ = !lean_is_exclusive(v_b_4836_);
if (v_isSharedCheck_4854_ == 0)
{
lean_object* v_unused_4855_; 
v_unused_4855_ = lean_ctor_get(v_b_4836_, 0);
lean_dec(v_unused_4855_);
v___x_4847_ = v_b_4836_;
v_isShared_4848_ = v_isSharedCheck_4854_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_snd_4845_);
lean_dec(v_b_4836_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4854_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
uint8_t v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4852_; 
v___x_4849_ = 1;
v___x_4850_ = lean_box(v___x_4849_);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 0, v___x_4850_);
v___x_4852_ = v___x_4847_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v___x_4850_);
lean_ctor_set(v_reuseFailAlloc_4853_, 1, v_snd_4845_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
v___y_4838_ = v___x_4852_;
goto v___jp_4837_;
}
}
}
else
{
lean_object* v_snd_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4866_; 
v_snd_4856_ = lean_ctor_get(v_b_4836_, 1);
v_isSharedCheck_4866_ = !lean_is_exclusive(v_b_4836_);
if (v_isSharedCheck_4866_ == 0)
{
lean_object* v_unused_4867_; 
v_unused_4867_ = lean_ctor_get(v_b_4836_, 0);
lean_dec(v_unused_4867_);
v___x_4858_ = v_b_4836_;
v_isShared_4859_ = v_isSharedCheck_4866_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_snd_4856_);
lean_dec(v_b_4836_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4866_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4864_; 
v___x_4860_ = lean_array_uget_borrowed(v_as_4833_, v_i_4834_);
lean_inc(v___x_4860_);
v___x_4861_ = lean_array_push(v_snd_4856_, v___x_4860_);
v___x_4862_ = lean_box(v___x_4842_);
if (v_isShared_4859_ == 0)
{
lean_ctor_set(v___x_4858_, 1, v___x_4861_);
lean_ctor_set(v___x_4858_, 0, v___x_4862_);
v___x_4864_ = v___x_4858_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v___x_4862_);
lean_ctor_set(v_reuseFailAlloc_4865_, 1, v___x_4861_);
v___x_4864_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
v___y_4838_ = v___x_4864_;
goto v___jp_4837_;
}
}
}
}
else
{
return v_b_4836_;
}
v___jp_4837_:
{
size_t v___x_4839_; size_t v___x_4840_; 
v___x_4839_ = ((size_t)1ULL);
v___x_4840_ = lean_usize_add(v_i_4834_, v___x_4839_);
v_i_4834_ = v___x_4840_;
v_b_4836_ = v___y_4838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4868_, lean_object* v_i_4869_, lean_object* v_stop_4870_, lean_object* v_b_4871_){
_start:
{
size_t v_i_boxed_4872_; size_t v_stop_boxed_4873_; lean_object* v_res_4874_; 
v_i_boxed_4872_ = lean_unbox_usize(v_i_4869_);
lean_dec(v_i_4869_);
v_stop_boxed_4873_ = lean_unbox_usize(v_stop_4870_);
lean_dec(v_stop_4870_);
v_res_4874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4868_, v_i_boxed_4872_, v_stop_boxed_4873_, v_b_4871_);
lean_dec_ref(v_as_4868_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4875_){
_start:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; uint8_t v___x_4879_; 
v___x_4876_ = lean_unsigned_to_nat(0u);
v___x_4877_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4878_ = lean_array_get_size(v_sa_4875_);
v___x_4879_ = lean_nat_dec_lt(v___x_4876_, v___x_4878_);
if (v___x_4879_ == 0)
{
return v___x_4877_;
}
else
{
lean_object* v___x_4880_; lean_object* v___x_4881_; size_t v___x_4882_; size_t v___x_4883_; lean_object* v___x_4884_; lean_object* v_snd_4885_; 
v___x_4880_ = lean_box(v___x_4879_);
v___x_4881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4880_);
lean_ctor_set(v___x_4881_, 1, v___x_4877_);
v___x_4882_ = ((size_t)0ULL);
v___x_4883_ = lean_usize_of_nat(v___x_4878_);
v___x_4884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4875_, v___x_4882_, v___x_4883_, v___x_4881_);
v_snd_4885_ = lean_ctor_get(v___x_4884_, 1);
lean_inc(v_snd_4885_);
lean_dec_ref(v___x_4884_);
return v_snd_4885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4886_){
_start:
{
lean_object* v_res_4887_; 
v_res_4887_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4886_);
lean_dec_ref(v_sa_4886_);
return v_res_4887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4888_, lean_object* v_sa_4889_){
_start:
{
lean_object* v___x_4890_; 
v___x_4890_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4889_);
return v___x_4890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4891_, lean_object* v_sa_4892_){
_start:
{
lean_object* v_res_4893_; 
v_res_4893_ = l_Lean_Syntax_SepArray_getElems(v_sep_4891_, v_sa_4892_);
lean_dec_ref(v_sa_4892_);
lean_dec_ref(v_sep_4891_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4894_){
_start:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; uint8_t v___x_4898_; 
v___x_4895_ = lean_unsigned_to_nat(0u);
v___x_4896_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4897_ = lean_array_get_size(v_sa_4894_);
v___x_4898_ = lean_nat_dec_lt(v___x_4895_, v___x_4897_);
if (v___x_4898_ == 0)
{
return v___x_4896_;
}
else
{
lean_object* v___x_4899_; lean_object* v___x_4900_; size_t v___x_4901_; size_t v___x_4902_; lean_object* v___x_4903_; lean_object* v_snd_4904_; 
v___x_4899_ = lean_box(v___x_4898_);
v___x_4900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4900_, 0, v___x_4899_);
lean_ctor_set(v___x_4900_, 1, v___x_4896_);
v___x_4901_ = ((size_t)0ULL);
v___x_4902_ = lean_usize_of_nat(v___x_4897_);
v___x_4903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4894_, v___x_4901_, v___x_4902_, v___x_4900_);
v_snd_4904_ = lean_ctor_get(v___x_4903_, 1);
lean_inc(v_snd_4904_);
lean_dec_ref(v___x_4903_);
return v_snd_4904_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4905_){
_start:
{
lean_object* v_res_4906_; 
v_res_4906_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4905_);
lean_dec_ref(v_sa_4905_);
return v_res_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4907_, lean_object* v_sep_4908_, lean_object* v_sa_4909_){
_start:
{
lean_object* v___x_4910_; 
v___x_4910_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4909_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4911_, lean_object* v_sep_4912_, lean_object* v_sa_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l_Lean_Syntax_TSepArray_getElems(v_k_4911_, v_sep_4912_, v_sa_4913_);
lean_dec_ref(v_sa_4913_);
lean_dec_ref(v_sep_4912_);
lean_dec(v_k_4911_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4915_, lean_object* v_sa_4916_, lean_object* v_e_4917_){
_start:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; uint8_t v___x_4920_; 
v___x_4918_ = lean_array_get_size(v_sa_4916_);
v___x_4919_ = lean_unsigned_to_nat(0u);
v___x_4920_ = lean_nat_dec_eq(v___x_4918_, v___x_4919_);
if (v___x_4920_ == 0)
{
lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
v___x_4921_ = l_Lean_mkAtom(v_sep_4915_);
v___x_4922_ = lean_array_push(v_sa_4916_, v___x_4921_);
v___x_4923_ = lean_array_push(v___x_4922_, v_e_4917_);
return v___x_4923_;
}
else
{
lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; 
lean_dec_ref(v_sa_4916_);
lean_dec_ref(v_sep_4915_);
v___x_4924_ = lean_unsigned_to_nat(1u);
v___x_4925_ = lean_mk_empty_array_with_capacity(v___x_4924_);
v___x_4926_ = lean_array_push(v___x_4925_, v_e_4917_);
return v___x_4926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_4927_, lean_object* v_sep_4928_, lean_object* v_sa_4929_, lean_object* v_e_4930_){
_start:
{
lean_object* v___x_4931_; 
v___x_4931_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_4928_, v_sa_4929_, v_e_4930_);
return v___x_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_4932_, lean_object* v_sep_4933_, lean_object* v_sa_4934_, lean_object* v_e_4935_){
_start:
{
lean_object* v_res_4936_; 
v_res_4936_ = l_Lean_Syntax_TSepArray_push(v_k_4932_, v_sep_4933_, v_sa_4934_, v_e_4935_);
lean_dec(v_k_4932_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg(){
_start:
{
lean_object* v___x_4938_; 
v___x_4938_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___redArg___boxed(lean_object* v___dummy_4939_){
_start:
{
lean_object* v_res_4940_; 
v_res_4940_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v_res_4940_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0(void){
_start:
{
lean_object* v___x_4941_; 
v___x_4941_ = l_Lean_Syntax_instEmptyCollectionSepArray___redArg();
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_4942_){
_start:
{
lean_object* v___x_4943_; 
v___x_4943_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionSepArray___closed__0);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_4944_);
lean_dec_ref(v_sep_4944_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg(){
_start:
{
lean_object* v___x_4947_; 
v___x_4947_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___redArg___boxed(lean_object* v___dummy_4948_){
_start:
{
lean_object* v_res_4949_; 
v_res_4949_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v_res_4949_;
}
}
static lean_object* _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0(void){
_start:
{
lean_object* v___x_4950_; 
v___x_4950_ = l_Lean_Syntax_instEmptyCollectionTSepArray___redArg();
return v___x_4950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_4951_, lean_object* v_k_4952_){
_start:
{
lean_object* v___x_4953_; 
v___x_4953_ = lean_obj_once(&l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0, &l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0_once, _init_l_Lean_Syntax_instEmptyCollectionTSepArray___closed__0);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_4954_, lean_object* v_k_4955_){
_start:
{
lean_object* v_res_4956_; 
v_res_4956_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_4954_, v_k_4955_);
lean_dec_ref(v_k_4955_);
lean_dec(v_sep_4954_);
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(lean_object* v_v_4957_){
_start:
{
lean_inc_ref(v_v_4957_);
return v_v_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0___boxed(lean_object* v_v_4958_){
_start:
{
lean_object* v_res_4959_; 
v_res_4959_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___lam__0(v_v_4958_);
lean_dec_ref(v_v_4958_);
return v_res_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg(){
_start:
{
lean_object* v___f_4962_; 
v___f_4962_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___boxed(lean_object* v___dummy_4963_){
_start:
{
lean_object* v_res_4964_; 
v_res_4964_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg();
return v_res_4964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray(lean_object* v_k_4965_, lean_object* v_sep_4966_){
_start:
{
lean_object* v___f_4967_; 
v___f_4967_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___redArg___closed__0));
return v___f_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___boxed(lean_object* v_k_4968_, lean_object* v_sep_4969_){
_start:
{
lean_object* v_res_4970_; 
v_res_4970_ = l_Lean_Syntax_instCoeOutTSepArraySepArray(v_k_4968_, v_sep_4969_);
lean_dec_ref(v_sep_4969_);
lean_dec(v_k_4968_);
return v_res_4970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_4971_, lean_object* v_sep_4972_){
_start:
{
lean_object* v___x_4973_; 
v___x_4973_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_4973_, 0, v_k_4971_);
lean_closure_set(v___x_4973_, 1, v_sep_4972_);
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_4974_, lean_object* v_x_4975_){
_start:
{
lean_object* v___x_4976_; 
v___x_4976_ = lean_apply_1(v_inst_4974_, v_x_4975_);
return v___x_4976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_4977_, lean_object* v_a_4978_){
_start:
{
lean_object* v___x_4979_; size_t v_sz_4980_; size_t v___x_4981_; lean_object* v___x_4982_; 
v___x_4979_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_4980_ = lean_array_size(v_a_4978_);
v___x_4981_ = ((size_t)0ULL);
v___x_4982_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4979_, v___f_4977_, v_sz_4980_, v___x_4981_, v_a_4978_);
return v___x_4982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_4983_){
_start:
{
lean_object* v___f_4984_; lean_object* v___f_4985_; 
v___f_4984_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4984_, 0, v_inst_4983_);
v___f_4985_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4985_, 0, v___f_4984_);
return v___f_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_4986_, lean_object* v_k_x27_4987_, lean_object* v_inst_4988_){
_start:
{
lean_object* v___x_4989_; 
v___x_4989_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_4988_);
return v___x_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_4990_, lean_object* v_k_x27_4991_, lean_object* v_inst_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_4990_, v_k_x27_4991_, v_inst_4992_);
lean_dec(v_k_x27_4991_);
lean_dec(v_k_4990_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(lean_object* v_a_4994_){
_start:
{
lean_inc_ref(v_a_4994_);
return v_a_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0___boxed(lean_object* v_a_4995_){
_start:
{
lean_object* v_res_4996_; 
v_res_4996_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___lam__0(v_a_4995_);
lean_dec_ref(v_a_4995_);
return v_res_4996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg(){
_start:
{
lean_object* v___f_4999_; 
v___f_4999_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_4999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___boxed(lean_object* v___dummy_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg();
return v_res_5001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_5002_){
_start:
{
lean_object* v___f_5003_; 
v___f_5003_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___redArg___closed__0));
return v___f_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* v_k_5004_){
_start:
{
lean_object* v_res_5005_; 
v_res_5005_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(v_k_5004_);
lean_dec(v_k_5004_);
return v_res_5005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_5012_){
_start:
{
lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; 
v___x_5013_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1));
v___x_5014_ = lean_box(2);
v___x_5015_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
v___x_5016_ = lean_unsigned_to_nat(2u);
v___x_5017_ = lean_mk_empty_array_with_capacity(v___x_5016_);
v___x_5018_ = lean_array_push(v___x_5017_, v_id_5012_);
v___x_5019_ = lean_array_push(v___x_5018_, v___x_5015_);
v___x_5020_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5020_, 0, v___x_5014_);
lean_ctor_set(v___x_5020_, 1, v___x_5013_);
lean_ctor_set(v___x_5020_, 2, v___x_5019_);
return v___x_5020_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_5024_; lean_object* v___x_5025_; 
v___x_5024_ = 123;
v___x_5025_ = lean_box_uint32(v___x_5024_);
return v___x_5025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* v_s_5026_, lean_object* v_i_5027_){
_start:
{
lean_object* v___x_5028_; 
v___x_5028_ = l_Lean_Syntax_decodeQuotedChar(v_s_5026_, v_i_5027_);
if (lean_obj_tag(v___x_5028_) == 0)
{
uint32_t v_c_5029_; uint32_t v___x_5030_; uint8_t v___x_5031_; 
v_c_5029_ = lean_string_utf8_get(v_s_5026_, v_i_5027_);
v___x_5030_ = 123;
v___x_5031_ = lean_uint32_dec_eq(v_c_5029_, v___x_5030_);
if (v___x_5031_ == 0)
{
return v___x_5028_;
}
else
{
lean_object* v_i_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
v_i_5032_ = lean_string_utf8_next(v_s_5026_, v_i_5027_);
v___x_5033_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
v___x_5034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5034_, 0, v___x_5033_);
lean_ctor_set(v___x_5034_, 1, v_i_5032_);
v___x_5035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5035_, 0, v___x_5034_);
return v___x_5035_;
}
}
else
{
return v___x_5028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* v_s_5036_, lean_object* v_i_5037_){
_start:
{
lean_object* v_res_5038_; 
v_res_5038_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5036_, v_i_5037_);
lean_dec(v_i_5037_);
lean_dec_ref(v_s_5036_);
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* v_s_5039_, lean_object* v_i_5040_, lean_object* v_acc_5041_){
_start:
{
uint32_t v_c_5042_; uint32_t v___x_5043_; uint8_t v___x_5044_; 
v_c_5042_ = lean_string_utf8_get(v_s_5039_, v_i_5040_);
v___x_5043_ = 34;
v___x_5044_ = lean_uint32_dec_eq(v_c_5042_, v___x_5043_);
if (v___x_5044_ == 0)
{
uint32_t v___x_5045_; uint8_t v___x_5046_; 
v___x_5045_ = 123;
v___x_5046_ = lean_uint32_dec_eq(v_c_5042_, v___x_5045_);
if (v___x_5046_ == 0)
{
lean_object* v_i_5047_; uint8_t v___x_5048_; 
v_i_5047_ = lean_string_utf8_next(v_s_5039_, v_i_5040_);
lean_dec(v_i_5040_);
v___x_5048_ = lean_string_utf8_at_end(v_s_5039_, v_i_5047_);
if (v___x_5048_ == 0)
{
uint32_t v___x_5049_; uint8_t v___x_5050_; 
v___x_5049_ = 92;
v___x_5050_ = lean_uint32_dec_eq(v_c_5042_, v___x_5049_);
if (v___x_5050_ == 0)
{
lean_object* v___x_5051_; 
v___x_5051_ = lean_string_push(v_acc_5041_, v_c_5042_);
v_i_5040_ = v_i_5047_;
v_acc_5041_ = v___x_5051_;
goto _start;
}
else
{
lean_object* v___x_5053_; 
v___x_5053_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_5039_, v_i_5047_);
if (lean_obj_tag(v___x_5053_) == 1)
{
lean_object* v_val_5054_; lean_object* v_fst_5055_; lean_object* v_snd_5056_; uint32_t v___x_5057_; lean_object* v___x_5058_; 
lean_dec(v_i_5047_);
v_val_5054_ = lean_ctor_get(v___x_5053_, 0);
lean_inc(v_val_5054_);
lean_dec_ref_known(v___x_5053_, 1);
v_fst_5055_ = lean_ctor_get(v_val_5054_, 0);
lean_inc(v_fst_5055_);
v_snd_5056_ = lean_ctor_get(v_val_5054_, 1);
lean_inc(v_snd_5056_);
lean_dec(v_val_5054_);
v___x_5057_ = lean_unbox_uint32(v_fst_5055_);
lean_dec(v_fst_5055_);
v___x_5058_ = lean_string_push(v_acc_5041_, v___x_5057_);
v_i_5040_ = v_snd_5056_;
v_acc_5041_ = v___x_5058_;
goto _start;
}
else
{
lean_object* v___x_5060_; 
lean_dec(v___x_5053_);
lean_inc_ref(v_s_5039_);
v___x_5060_ = l_Lean_Syntax_decodeStringGap(v_s_5039_, v_i_5047_);
lean_dec(v_i_5047_);
if (lean_obj_tag(v___x_5060_) == 1)
{
lean_object* v_val_5061_; 
v_val_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_val_5061_);
lean_dec_ref_known(v___x_5060_, 1);
v_i_5040_ = v_val_5061_;
goto _start;
}
else
{
lean_object* v___x_5063_; 
lean_dec(v___x_5060_);
lean_dec_ref(v_acc_5041_);
lean_dec_ref(v_s_5039_);
v___x_5063_ = lean_box(0);
return v___x_5063_;
}
}
}
}
else
{
lean_object* v___x_5064_; 
lean_dec(v_i_5047_);
lean_dec_ref(v_acc_5041_);
lean_dec_ref(v_s_5039_);
v___x_5064_ = lean_box(0);
return v___x_5064_;
}
}
else
{
lean_object* v___x_5065_; 
lean_dec(v_i_5040_);
lean_dec_ref(v_s_5039_);
v___x_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5065_, 0, v_acc_5041_);
return v___x_5065_;
}
}
else
{
lean_object* v___x_5066_; 
lean_dec(v_i_5040_);
lean_dec_ref(v_s_5039_);
v___x_5066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5066_, 0, v_acc_5041_);
return v___x_5066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5067_){
_start:
{
lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5068_ = lean_unsigned_to_nat(1u);
v___x_5069_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5070_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5067_, v___x_5068_, v___x_5069_);
return v___x_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5074_){
_start:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___x_5075_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5076_ = l_Lean_Syntax_isLit_x3f(v___x_5075_, v_stx_5074_);
if (lean_obj_tag(v___x_5076_) == 0)
{
return v___x_5076_;
}
else
{
lean_object* v_val_5077_; lean_object* v___x_5078_; 
v_val_5077_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_val_5077_);
lean_dec_ref_known(v___x_5076_, 1);
v___x_5078_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5077_);
return v___x_5078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5079_);
lean_dec(v_stx_5079_);
return v_res_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5081_){
_start:
{
lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; uint8_t v___x_5086_; 
v___x_5082_ = l_Lean_Syntax_getArgs(v_stx_5081_);
v___x_5083_ = lean_unsigned_to_nat(0u);
v___x_5084_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5085_ = lean_array_get_size(v___x_5082_);
v___x_5086_ = lean_nat_dec_lt(v___x_5083_, v___x_5085_);
if (v___x_5086_ == 0)
{
lean_dec_ref(v___x_5082_);
return v___x_5084_;
}
else
{
lean_object* v___x_5087_; lean_object* v___x_5088_; size_t v___x_5089_; size_t v___x_5090_; lean_object* v___x_5091_; lean_object* v_snd_5092_; 
v___x_5087_ = lean_box(v___x_5086_);
v___x_5088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5088_, 0, v___x_5087_);
lean_ctor_set(v___x_5088_, 1, v___x_5084_);
v___x_5089_ = ((size_t)0ULL);
v___x_5090_ = lean_usize_of_nat(v___x_5085_);
v___x_5091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5082_, v___x_5089_, v___x_5090_, v___x_5088_);
lean_dec_ref(v___x_5082_);
v_snd_5092_ = lean_ctor_get(v___x_5091_, 1);
lean_inc(v_snd_5092_);
lean_dec_ref(v___x_5091_);
return v_snd_5092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5093_){
_start:
{
lean_object* v_res_5094_; 
v_res_5094_ = l_Lean_Syntax_getSepArgs(v_stx_5093_);
lean_dec(v_stx_5093_);
return v_res_5094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5095_, lean_object* v_mkElem_5096_, lean_object* v_mkLit_5097_, lean_object* v_as_5098_, size_t v_sz_5099_, size_t v_i_5100_, lean_object* v_b_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_){
_start:
{
lean_object* v_a_5105_; lean_object* v_a_5106_; lean_object* v_elem_5111_; lean_object* v___y_5112_; lean_object* v___y_5113_; uint8_t v___x_5118_; 
v___x_5118_ = lean_usize_dec_lt(v_i_5100_, v_sz_5099_);
if (v___x_5118_ == 0)
{
lean_object* v___x_5119_; 
lean_dec_ref(v_mkLit_5097_);
lean_dec_ref(v_mkElem_5096_);
lean_dec_ref(v_mkAppend_5095_);
v___x_5119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5119_, 0, v_b_5101_);
lean_ctor_set(v___x_5119_, 1, v___y_5103_);
return v___x_5119_;
}
else
{
lean_object* v_a_5120_; lean_object* v___x_5121_; 
v_a_5120_ = lean_array_uget_borrowed(v_as_5098_, v_i_5100_);
v___x_5121_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5120_);
if (lean_obj_tag(v___x_5121_) == 0)
{
lean_object* v_methods_5122_; lean_object* v_quotContext_5123_; lean_object* v_currMacroScope_5124_; lean_object* v_currRecDepth_5125_; lean_object* v_maxRecDepth_5126_; lean_object* v_ref_5127_; lean_object* v_ref_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; 
v_methods_5122_ = lean_ctor_get(v___y_5102_, 0);
v_quotContext_5123_ = lean_ctor_get(v___y_5102_, 1);
v_currMacroScope_5124_ = lean_ctor_get(v___y_5102_, 2);
v_currRecDepth_5125_ = lean_ctor_get(v___y_5102_, 3);
v_maxRecDepth_5126_ = lean_ctor_get(v___y_5102_, 4);
v_ref_5127_ = lean_ctor_get(v___y_5102_, 5);
v_ref_5128_ = l_Lean_replaceRef(v_a_5120_, v_ref_5127_);
lean_inc(v_maxRecDepth_5126_);
lean_inc(v_currRecDepth_5125_);
lean_inc(v_currMacroScope_5124_);
lean_inc(v_quotContext_5123_);
lean_inc(v_methods_5122_);
v___x_5129_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5129_, 0, v_methods_5122_);
lean_ctor_set(v___x_5129_, 1, v_quotContext_5123_);
lean_ctor_set(v___x_5129_, 2, v_currMacroScope_5124_);
lean_ctor_set(v___x_5129_, 3, v_currRecDepth_5125_);
lean_ctor_set(v___x_5129_, 4, v_maxRecDepth_5126_);
lean_ctor_set(v___x_5129_, 5, v_ref_5128_);
lean_inc_ref(v_mkElem_5096_);
lean_inc(v_a_5120_);
v___x_5130_ = lean_apply_3(v_mkElem_5096_, v_a_5120_, v___x_5129_, v___y_5103_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v_a_5131_; lean_object* v_a_5132_; 
v_a_5131_ = lean_ctor_get(v___x_5130_, 0);
lean_inc(v_a_5131_);
v_a_5132_ = lean_ctor_get(v___x_5130_, 1);
lean_inc(v_a_5132_);
lean_dec_ref_known(v___x_5130_, 2);
v_elem_5111_ = v_a_5131_;
v___y_5112_ = v___y_5102_;
v___y_5113_ = v_a_5132_;
goto v___jp_5110_;
}
else
{
lean_dec(v_b_5101_);
lean_dec_ref(v_mkLit_5097_);
lean_dec_ref(v_mkElem_5096_);
lean_dec_ref(v_mkAppend_5095_);
return v___x_5130_;
}
}
else
{
lean_object* v_val_5133_; uint8_t v___x_5134_; 
v_val_5133_ = lean_ctor_get(v___x_5121_, 0);
lean_inc_n(v_val_5133_, 2);
lean_dec_ref_known(v___x_5121_, 1);
v___x_5134_ = lean_string_isempty(v_val_5133_);
if (v___x_5134_ == 0)
{
lean_object* v_methods_5135_; lean_object* v_quotContext_5136_; lean_object* v_currMacroScope_5137_; lean_object* v_currRecDepth_5138_; lean_object* v_maxRecDepth_5139_; lean_object* v_ref_5140_; lean_object* v_ref_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; 
v_methods_5135_ = lean_ctor_get(v___y_5102_, 0);
v_quotContext_5136_ = lean_ctor_get(v___y_5102_, 1);
v_currMacroScope_5137_ = lean_ctor_get(v___y_5102_, 2);
v_currRecDepth_5138_ = lean_ctor_get(v___y_5102_, 3);
v_maxRecDepth_5139_ = lean_ctor_get(v___y_5102_, 4);
v_ref_5140_ = lean_ctor_get(v___y_5102_, 5);
v_ref_5141_ = l_Lean_replaceRef(v_a_5120_, v_ref_5140_);
lean_inc(v_maxRecDepth_5139_);
lean_inc(v_currRecDepth_5138_);
lean_inc(v_currMacroScope_5137_);
lean_inc(v_quotContext_5136_);
lean_inc(v_methods_5135_);
v___x_5142_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5142_, 0, v_methods_5135_);
lean_ctor_set(v___x_5142_, 1, v_quotContext_5136_);
lean_ctor_set(v___x_5142_, 2, v_currMacroScope_5137_);
lean_ctor_set(v___x_5142_, 3, v_currRecDepth_5138_);
lean_ctor_set(v___x_5142_, 4, v_maxRecDepth_5139_);
lean_ctor_set(v___x_5142_, 5, v_ref_5141_);
lean_inc_ref(v_mkLit_5097_);
v___x_5143_ = lean_apply_3(v_mkLit_5097_, v_val_5133_, v___x_5142_, v___y_5103_);
if (lean_obj_tag(v___x_5143_) == 0)
{
lean_object* v_a_5144_; lean_object* v_a_5145_; 
v_a_5144_ = lean_ctor_get(v___x_5143_, 0);
lean_inc(v_a_5144_);
v_a_5145_ = lean_ctor_get(v___x_5143_, 1);
lean_inc(v_a_5145_);
lean_dec_ref_known(v___x_5143_, 2);
v_elem_5111_ = v_a_5144_;
v___y_5112_ = v___y_5102_;
v___y_5113_ = v_a_5145_;
goto v___jp_5110_;
}
else
{
lean_dec(v_b_5101_);
lean_dec_ref(v_mkLit_5097_);
lean_dec_ref(v_mkElem_5096_);
lean_dec_ref(v_mkAppend_5095_);
return v___x_5143_;
}
}
else
{
lean_dec(v_val_5133_);
v_a_5105_ = v_b_5101_;
v_a_5106_ = v___y_5103_;
goto v___jp_5104_;
}
}
}
v___jp_5104_:
{
size_t v___x_5107_; size_t v___x_5108_; 
v___x_5107_ = ((size_t)1ULL);
v___x_5108_ = lean_usize_add(v_i_5100_, v___x_5107_);
v_i_5100_ = v___x_5108_;
v_b_5101_ = v_a_5105_;
v___y_5103_ = v_a_5106_;
goto _start;
}
v___jp_5110_:
{
uint8_t v___x_5114_; 
v___x_5114_ = l_Lean_Syntax_isMissing(v_b_5101_);
if (v___x_5114_ == 0)
{
lean_object* v___x_5115_; 
lean_inc_ref(v_mkAppend_5095_);
lean_inc_ref(v___y_5112_);
v___x_5115_ = lean_apply_4(v_mkAppend_5095_, v_b_5101_, v_elem_5111_, v___y_5112_, v___y_5113_);
if (lean_obj_tag(v___x_5115_) == 0)
{
lean_object* v_a_5116_; lean_object* v_a_5117_; 
v_a_5116_ = lean_ctor_get(v___x_5115_, 0);
lean_inc(v_a_5116_);
v_a_5117_ = lean_ctor_get(v___x_5115_, 1);
lean_inc(v_a_5117_);
lean_dec_ref_known(v___x_5115_, 2);
v_a_5105_ = v_a_5116_;
v_a_5106_ = v_a_5117_;
goto v___jp_5104_;
}
else
{
lean_dec_ref(v_mkLit_5097_);
lean_dec_ref(v_mkElem_5096_);
lean_dec_ref(v_mkAppend_5095_);
return v___x_5115_;
}
}
else
{
lean_dec(v_b_5101_);
v_a_5105_ = v_elem_5111_;
v_a_5106_ = v___y_5113_;
goto v___jp_5104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5146_, lean_object* v_mkElem_5147_, lean_object* v_mkLit_5148_, lean_object* v_as_5149_, lean_object* v_sz_5150_, lean_object* v_i_5151_, lean_object* v_b_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_){
_start:
{
size_t v_sz_boxed_5155_; size_t v_i_boxed_5156_; lean_object* v_res_5157_; 
v_sz_boxed_5155_ = lean_unbox_usize(v_sz_5150_);
lean_dec(v_sz_5150_);
v_i_boxed_5156_ = lean_unbox_usize(v_i_5151_);
lean_dec(v_i_5151_);
v_res_5157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5146_, v_mkElem_5147_, v_mkLit_5148_, v_as_5149_, v_sz_boxed_5155_, v_i_boxed_5156_, v_b_5152_, v___y_5153_, v___y_5154_);
lean_dec_ref(v___y_5153_);
lean_dec_ref(v_as_5149_);
return v_res_5157_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5158_, lean_object* v_mkAppend_5159_, lean_object* v_mkElem_5160_, lean_object* v_mkLit_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_){
_start:
{
lean_object* v_result_5164_; size_t v_sz_5165_; size_t v___x_5166_; lean_object* v___x_5167_; 
v_result_5164_ = lean_box(0);
v_sz_5165_ = lean_array_size(v_chunks_5158_);
v___x_5166_ = ((size_t)0ULL);
lean_inc_ref(v_mkLit_5161_);
v___x_5167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5159_, v_mkElem_5160_, v_mkLit_5161_, v_chunks_5158_, v_sz_5165_, v___x_5166_, v_result_5164_, v_a_5162_, v_a_5163_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; lean_object* v_a_5169_; uint8_t v___x_5170_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
v_a_5169_ = lean_ctor_get(v___x_5167_, 1);
v___x_5170_ = l_Lean_Syntax_isMissing(v_a_5168_);
if (v___x_5170_ == 0)
{
lean_dec_ref(v_mkLit_5161_);
return v___x_5167_;
}
else
{
lean_object* v___x_5171_; lean_object* v___x_5172_; 
lean_inc(v_a_5169_);
lean_dec_ref_known(v___x_5167_, 2);
v___x_5171_ = ((lean_object*)(l_Lean_versionString___closed__0));
lean_inc_ref(v_a_5162_);
v___x_5172_ = lean_apply_3(v_mkLit_5161_, v___x_5171_, v_a_5162_, v_a_5169_);
return v___x_5172_;
}
}
else
{
lean_dec_ref(v_mkLit_5161_);
return v___x_5167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5173_, lean_object* v_mkAppend_5174_, lean_object* v_mkElem_5175_, lean_object* v_mkLit_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_){
_start:
{
lean_object* v_res_5179_; 
v_res_5179_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5173_, v_mkAppend_5174_, v_mkElem_5175_, v_mkLit_5176_, v_a_5177_, v_a_5178_);
lean_dec_ref(v_a_5177_);
lean_dec_ref(v_chunks_5173_);
return v_res_5179_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5184_, lean_object* v_b_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_){
_start:
{
lean_object* v_ref_5188_; uint8_t v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; 
v_ref_5188_ = lean_ctor_get(v___y_5186_, 5);
v___x_5189_ = 0;
v___x_5190_ = l_Lean_SourceInfo_fromRef(v_ref_5188_, v___x_5189_);
v___x_5191_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5192_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5190_);
v___x_5193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5193_, 0, v___x_5190_);
lean_ctor_set(v___x_5193_, 1, v___x_5192_);
v___x_5194_ = l_Lean_Syntax_node3(v___x_5190_, v___x_5191_, v_a_5184_, v___x_5193_, v_b_5185_);
v___x_5195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5195_, 0, v___x_5194_);
lean_ctor_set(v___x_5195_, 1, v___y_5187_);
return v___x_5195_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5196_, lean_object* v_b_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_){
_start:
{
lean_object* v_res_5200_; 
v_res_5200_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5196_, v_b_5197_, v___y_5198_, v___y_5199_);
lean_dec_ref(v___y_5198_);
return v_res_5200_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5201_, lean_object* v_a_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_){
_start:
{
lean_object* v_ref_5205_; uint8_t v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; 
v_ref_5205_ = lean_ctor_get(v___y_5203_, 5);
v___x_5206_ = 0;
v___x_5207_ = l_Lean_SourceInfo_fromRef(v_ref_5205_, v___x_5206_);
v___x_5208_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5209_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5207_);
v___x_5210_ = l_Lean_Syntax_node1(v___x_5207_, v___x_5209_, v_a_5202_);
v___x_5211_ = l_Lean_Syntax_node2(v___x_5207_, v___x_5208_, v_ofInterpFn_5201_, v___x_5210_);
v___x_5212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5212_, 0, v___x_5211_);
lean_ctor_set(v___x_5212_, 1, v___y_5204_);
return v___x_5212_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5213_, lean_object* v_a_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_){
_start:
{
lean_object* v_res_5217_; 
v_res_5217_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5213_, v_a_5214_, v___y_5215_, v___y_5216_);
lean_dec_ref(v___y_5215_);
return v_res_5217_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5218_, lean_object* v_s_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_){
_start:
{
lean_object* v_ref_5222_; uint8_t v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; 
v_ref_5222_ = lean_ctor_get(v___y_5220_, 5);
v___x_5223_ = 0;
v___x_5224_ = l_Lean_SourceInfo_fromRef(v_ref_5222_, v___x_5223_);
v___x_5225_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5226_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5227_ = lean_box(2);
v___x_5228_ = l_Lean_Syntax_mkStrLit(v_s_5219_, v___x_5227_);
lean_inc(v___x_5224_);
v___x_5229_ = l_Lean_Syntax_node1(v___x_5224_, v___x_5226_, v___x_5228_);
v___x_5230_ = l_Lean_Syntax_node2(v___x_5224_, v___x_5225_, v_ofLitFn_5218_, v___x_5229_);
v___x_5231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5231_, 0, v___x_5230_);
lean_ctor_set(v___x_5231_, 1, v___y_5221_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5232_, lean_object* v_s_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_){
_start:
{
lean_object* v_res_5236_; 
v_res_5236_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5232_, v_s_5233_, v___y_5234_, v___y_5235_);
lean_dec_ref(v___y_5234_);
return v_res_5236_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5254_; lean_object* v___x_5255_; 
v___x_5254_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5255_ = l_String_toRawSubstring_x27(v___x_5254_);
return v___x_5255_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5276_, lean_object* v_type_5277_, lean_object* v_ofInterpFn_5278_, lean_object* v_ofLitFn_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_){
_start:
{
lean_object* v___f_5282_; lean_object* v___f_5283_; lean_object* v___f_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; 
v___f_5282_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5283_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5283_, 0, v_ofInterpFn_5278_);
v___f_5284_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5284_, 0, v_ofLitFn_5279_);
v___x_5285_ = l_Lean_Syntax_getArgs(v_interpStr_5276_);
v___x_5286_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5285_, v___f_5282_, v___f_5283_, v___f_5284_, v_a_5280_, v_a_5281_);
lean_dec_ref(v___x_5285_);
if (lean_obj_tag(v___x_5286_) == 0)
{
lean_object* v_a_5287_; lean_object* v_a_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5319_; 
v_a_5287_ = lean_ctor_get(v___x_5286_, 0);
v_a_5288_ = lean_ctor_get(v___x_5286_, 1);
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5286_);
if (v_isSharedCheck_5319_ == 0)
{
v___x_5290_ = v___x_5286_;
v_isShared_5291_ = v_isSharedCheck_5319_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_a_5288_);
lean_inc(v_a_5287_);
lean_dec(v___x_5286_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5319_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v_quotContext_5292_; lean_object* v_currMacroScope_5293_; lean_object* v_ref_5294_; uint8_t v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5317_; 
v_quotContext_5292_ = lean_ctor_get(v_a_5280_, 1);
v_currMacroScope_5293_ = lean_ctor_get(v_a_5280_, 2);
v_ref_5294_ = lean_ctor_get(v_a_5280_, 5);
v___x_5295_ = 0;
v___x_5296_ = l_Lean_SourceInfo_fromRef(v_ref_5294_, v___x_5295_);
v___x_5297_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5298_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5299_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc_n(v___x_5296_, 7);
v___x_5300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5300_, 0, v___x_5296_);
lean_ctor_set(v___x_5300_, 1, v___x_5299_);
v___x_5301_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5302_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5303_ = lean_box(0);
lean_inc(v_currMacroScope_5293_);
lean_inc(v_quotContext_5292_);
v___x_5304_ = l_Lean_addMacroScope(v_quotContext_5292_, v___x_5303_, v_currMacroScope_5293_);
v___x_5305_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
v___x_5306_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5306_, 0, v___x_5296_);
lean_ctor_set(v___x_5306_, 1, v___x_5302_);
lean_ctor_set(v___x_5306_, 2, v___x_5304_);
lean_ctor_set(v___x_5306_, 3, v___x_5305_);
v___x_5307_ = l_Lean_Syntax_node1(v___x_5296_, v___x_5301_, v___x_5306_);
v___x_5308_ = l_Lean_Syntax_node2(v___x_5296_, v___x_5298_, v___x_5300_, v___x_5307_);
v___x_5309_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_5310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5310_, 0, v___x_5296_);
lean_ctor_set(v___x_5310_, 1, v___x_5309_);
v___x_5311_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5312_ = l_Lean_Syntax_node1(v___x_5296_, v___x_5311_, v_type_5277_);
v___x_5313_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
v___x_5314_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5314_, 0, v___x_5296_);
lean_ctor_set(v___x_5314_, 1, v___x_5313_);
v___x_5315_ = l_Lean_Syntax_node5(v___x_5296_, v___x_5297_, v___x_5308_, v_a_5287_, v___x_5310_, v___x_5312_, v___x_5314_);
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 0, v___x_5315_);
v___x_5317_ = v___x_5290_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v___x_5315_);
lean_ctor_set(v_reuseFailAlloc_5318_, 1, v_a_5288_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
return v___x_5317_;
}
}
}
else
{
lean_object* v_a_5320_; lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5328_; 
lean_dec(v_type_5277_);
v_a_5320_ = lean_ctor_get(v___x_5286_, 0);
v_a_5321_ = lean_ctor_get(v___x_5286_, 1);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5286_);
if (v_isSharedCheck_5328_ == 0)
{
v___x_5323_ = v___x_5286_;
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_inc(v_a_5320_);
lean_dec(v___x_5286_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5326_; 
if (v_isShared_5324_ == 0)
{
v___x_5326_ = v___x_5323_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5320_);
lean_ctor_set(v_reuseFailAlloc_5327_, 1, v_a_5321_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5329_, lean_object* v_type_5330_, lean_object* v_ofInterpFn_5331_, lean_object* v_ofLitFn_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_){
_start:
{
lean_object* v_res_5335_; 
v_res_5335_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5329_, v_type_5330_, v_ofInterpFn_5331_, v_ofLitFn_5332_, v_a_5333_, v_a_5334_);
lean_dec_ref(v_a_5333_);
lean_dec(v_interpStr_5329_);
return v_res_5335_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5336_){
_start:
{
lean_object* v___x_5337_; lean_object* v___x_5338_; 
v___x_5337_ = lean_unsigned_to_nat(1u);
v___x_5338_ = l_Lean_Syntax_getArg(v_stx_5336_, v___x_5337_);
if (lean_obj_tag(v___x_5338_) == 1)
{
lean_object* v_kind_5339_; 
v_kind_5339_ = lean_ctor_get(v___x_5338_, 1);
lean_inc(v_kind_5339_);
if (lean_obj_tag(v_kind_5339_) == 1)
{
lean_object* v_pre_5340_; 
v_pre_5340_ = lean_ctor_get(v_kind_5339_, 0);
lean_inc(v_pre_5340_);
if (lean_obj_tag(v_pre_5340_) == 1)
{
lean_object* v_pre_5341_; 
v_pre_5341_ = lean_ctor_get(v_pre_5340_, 0);
lean_inc(v_pre_5341_);
if (lean_obj_tag(v_pre_5341_) == 1)
{
lean_object* v_pre_5342_; 
v_pre_5342_ = lean_ctor_get(v_pre_5341_, 0);
lean_inc(v_pre_5342_);
if (lean_obj_tag(v_pre_5342_) == 1)
{
lean_object* v_pre_5343_; 
v_pre_5343_ = lean_ctor_get(v_pre_5342_, 0);
if (lean_obj_tag(v_pre_5343_) == 0)
{
lean_object* v_args_5344_; lean_object* v_str_5345_; lean_object* v_str_5346_; lean_object* v_str_5347_; lean_object* v_str_5348_; lean_object* v___x_5349_; uint8_t v___x_5350_; 
v_args_5344_ = lean_ctor_get(v___x_5338_, 2);
lean_inc_ref(v_args_5344_);
lean_dec_ref_known(v___x_5338_, 3);
v_str_5345_ = lean_ctor_get(v_kind_5339_, 1);
lean_inc_ref(v_str_5345_);
lean_dec_ref_known(v_kind_5339_, 2);
v_str_5346_ = lean_ctor_get(v_pre_5340_, 1);
lean_inc_ref(v_str_5346_);
lean_dec_ref_known(v_pre_5340_, 2);
v_str_5347_ = lean_ctor_get(v_pre_5341_, 1);
lean_inc_ref(v_str_5347_);
lean_dec_ref_known(v_pre_5341_, 2);
v_str_5348_ = lean_ctor_get(v_pre_5342_, 1);
lean_inc_ref(v_str_5348_);
lean_dec_ref_known(v_pre_5342_, 2);
v___x_5349_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__0));
v___x_5350_ = lean_string_dec_eq(v_str_5348_, v___x_5349_);
lean_dec_ref(v_str_5348_);
if (v___x_5350_ == 0)
{
lean_object* v___x_5351_; 
lean_dec_ref(v_str_5347_);
lean_dec_ref(v_str_5346_);
lean_dec_ref(v_str_5345_);
lean_dec_ref(v_args_5344_);
v___x_5351_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5351_;
}
else
{
lean_object* v___x_5352_; uint8_t v___x_5353_; 
v___x_5352_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__1));
v___x_5353_ = lean_string_dec_eq(v_str_5347_, v___x_5352_);
lean_dec_ref(v_str_5347_);
if (v___x_5353_ == 0)
{
lean_object* v___x_5354_; 
lean_dec_ref(v_str_5346_);
lean_dec_ref(v_str_5345_);
lean_dec_ref(v_args_5344_);
v___x_5354_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5354_;
}
else
{
lean_object* v___x_5355_; uint8_t v___x_5356_; 
v___x_5355_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__0));
v___x_5356_ = lean_string_dec_eq(v_str_5346_, v___x_5355_);
lean_dec_ref(v_str_5346_);
if (v___x_5356_ == 0)
{
lean_object* v___x_5357_; 
lean_dec_ref(v_str_5345_);
lean_dec_ref(v_args_5344_);
v___x_5357_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5357_;
}
else
{
lean_object* v___x_5358_; uint8_t v___x_5359_; 
v___x_5358_ = ((lean_object*)(l_Lean_mkMarkdownDocCommentFrom___closed__1));
v___x_5359_ = lean_string_dec_eq(v_str_5345_, v___x_5358_);
lean_dec_ref(v_str_5345_);
if (v___x_5359_ == 0)
{
lean_object* v___x_5360_; 
lean_dec_ref(v_args_5344_);
v___x_5360_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5360_;
}
else
{
lean_object* v___x_5361_; lean_object* v___x_5362_; uint8_t v___x_5363_; 
v___x_5361_ = lean_array_get_size(v_args_5344_);
v___x_5362_ = lean_unsigned_to_nat(2u);
v___x_5363_ = lean_nat_dec_eq(v___x_5361_, v___x_5362_);
if (v___x_5363_ == 0)
{
lean_object* v___x_5364_; 
lean_dec_ref(v_args_5344_);
v___x_5364_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5364_;
}
else
{
lean_object* v___x_5365_; lean_object* v___x_5366_; 
v___x_5365_ = lean_unsigned_to_nat(0u);
v___x_5366_ = lean_array_fget(v_args_5344_, v___x_5365_);
lean_dec_ref(v_args_5344_);
if (lean_obj_tag(v___x_5366_) == 2)
{
lean_object* v_val_5367_; 
v_val_5367_ = lean_ctor_get(v___x_5366_, 1);
lean_inc_ref(v_val_5367_);
lean_dec_ref_known(v___x_5366_, 2);
return v_val_5367_;
}
else
{
lean_object* v___x_5368_; 
lean_dec(v___x_5366_);
v___x_5368_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5368_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5369_; 
lean_dec_ref_known(v_pre_5342_, 2);
lean_dec_ref_known(v_pre_5341_, 2);
lean_dec_ref_known(v_pre_5340_, 2);
lean_dec_ref_known(v_kind_5339_, 2);
lean_dec_ref_known(v___x_5338_, 3);
v___x_5369_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5369_;
}
}
else
{
lean_object* v___x_5370_; 
lean_dec(v_pre_5342_);
lean_dec_ref_known(v_pre_5341_, 2);
lean_dec_ref_known(v_pre_5340_, 2);
lean_dec_ref_known(v_kind_5339_, 2);
lean_dec_ref_known(v___x_5338_, 3);
v___x_5370_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5370_;
}
}
else
{
lean_object* v___x_5371_; 
lean_dec_ref_known(v_pre_5340_, 2);
lean_dec(v_pre_5341_);
lean_dec_ref_known(v_kind_5339_, 2);
lean_dec_ref_known(v___x_5338_, 3);
v___x_5371_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5371_;
}
}
else
{
lean_object* v___x_5372_; 
lean_dec_ref_known(v_kind_5339_, 2);
lean_dec(v_pre_5340_);
lean_dec_ref_known(v___x_5338_, 3);
v___x_5372_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5372_;
}
}
else
{
lean_object* v___x_5373_; 
lean_dec(v_kind_5339_);
lean_dec_ref_known(v___x_5338_, 3);
v___x_5373_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5373_;
}
}
else
{
lean_object* v___x_5374_; 
lean_dec(v___x_5338_);
v___x_5374_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* v_stx_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l_Lean_TSyntax_getDocString(v_stx_5375_);
lean_dec(v_stx_5375_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5395_, lean_object* v_prec_5396_){
_start:
{
lean_object* v___y_5398_; lean_object* v___y_5405_; lean_object* v___y_5412_; lean_object* v___y_5419_; lean_object* v___y_5426_; lean_object* v___y_5433_; 
switch(v_x_5395_)
{
case 0:
{
lean_object* v___x_5439_; uint8_t v___x_5440_; 
v___x_5439_ = lean_unsigned_to_nat(1024u);
v___x_5440_ = lean_nat_dec_le(v___x_5439_, v_prec_5396_);
if (v___x_5440_ == 0)
{
lean_object* v___x_5441_; 
v___x_5441_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5398_ = v___x_5441_;
goto v___jp_5397_;
}
else
{
lean_object* v___x_5442_; 
v___x_5442_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5398_ = v___x_5442_;
goto v___jp_5397_;
}
}
case 1:
{
lean_object* v___x_5443_; uint8_t v___x_5444_; 
v___x_5443_ = lean_unsigned_to_nat(1024u);
v___x_5444_ = lean_nat_dec_le(v___x_5443_, v_prec_5396_);
if (v___x_5444_ == 0)
{
lean_object* v___x_5445_; 
v___x_5445_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5405_ = v___x_5445_;
goto v___jp_5404_;
}
else
{
lean_object* v___x_5446_; 
v___x_5446_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5405_ = v___x_5446_;
goto v___jp_5404_;
}
}
case 2:
{
lean_object* v___x_5447_; uint8_t v___x_5448_; 
v___x_5447_ = lean_unsigned_to_nat(1024u);
v___x_5448_ = lean_nat_dec_le(v___x_5447_, v_prec_5396_);
if (v___x_5448_ == 0)
{
lean_object* v___x_5449_; 
v___x_5449_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5412_ = v___x_5449_;
goto v___jp_5411_;
}
else
{
lean_object* v___x_5450_; 
v___x_5450_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5412_ = v___x_5450_;
goto v___jp_5411_;
}
}
case 3:
{
lean_object* v___x_5451_; uint8_t v___x_5452_; 
v___x_5451_ = lean_unsigned_to_nat(1024u);
v___x_5452_ = lean_nat_dec_le(v___x_5451_, v_prec_5396_);
if (v___x_5452_ == 0)
{
lean_object* v___x_5453_; 
v___x_5453_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5419_ = v___x_5453_;
goto v___jp_5418_;
}
else
{
lean_object* v___x_5454_; 
v___x_5454_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5419_ = v___x_5454_;
goto v___jp_5418_;
}
}
case 4:
{
lean_object* v___x_5455_; uint8_t v___x_5456_; 
v___x_5455_ = lean_unsigned_to_nat(1024u);
v___x_5456_ = lean_nat_dec_le(v___x_5455_, v_prec_5396_);
if (v___x_5456_ == 0)
{
lean_object* v___x_5457_; 
v___x_5457_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5426_ = v___x_5457_;
goto v___jp_5425_;
}
else
{
lean_object* v___x_5458_; 
v___x_5458_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5426_ = v___x_5458_;
goto v___jp_5425_;
}
}
default: 
{
lean_object* v___x_5459_; uint8_t v___x_5460_; 
v___x_5459_ = lean_unsigned_to_nat(1024u);
v___x_5460_ = lean_nat_dec_le(v___x_5459_, v_prec_5396_);
if (v___x_5460_ == 0)
{
lean_object* v___x_5461_; 
v___x_5461_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5433_ = v___x_5461_;
goto v___jp_5432_;
}
else
{
lean_object* v___x_5462_; 
v___x_5462_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5433_ = v___x_5462_;
goto v___jp_5432_;
}
}
}
v___jp_5397_:
{
lean_object* v___x_5399_; lean_object* v___x_5400_; uint8_t v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; 
v___x_5399_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
lean_inc(v___y_5398_);
v___x_5400_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5400_, 0, v___y_5398_);
lean_ctor_set(v___x_5400_, 1, v___x_5399_);
v___x_5401_ = 0;
v___x_5402_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5402_, 0, v___x_5400_);
lean_ctor_set_uint8(v___x_5402_, sizeof(void*)*1, v___x_5401_);
v___x_5403_ = l_Repr_addAppParen(v___x_5402_, v_prec_5396_);
return v___x_5403_;
}
v___jp_5404_:
{
lean_object* v___x_5406_; lean_object* v___x_5407_; uint8_t v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; 
v___x_5406_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__3));
lean_inc(v___y_5405_);
v___x_5407_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5407_, 0, v___y_5405_);
lean_ctor_set(v___x_5407_, 1, v___x_5406_);
v___x_5408_ = 0;
v___x_5409_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5409_, 0, v___x_5407_);
lean_ctor_set_uint8(v___x_5409_, sizeof(void*)*1, v___x_5408_);
v___x_5410_ = l_Repr_addAppParen(v___x_5409_, v_prec_5396_);
return v___x_5410_;
}
v___jp_5411_:
{
lean_object* v___x_5413_; lean_object* v___x_5414_; uint8_t v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; 
v___x_5413_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__5));
lean_inc(v___y_5412_);
v___x_5414_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5414_, 0, v___y_5412_);
lean_ctor_set(v___x_5414_, 1, v___x_5413_);
v___x_5415_ = 0;
v___x_5416_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5416_, 0, v___x_5414_);
lean_ctor_set_uint8(v___x_5416_, sizeof(void*)*1, v___x_5415_);
v___x_5417_ = l_Repr_addAppParen(v___x_5416_, v_prec_5396_);
return v___x_5417_;
}
v___jp_5418_:
{
lean_object* v___x_5420_; lean_object* v___x_5421_; uint8_t v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; 
v___x_5420_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__7));
lean_inc(v___y_5419_);
v___x_5421_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5421_, 0, v___y_5419_);
lean_ctor_set(v___x_5421_, 1, v___x_5420_);
v___x_5422_ = 0;
v___x_5423_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5423_, 0, v___x_5421_);
lean_ctor_set_uint8(v___x_5423_, sizeof(void*)*1, v___x_5422_);
v___x_5424_ = l_Repr_addAppParen(v___x_5423_, v_prec_5396_);
return v___x_5424_;
}
v___jp_5425_:
{
lean_object* v___x_5427_; lean_object* v___x_5428_; uint8_t v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___x_5427_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__9));
lean_inc(v___y_5426_);
v___x_5428_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5428_, 0, v___y_5426_);
lean_ctor_set(v___x_5428_, 1, v___x_5427_);
v___x_5429_ = 0;
v___x_5430_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5430_, 0, v___x_5428_);
lean_ctor_set_uint8(v___x_5430_, sizeof(void*)*1, v___x_5429_);
v___x_5431_ = l_Repr_addAppParen(v___x_5430_, v_prec_5396_);
return v___x_5431_;
}
v___jp_5432_:
{
lean_object* v___x_5434_; lean_object* v___x_5435_; uint8_t v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; 
v___x_5434_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__11));
lean_inc(v___y_5433_);
v___x_5435_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5435_, 0, v___y_5433_);
lean_ctor_set(v___x_5435_, 1, v___x_5434_);
v___x_5436_ = 0;
v___x_5437_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5437_, 0, v___x_5435_);
lean_ctor_set_uint8(v___x_5437_, sizeof(void*)*1, v___x_5436_);
v___x_5438_ = l_Repr_addAppParen(v___x_5437_, v_prec_5396_);
return v___x_5438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5463_, lean_object* v_prec_5464_){
_start:
{
uint8_t v_x_329__boxed_5465_; lean_object* v_res_5466_; 
v_x_329__boxed_5465_ = lean_unbox(v_x_5463_);
v_res_5466_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_329__boxed_5465_, v_prec_5464_);
lean_dec(v_prec_5464_);
return v_res_5466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5478_, lean_object* v_prec_5479_){
_start:
{
lean_object* v___y_5481_; lean_object* v___y_5488_; lean_object* v___y_5495_; 
switch(v_x_5478_)
{
case 0:
{
lean_object* v___x_5501_; uint8_t v___x_5502_; 
v___x_5501_ = lean_unsigned_to_nat(1024u);
v___x_5502_ = lean_nat_dec_le(v___x_5501_, v_prec_5479_);
if (v___x_5502_ == 0)
{
lean_object* v___x_5503_; 
v___x_5503_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5481_ = v___x_5503_;
goto v___jp_5480_;
}
else
{
lean_object* v___x_5504_; 
v___x_5504_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5481_ = v___x_5504_;
goto v___jp_5480_;
}
}
case 1:
{
lean_object* v___x_5505_; uint8_t v___x_5506_; 
v___x_5505_ = lean_unsigned_to_nat(1024u);
v___x_5506_ = lean_nat_dec_le(v___x_5505_, v_prec_5479_);
if (v___x_5506_ == 0)
{
lean_object* v___x_5507_; 
v___x_5507_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5488_ = v___x_5507_;
goto v___jp_5487_;
}
else
{
lean_object* v___x_5508_; 
v___x_5508_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5488_ = v___x_5508_;
goto v___jp_5487_;
}
}
default: 
{
lean_object* v___x_5509_; uint8_t v___x_5510_; 
v___x_5509_ = lean_unsigned_to_nat(1024u);
v___x_5510_ = lean_nat_dec_le(v___x_5509_, v_prec_5479_);
if (v___x_5510_ == 0)
{
lean_object* v___x_5511_; 
v___x_5511_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5495_ = v___x_5511_;
goto v___jp_5494_;
}
else
{
lean_object* v___x_5512_; 
v___x_5512_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5495_ = v___x_5512_;
goto v___jp_5494_;
}
}
}
v___jp_5480_:
{
lean_object* v___x_5482_; lean_object* v___x_5483_; uint8_t v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; 
v___x_5482_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
lean_inc(v___y_5481_);
v___x_5483_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5483_, 0, v___y_5481_);
lean_ctor_set(v___x_5483_, 1, v___x_5482_);
v___x_5484_ = 0;
v___x_5485_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5485_, 0, v___x_5483_);
lean_ctor_set_uint8(v___x_5485_, sizeof(void*)*1, v___x_5484_);
v___x_5486_ = l_Repr_addAppParen(v___x_5485_, v_prec_5479_);
return v___x_5486_;
}
v___jp_5487_:
{
lean_object* v___x_5489_; lean_object* v___x_5490_; uint8_t v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; 
v___x_5489_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
lean_inc(v___y_5488_);
v___x_5490_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5490_, 0, v___y_5488_);
lean_ctor_set(v___x_5490_, 1, v___x_5489_);
v___x_5491_ = 0;
v___x_5492_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5492_, 0, v___x_5490_);
lean_ctor_set_uint8(v___x_5492_, sizeof(void*)*1, v___x_5491_);
v___x_5493_ = l_Repr_addAppParen(v___x_5492_, v_prec_5479_);
return v___x_5493_;
}
v___jp_5494_:
{
lean_object* v___x_5496_; lean_object* v___x_5497_; uint8_t v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; 
v___x_5496_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
lean_inc(v___y_5495_);
v___x_5497_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5497_, 0, v___y_5495_);
lean_ctor_set(v___x_5497_, 1, v___x_5496_);
v___x_5498_ = 0;
v___x_5499_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5499_, 0, v___x_5497_);
lean_ctor_set_uint8(v___x_5499_, sizeof(void*)*1, v___x_5498_);
v___x_5500_ = l_Repr_addAppParen(v___x_5499_, v_prec_5479_);
return v___x_5500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5513_, lean_object* v_prec_5514_){
_start:
{
uint8_t v_x_167__boxed_5515_; lean_object* v_res_5516_; 
v_x_167__boxed_5515_ = lean_unbox(v_x_5513_);
v_res_5516_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_167__boxed_5515_, v_prec_5514_);
lean_dec(v_prec_5514_);
return v_res_5516_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5528_; lean_object* v___x_5529_; 
v___x_5528_ = lean_unsigned_to_nat(8u);
v___x_5529_ = lean_nat_to_int(v___x_5528_);
return v___x_5529_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5539_; lean_object* v___x_5540_; 
v___x_5539_ = lean_unsigned_to_nat(13u);
v___x_5540_ = lean_nat_to_int(v___x_5539_);
return v___x_5540_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5550_; lean_object* v___x_5551_; 
v___x_5550_ = lean_unsigned_to_nat(10u);
v___x_5551_ = lean_nat_to_int(v___x_5550_);
return v___x_5551_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5555_; lean_object* v___x_5556_; 
v___x_5555_ = lean_unsigned_to_nat(14u);
v___x_5556_ = lean_nat_to_int(v___x_5555_);
return v___x_5556_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5560_; lean_object* v___x_5561_; 
v___x_5560_ = lean_unsigned_to_nat(19u);
v___x_5561_ = lean_nat_to_int(v___x_5560_);
return v___x_5561_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5565_; lean_object* v___x_5566_; 
v___x_5565_ = lean_unsigned_to_nat(20u);
v___x_5566_ = lean_nat_to_int(v___x_5565_);
return v___x_5566_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5573_; lean_object* v___x_5574_; 
v___x_5573_ = lean_unsigned_to_nat(9u);
v___x_5574_ = lean_nat_to_int(v___x_5573_);
return v___x_5574_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5581_; lean_object* v___x_5582_; 
v___x_5581_ = lean_unsigned_to_nat(12u);
v___x_5582_ = lean_nat_to_int(v___x_5581_);
return v___x_5582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5589_){
_start:
{
uint8_t v_zeta_5590_; uint8_t v_beta_5591_; uint8_t v_eta_5592_; uint8_t v_etaStruct_5593_; uint8_t v_iota_5594_; uint8_t v_proj_5595_; uint8_t v_decide_5596_; uint8_t v_autoUnfold_5597_; uint8_t v_failIfUnchanged_5598_; uint8_t v_unfoldPartialApp_5599_; uint8_t v_zetaDelta_5600_; uint8_t v_index_5601_; uint8_t v_zetaUnused_5602_; uint8_t v_zetaHave_5603_; uint8_t v_locals_5604_; uint8_t v_instances_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; uint8_t v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; 
v_zeta_5590_ = lean_ctor_get_uint8(v_x_5589_, 0);
v_beta_5591_ = lean_ctor_get_uint8(v_x_5589_, 1);
v_eta_5592_ = lean_ctor_get_uint8(v_x_5589_, 2);
v_etaStruct_5593_ = lean_ctor_get_uint8(v_x_5589_, 3);
v_iota_5594_ = lean_ctor_get_uint8(v_x_5589_, 4);
v_proj_5595_ = lean_ctor_get_uint8(v_x_5589_, 5);
v_decide_5596_ = lean_ctor_get_uint8(v_x_5589_, 6);
v_autoUnfold_5597_ = lean_ctor_get_uint8(v_x_5589_, 7);
v_failIfUnchanged_5598_ = lean_ctor_get_uint8(v_x_5589_, 8);
v_unfoldPartialApp_5599_ = lean_ctor_get_uint8(v_x_5589_, 9);
v_zetaDelta_5600_ = lean_ctor_get_uint8(v_x_5589_, 10);
v_index_5601_ = lean_ctor_get_uint8(v_x_5589_, 11);
v_zetaUnused_5602_ = lean_ctor_get_uint8(v_x_5589_, 12);
v_zetaHave_5603_ = lean_ctor_get_uint8(v_x_5589_, 13);
v_locals_5604_ = lean_ctor_get_uint8(v_x_5589_, 14);
v_instances_5605_ = lean_ctor_get_uint8(v_x_5589_, 15);
v___x_5606_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5607_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5608_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5609_ = lean_unsigned_to_nat(0u);
v___x_5610_ = l_Bool_repr___redArg(v_zeta_5590_);
v___x_5611_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5611_, 0, v___x_5608_);
lean_ctor_set(v___x_5611_, 1, v___x_5610_);
v___x_5612_ = 0;
v___x_5613_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5613_, 0, v___x_5611_);
lean_ctor_set_uint8(v___x_5613_, sizeof(void*)*1, v___x_5612_);
v___x_5614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5614_, 0, v___x_5607_);
lean_ctor_set(v___x_5614_, 1, v___x_5613_);
v___x_5615_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5614_);
lean_ctor_set(v___x_5616_, 1, v___x_5615_);
v___x_5617_ = lean_box(1);
v___x_5618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5618_, 0, v___x_5616_);
lean_ctor_set(v___x_5618_, 1, v___x_5617_);
v___x_5619_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5620_, 0, v___x_5618_);
lean_ctor_set(v___x_5620_, 1, v___x_5619_);
v___x_5621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5621_, 0, v___x_5620_);
lean_ctor_set(v___x_5621_, 1, v___x_5606_);
v___x_5622_ = l_Bool_repr___redArg(v_beta_5591_);
v___x_5623_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5623_, 0, v___x_5608_);
lean_ctor_set(v___x_5623_, 1, v___x_5622_);
v___x_5624_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5624_, 0, v___x_5623_);
lean_ctor_set_uint8(v___x_5624_, sizeof(void*)*1, v___x_5612_);
v___x_5625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5625_, 0, v___x_5621_);
lean_ctor_set(v___x_5625_, 1, v___x_5624_);
v___x_5626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5626_, 0, v___x_5625_);
lean_ctor_set(v___x_5626_, 1, v___x_5615_);
v___x_5627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5627_, 0, v___x_5626_);
lean_ctor_set(v___x_5627_, 1, v___x_5617_);
v___x_5628_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5629_, 0, v___x_5627_);
lean_ctor_set(v___x_5629_, 1, v___x_5628_);
v___x_5630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5630_, 0, v___x_5629_);
lean_ctor_set(v___x_5630_, 1, v___x_5606_);
v___x_5631_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5632_ = l_Bool_repr___redArg(v_eta_5592_);
v___x_5633_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5633_, 0, v___x_5631_);
lean_ctor_set(v___x_5633_, 1, v___x_5632_);
v___x_5634_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5634_, 0, v___x_5633_);
lean_ctor_set_uint8(v___x_5634_, sizeof(void*)*1, v___x_5612_);
v___x_5635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5635_, 0, v___x_5630_);
lean_ctor_set(v___x_5635_, 1, v___x_5634_);
v___x_5636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5635_);
lean_ctor_set(v___x_5636_, 1, v___x_5615_);
v___x_5637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5637_, 0, v___x_5636_);
lean_ctor_set(v___x_5637_, 1, v___x_5617_);
v___x_5638_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5639_, 0, v___x_5637_);
lean_ctor_set(v___x_5639_, 1, v___x_5638_);
v___x_5640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5640_, 0, v___x_5639_);
lean_ctor_set(v___x_5640_, 1, v___x_5606_);
v___x_5641_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5642_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5593_, v___x_5609_);
v___x_5643_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5641_);
lean_ctor_set(v___x_5643_, 1, v___x_5642_);
v___x_5644_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5644_, 0, v___x_5643_);
lean_ctor_set_uint8(v___x_5644_, sizeof(void*)*1, v___x_5612_);
v___x_5645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5640_);
lean_ctor_set(v___x_5645_, 1, v___x_5644_);
v___x_5646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5646_, 0, v___x_5645_);
lean_ctor_set(v___x_5646_, 1, v___x_5615_);
v___x_5647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5647_, 0, v___x_5646_);
lean_ctor_set(v___x_5647_, 1, v___x_5617_);
v___x_5648_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5649_, 0, v___x_5647_);
lean_ctor_set(v___x_5649_, 1, v___x_5648_);
v___x_5650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5650_, 0, v___x_5649_);
lean_ctor_set(v___x_5650_, 1, v___x_5606_);
v___x_5651_ = l_Bool_repr___redArg(v_iota_5594_);
v___x_5652_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5652_, 0, v___x_5608_);
lean_ctor_set(v___x_5652_, 1, v___x_5651_);
v___x_5653_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5653_, 0, v___x_5652_);
lean_ctor_set_uint8(v___x_5653_, sizeof(void*)*1, v___x_5612_);
v___x_5654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5654_, 0, v___x_5650_);
lean_ctor_set(v___x_5654_, 1, v___x_5653_);
v___x_5655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5655_, 0, v___x_5654_);
lean_ctor_set(v___x_5655_, 1, v___x_5615_);
v___x_5656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5656_, 0, v___x_5655_);
lean_ctor_set(v___x_5656_, 1, v___x_5617_);
v___x_5657_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5658_, 0, v___x_5656_);
lean_ctor_set(v___x_5658_, 1, v___x_5657_);
v___x_5659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5659_, 0, v___x_5658_);
lean_ctor_set(v___x_5659_, 1, v___x_5606_);
v___x_5660_ = l_Bool_repr___redArg(v_proj_5595_);
v___x_5661_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5661_, 0, v___x_5608_);
lean_ctor_set(v___x_5661_, 1, v___x_5660_);
v___x_5662_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5662_, 0, v___x_5661_);
lean_ctor_set_uint8(v___x_5662_, sizeof(void*)*1, v___x_5612_);
v___x_5663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5659_);
lean_ctor_set(v___x_5663_, 1, v___x_5662_);
v___x_5664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5663_);
lean_ctor_set(v___x_5664_, 1, v___x_5615_);
v___x_5665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5665_, 0, v___x_5664_);
lean_ctor_set(v___x_5665_, 1, v___x_5617_);
v___x_5666_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5667_, 0, v___x_5665_);
lean_ctor_set(v___x_5667_, 1, v___x_5666_);
v___x_5668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5667_);
lean_ctor_set(v___x_5668_, 1, v___x_5606_);
v___x_5669_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5670_ = l_Bool_repr___redArg(v_decide_5596_);
v___x_5671_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5671_, 0, v___x_5669_);
lean_ctor_set(v___x_5671_, 1, v___x_5670_);
v___x_5672_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5672_, 0, v___x_5671_);
lean_ctor_set_uint8(v___x_5672_, sizeof(void*)*1, v___x_5612_);
v___x_5673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5673_, 0, v___x_5668_);
lean_ctor_set(v___x_5673_, 1, v___x_5672_);
v___x_5674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5674_, 0, v___x_5673_);
lean_ctor_set(v___x_5674_, 1, v___x_5615_);
v___x_5675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5675_, 0, v___x_5674_);
lean_ctor_set(v___x_5675_, 1, v___x_5617_);
v___x_5676_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5677_, 0, v___x_5675_);
lean_ctor_set(v___x_5677_, 1, v___x_5676_);
v___x_5678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5678_, 0, v___x_5677_);
lean_ctor_set(v___x_5678_, 1, v___x_5606_);
v___x_5679_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5680_ = l_Bool_repr___redArg(v_autoUnfold_5597_);
v___x_5681_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5681_, 0, v___x_5679_);
lean_ctor_set(v___x_5681_, 1, v___x_5680_);
v___x_5682_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5682_, 0, v___x_5681_);
lean_ctor_set_uint8(v___x_5682_, sizeof(void*)*1, v___x_5612_);
v___x_5683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5683_, 0, v___x_5678_);
lean_ctor_set(v___x_5683_, 1, v___x_5682_);
v___x_5684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5683_);
lean_ctor_set(v___x_5684_, 1, v___x_5615_);
v___x_5685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5685_, 0, v___x_5684_);
lean_ctor_set(v___x_5685_, 1, v___x_5617_);
v___x_5686_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5687_, 0, v___x_5685_);
lean_ctor_set(v___x_5687_, 1, v___x_5686_);
v___x_5688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5687_);
lean_ctor_set(v___x_5688_, 1, v___x_5606_);
v___x_5689_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5690_ = l_Bool_repr___redArg(v_failIfUnchanged_5598_);
v___x_5691_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5689_);
lean_ctor_set(v___x_5691_, 1, v___x_5690_);
v___x_5692_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5692_, 0, v___x_5691_);
lean_ctor_set_uint8(v___x_5692_, sizeof(void*)*1, v___x_5612_);
v___x_5693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5693_, 0, v___x_5688_);
lean_ctor_set(v___x_5693_, 1, v___x_5692_);
v___x_5694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5693_);
lean_ctor_set(v___x_5694_, 1, v___x_5615_);
v___x_5695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5695_, 0, v___x_5694_);
lean_ctor_set(v___x_5695_, 1, v___x_5617_);
v___x_5696_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5697_, 0, v___x_5695_);
lean_ctor_set(v___x_5697_, 1, v___x_5696_);
v___x_5698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5697_);
lean_ctor_set(v___x_5698_, 1, v___x_5606_);
v___x_5699_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5700_ = l_Bool_repr___redArg(v_unfoldPartialApp_5599_);
v___x_5701_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5701_, 0, v___x_5699_);
lean_ctor_set(v___x_5701_, 1, v___x_5700_);
v___x_5702_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5702_, 0, v___x_5701_);
lean_ctor_set_uint8(v___x_5702_, sizeof(void*)*1, v___x_5612_);
v___x_5703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5703_, 0, v___x_5698_);
lean_ctor_set(v___x_5703_, 1, v___x_5702_);
v___x_5704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5704_, 0, v___x_5703_);
lean_ctor_set(v___x_5704_, 1, v___x_5615_);
v___x_5705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5705_, 0, v___x_5704_);
lean_ctor_set(v___x_5705_, 1, v___x_5617_);
v___x_5706_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5707_, 0, v___x_5705_);
lean_ctor_set(v___x_5707_, 1, v___x_5706_);
v___x_5708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5708_, 0, v___x_5707_);
lean_ctor_set(v___x_5708_, 1, v___x_5606_);
v___x_5709_ = l_Bool_repr___redArg(v_zetaDelta_5600_);
v___x_5710_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5710_, 0, v___x_5641_);
lean_ctor_set(v___x_5710_, 1, v___x_5709_);
v___x_5711_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5711_, 0, v___x_5710_);
lean_ctor_set_uint8(v___x_5711_, sizeof(void*)*1, v___x_5612_);
v___x_5712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5712_, 0, v___x_5708_);
lean_ctor_set(v___x_5712_, 1, v___x_5711_);
v___x_5713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5712_);
lean_ctor_set(v___x_5713_, 1, v___x_5615_);
v___x_5714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5713_);
lean_ctor_set(v___x_5714_, 1, v___x_5617_);
v___x_5715_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5716_, 0, v___x_5714_);
lean_ctor_set(v___x_5716_, 1, v___x_5715_);
v___x_5717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5716_);
lean_ctor_set(v___x_5717_, 1, v___x_5606_);
v___x_5718_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5719_ = l_Bool_repr___redArg(v_index_5601_);
v___x_5720_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5720_, 0, v___x_5718_);
lean_ctor_set(v___x_5720_, 1, v___x_5719_);
v___x_5721_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5721_, 0, v___x_5720_);
lean_ctor_set_uint8(v___x_5721_, sizeof(void*)*1, v___x_5612_);
v___x_5722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5722_, 0, v___x_5717_);
lean_ctor_set(v___x_5722_, 1, v___x_5721_);
v___x_5723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5723_, 0, v___x_5722_);
lean_ctor_set(v___x_5723_, 1, v___x_5615_);
v___x_5724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5724_, 0, v___x_5723_);
lean_ctor_set(v___x_5724_, 1, v___x_5617_);
v___x_5725_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5726_, 0, v___x_5724_);
lean_ctor_set(v___x_5726_, 1, v___x_5725_);
v___x_5727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5727_, 0, v___x_5726_);
lean_ctor_set(v___x_5727_, 1, v___x_5606_);
v___x_5728_ = l_Bool_repr___redArg(v_zetaUnused_5602_);
v___x_5729_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5679_);
lean_ctor_set(v___x_5729_, 1, v___x_5728_);
v___x_5730_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5730_, 0, v___x_5729_);
lean_ctor_set_uint8(v___x_5730_, sizeof(void*)*1, v___x_5612_);
v___x_5731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5731_, 0, v___x_5727_);
lean_ctor_set(v___x_5731_, 1, v___x_5730_);
v___x_5732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5731_);
lean_ctor_set(v___x_5732_, 1, v___x_5615_);
v___x_5733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5733_, 0, v___x_5732_);
lean_ctor_set(v___x_5733_, 1, v___x_5617_);
v___x_5734_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5735_, 0, v___x_5733_);
lean_ctor_set(v___x_5735_, 1, v___x_5734_);
v___x_5736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5735_);
lean_ctor_set(v___x_5736_, 1, v___x_5606_);
v___x_5737_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5738_ = l_Bool_repr___redArg(v_zetaHave_5603_);
v___x_5739_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5739_, 0, v___x_5737_);
lean_ctor_set(v___x_5739_, 1, v___x_5738_);
v___x_5740_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5740_, 0, v___x_5739_);
lean_ctor_set_uint8(v___x_5740_, sizeof(void*)*1, v___x_5612_);
v___x_5741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5741_, 0, v___x_5736_);
lean_ctor_set(v___x_5741_, 1, v___x_5740_);
v___x_5742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5742_, 0, v___x_5741_);
lean_ctor_set(v___x_5742_, 1, v___x_5615_);
v___x_5743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5742_);
lean_ctor_set(v___x_5743_, 1, v___x_5617_);
v___x_5744_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5745_, 0, v___x_5743_);
lean_ctor_set(v___x_5745_, 1, v___x_5744_);
v___x_5746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5746_, 0, v___x_5745_);
lean_ctor_set(v___x_5746_, 1, v___x_5606_);
v___x_5747_ = l_Bool_repr___redArg(v_locals_5604_);
v___x_5748_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5748_, 0, v___x_5669_);
lean_ctor_set(v___x_5748_, 1, v___x_5747_);
v___x_5749_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5749_, 0, v___x_5748_);
lean_ctor_set_uint8(v___x_5749_, sizeof(void*)*1, v___x_5612_);
v___x_5750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5750_, 0, v___x_5746_);
lean_ctor_set(v___x_5750_, 1, v___x_5749_);
v___x_5751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5750_);
lean_ctor_set(v___x_5751_, 1, v___x_5615_);
v___x_5752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5752_, 0, v___x_5751_);
lean_ctor_set(v___x_5752_, 1, v___x_5617_);
v___x_5753_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5754_, 0, v___x_5752_);
lean_ctor_set(v___x_5754_, 1, v___x_5753_);
v___x_5755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5755_, 0, v___x_5754_);
lean_ctor_set(v___x_5755_, 1, v___x_5606_);
v___x_5756_ = l_Bool_repr___redArg(v_instances_5605_);
v___x_5757_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5757_, 0, v___x_5641_);
lean_ctor_set(v___x_5757_, 1, v___x_5756_);
v___x_5758_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5758_, 0, v___x_5757_);
lean_ctor_set_uint8(v___x_5758_, sizeof(void*)*1, v___x_5612_);
v___x_5759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5759_, 0, v___x_5755_);
lean_ctor_set(v___x_5759_, 1, v___x_5758_);
v___x_5760_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5761_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5762_, 0, v___x_5761_);
lean_ctor_set(v___x_5762_, 1, v___x_5759_);
v___x_5763_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5764_, 0, v___x_5762_);
lean_ctor_set(v___x_5764_, 1, v___x_5763_);
v___x_5765_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5765_, 0, v___x_5760_);
lean_ctor_set(v___x_5765_, 1, v___x_5764_);
v___x_5766_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5766_, 0, v___x_5765_);
lean_ctor_set_uint8(v___x_5766_, sizeof(void*)*1, v___x_5612_);
return v___x_5766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5767_){
_start:
{
lean_object* v_res_5768_; 
v_res_5768_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5767_);
lean_dec_ref(v_x_5767_);
return v_res_5768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5769_, lean_object* v_prec_5770_){
_start:
{
lean_object* v___x_5771_; 
v___x_5771_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5769_);
return v___x_5771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5772_, lean_object* v_prec_5773_){
_start:
{
lean_object* v_res_5774_; 
v_res_5774_ = l_Lean_Meta_instReprConfig_repr(v_x_5772_, v_prec_5773_);
lean_dec(v_prec_5773_);
lean_dec_ref(v_x_5772_);
return v_res_5774_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5782_, lean_object* v_x_5783_){
_start:
{
if (lean_obj_tag(v_x_5782_) == 0)
{
lean_object* v___x_5784_; 
v___x_5784_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5784_;
}
else
{
lean_object* v_val_5785_; lean_object* v___x_5787_; uint8_t v_isShared_5788_; uint8_t v_isSharedCheck_5796_; 
v_val_5785_ = lean_ctor_get(v_x_5782_, 0);
v_isSharedCheck_5796_ = !lean_is_exclusive(v_x_5782_);
if (v_isSharedCheck_5796_ == 0)
{
v___x_5787_ = v_x_5782_;
v_isShared_5788_ = v_isSharedCheck_5796_;
goto v_resetjp_5786_;
}
else
{
lean_inc(v_val_5785_);
lean_dec(v_x_5782_);
v___x_5787_ = lean_box(0);
v_isShared_5788_ = v_isSharedCheck_5796_;
goto v_resetjp_5786_;
}
v_resetjp_5786_:
{
lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5792_; 
v___x_5789_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5790_ = l_Nat_reprFast(v_val_5785_);
if (v_isShared_5788_ == 0)
{
lean_ctor_set_tag(v___x_5787_, 3);
lean_ctor_set(v___x_5787_, 0, v___x_5790_);
v___x_5792_ = v___x_5787_;
goto v_reusejp_5791_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v___x_5790_);
v___x_5792_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5791_;
}
v_reusejp_5791_:
{
lean_object* v___x_5793_; lean_object* v___x_5794_; 
v___x_5793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5793_, 0, v___x_5789_);
lean_ctor_set(v___x_5793_, 1, v___x_5792_);
v___x_5794_ = l_Repr_addAppParen(v___x_5793_, v_x_5783_);
return v___x_5794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5797_, lean_object* v_x_5798_){
_start:
{
lean_object* v_res_5799_; 
v_res_5799_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5797_, v_x_5798_);
lean_dec(v_x_5798_);
return v_res_5799_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5812_; lean_object* v___x_5813_; 
v___x_5812_ = lean_unsigned_to_nat(21u);
v___x_5813_ = lean_nat_to_int(v___x_5812_);
return v___x_5813_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; 
v___x_5820_ = lean_unsigned_to_nat(11u);
v___x_5821_ = lean_nat_to_int(v___x_5820_);
return v___x_5821_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5837_; lean_object* v___x_5838_; 
v___x_5837_ = lean_unsigned_to_nat(23u);
v___x_5838_ = lean_nat_to_int(v___x_5837_);
return v___x_5838_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5842_; lean_object* v___x_5843_; 
v___x_5842_ = lean_unsigned_to_nat(16u);
v___x_5843_ = lean_nat_to_int(v___x_5842_);
return v___x_5843_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5850_; lean_object* v___x_5851_; 
v___x_5850_ = lean_unsigned_to_nat(15u);
v___x_5851_ = lean_nat_to_int(v___x_5850_);
return v___x_5851_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5858_; lean_object* v___x_5859_; 
v___x_5858_ = lean_unsigned_to_nat(17u);
v___x_5859_ = lean_nat_to_int(v___x_5858_);
return v___x_5859_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5866_; lean_object* v___x_5867_; 
v___x_5866_ = lean_unsigned_to_nat(18u);
v___x_5867_ = lean_nat_to_int(v___x_5866_);
return v___x_5867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5868_){
_start:
{
lean_object* v_maxSteps_5869_; lean_object* v_maxDischargeDepth_5870_; uint8_t v_contextual_5871_; uint8_t v_memoize_5872_; uint8_t v_singlePass_5873_; uint8_t v_zeta_5874_; uint8_t v_beta_5875_; uint8_t v_eta_5876_; uint8_t v_etaStruct_5877_; uint8_t v_iota_5878_; uint8_t v_proj_5879_; uint8_t v_decide_5880_; uint8_t v_arith_5881_; uint8_t v_autoUnfold_5882_; uint8_t v_dsimp_5883_; uint8_t v_failIfUnchanged_5884_; uint8_t v_ground_5885_; uint8_t v_unfoldPartialApp_5886_; uint8_t v_zetaDelta_5887_; uint8_t v_index_5888_; uint8_t v_implicitDefEqProofs_5889_; uint8_t v_zetaUnused_5890_; uint8_t v_catchRuntime_5891_; uint8_t v_zetaHave_5892_; uint8_t v_letToHave_5893_; uint8_t v_congrConsts_5894_; uint8_t v_bitVecOfNat_5895_; uint8_t v_warnExponents_5896_; uint8_t v_suggestions_5897_; lean_object* v_maxSuggestions_5898_; uint8_t v_locals_5899_; uint8_t v_instances_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; uint8_t v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; 
v_maxSteps_5869_ = lean_ctor_get(v_x_5868_, 0);
lean_inc(v_maxSteps_5869_);
v_maxDischargeDepth_5870_ = lean_ctor_get(v_x_5868_, 1);
lean_inc(v_maxDischargeDepth_5870_);
v_contextual_5871_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3);
v_memoize_5872_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 1);
v_singlePass_5873_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 2);
v_zeta_5874_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 3);
v_beta_5875_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 4);
v_eta_5876_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 5);
v_etaStruct_5877_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 6);
v_iota_5878_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 7);
v_proj_5879_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 8);
v_decide_5880_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 9);
v_arith_5881_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 10);
v_autoUnfold_5882_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 11);
v_dsimp_5883_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5884_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 13);
v_ground_5885_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5886_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 15);
v_zetaDelta_5887_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 16);
v_index_5888_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5889_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 18);
v_zetaUnused_5890_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 19);
v_catchRuntime_5891_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 20);
v_zetaHave_5892_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 21);
v_letToHave_5893_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 22);
v_congrConsts_5894_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5895_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 24);
v_warnExponents_5896_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 25);
v_suggestions_5897_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 26);
v_maxSuggestions_5898_ = lean_ctor_get(v_x_5868_, 2);
lean_inc(v_maxSuggestions_5898_);
v_locals_5899_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 27);
v_instances_5900_ = lean_ctor_get_uint8(v_x_5868_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5868_);
v___x_5901_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5902_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5903_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5904_ = l_Nat_reprFast(v_maxSteps_5869_);
v___x_5905_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5905_, 0, v___x_5904_);
v___x_5906_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5906_, 0, v___x_5903_);
lean_ctor_set(v___x_5906_, 1, v___x_5905_);
v___x_5907_ = 0;
v___x_5908_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5908_, 0, v___x_5906_);
lean_ctor_set_uint8(v___x_5908_, sizeof(void*)*1, v___x_5907_);
v___x_5909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5909_, 0, v___x_5902_);
lean_ctor_set(v___x_5909_, 1, v___x_5908_);
v___x_5910_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5911_, 0, v___x_5909_);
lean_ctor_set(v___x_5911_, 1, v___x_5910_);
v___x_5912_ = lean_box(1);
v___x_5913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5913_, 0, v___x_5911_);
lean_ctor_set(v___x_5913_, 1, v___x_5912_);
v___x_5914_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_5915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5915_, 0, v___x_5913_);
lean_ctor_set(v___x_5915_, 1, v___x_5914_);
v___x_5916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5916_, 0, v___x_5915_);
lean_ctor_set(v___x_5916_, 1, v___x_5901_);
v___x_5917_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_5918_ = l_Nat_reprFast(v_maxDischargeDepth_5870_);
v___x_5919_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5919_, 0, v___x_5918_);
v___x_5920_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5920_, 0, v___x_5917_);
lean_ctor_set(v___x_5920_, 1, v___x_5919_);
v___x_5921_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5921_, 0, v___x_5920_);
lean_ctor_set_uint8(v___x_5921_, sizeof(void*)*1, v___x_5907_);
v___x_5922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5922_, 0, v___x_5916_);
lean_ctor_set(v___x_5922_, 1, v___x_5921_);
v___x_5923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5922_);
lean_ctor_set(v___x_5923_, 1, v___x_5910_);
v___x_5924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5924_, 0, v___x_5923_);
lean_ctor_set(v___x_5924_, 1, v___x_5912_);
v___x_5925_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_5926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5926_, 0, v___x_5924_);
lean_ctor_set(v___x_5926_, 1, v___x_5925_);
v___x_5927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5927_, 0, v___x_5926_);
lean_ctor_set(v___x_5927_, 1, v___x_5901_);
v___x_5928_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5929_ = lean_unsigned_to_nat(0u);
v___x_5930_ = l_Bool_repr___redArg(v_contextual_5871_);
v___x_5931_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5931_, 0, v___x_5928_);
lean_ctor_set(v___x_5931_, 1, v___x_5930_);
v___x_5932_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5932_, 0, v___x_5931_);
lean_ctor_set_uint8(v___x_5932_, sizeof(void*)*1, v___x_5907_);
v___x_5933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5933_, 0, v___x_5927_);
lean_ctor_set(v___x_5933_, 1, v___x_5932_);
v___x_5934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5933_);
lean_ctor_set(v___x_5934_, 1, v___x_5910_);
v___x_5935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5935_, 0, v___x_5934_);
lean_ctor_set(v___x_5935_, 1, v___x_5912_);
v___x_5936_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_5937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5937_, 0, v___x_5935_);
lean_ctor_set(v___x_5937_, 1, v___x_5936_);
v___x_5938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5937_);
lean_ctor_set(v___x_5938_, 1, v___x_5901_);
v___x_5939_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_5940_ = l_Bool_repr___redArg(v_memoize_5872_);
v___x_5941_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5941_, 0, v___x_5939_);
lean_ctor_set(v___x_5941_, 1, v___x_5940_);
v___x_5942_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5942_, 0, v___x_5941_);
lean_ctor_set_uint8(v___x_5942_, sizeof(void*)*1, v___x_5907_);
v___x_5943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5943_, 0, v___x_5938_);
lean_ctor_set(v___x_5943_, 1, v___x_5942_);
v___x_5944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5943_);
lean_ctor_set(v___x_5944_, 1, v___x_5910_);
v___x_5945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5945_, 0, v___x_5944_);
lean_ctor_set(v___x_5945_, 1, v___x_5912_);
v___x_5946_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_5947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5947_, 0, v___x_5945_);
lean_ctor_set(v___x_5947_, 1, v___x_5946_);
v___x_5948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5948_, 0, v___x_5947_);
lean_ctor_set(v___x_5948_, 1, v___x_5901_);
v___x_5949_ = l_Bool_repr___redArg(v_singlePass_5873_);
v___x_5950_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5928_);
lean_ctor_set(v___x_5950_, 1, v___x_5949_);
v___x_5951_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5951_, 0, v___x_5950_);
lean_ctor_set_uint8(v___x_5951_, sizeof(void*)*1, v___x_5907_);
v___x_5952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5952_, 0, v___x_5948_);
lean_ctor_set(v___x_5952_, 1, v___x_5951_);
v___x_5953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5953_, 0, v___x_5952_);
lean_ctor_set(v___x_5953_, 1, v___x_5910_);
v___x_5954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5954_, 0, v___x_5953_);
lean_ctor_set(v___x_5954_, 1, v___x_5912_);
v___x_5955_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_5956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5956_, 0, v___x_5954_);
lean_ctor_set(v___x_5956_, 1, v___x_5955_);
v___x_5957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5956_);
lean_ctor_set(v___x_5957_, 1, v___x_5901_);
v___x_5958_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5959_ = l_Bool_repr___redArg(v_zeta_5874_);
v___x_5960_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5960_, 0, v___x_5958_);
lean_ctor_set(v___x_5960_, 1, v___x_5959_);
v___x_5961_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5961_, 0, v___x_5960_);
lean_ctor_set_uint8(v___x_5961_, sizeof(void*)*1, v___x_5907_);
v___x_5962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5962_, 0, v___x_5957_);
lean_ctor_set(v___x_5962_, 1, v___x_5961_);
v___x_5963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5963_, 0, v___x_5962_);
lean_ctor_set(v___x_5963_, 1, v___x_5910_);
v___x_5964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5964_, 0, v___x_5963_);
lean_ctor_set(v___x_5964_, 1, v___x_5912_);
v___x_5965_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5966_, 0, v___x_5964_);
lean_ctor_set(v___x_5966_, 1, v___x_5965_);
v___x_5967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5967_, 0, v___x_5966_);
lean_ctor_set(v___x_5967_, 1, v___x_5901_);
v___x_5968_ = l_Bool_repr___redArg(v_beta_5875_);
v___x_5969_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5958_);
lean_ctor_set(v___x_5969_, 1, v___x_5968_);
v___x_5970_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5970_, 0, v___x_5969_);
lean_ctor_set_uint8(v___x_5970_, sizeof(void*)*1, v___x_5907_);
v___x_5971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5971_, 0, v___x_5967_);
lean_ctor_set(v___x_5971_, 1, v___x_5970_);
v___x_5972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5971_);
lean_ctor_set(v___x_5972_, 1, v___x_5910_);
v___x_5973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5973_, 0, v___x_5972_);
lean_ctor_set(v___x_5973_, 1, v___x_5912_);
v___x_5974_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5973_);
lean_ctor_set(v___x_5975_, 1, v___x_5974_);
v___x_5976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5975_);
lean_ctor_set(v___x_5976_, 1, v___x_5901_);
v___x_5977_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5978_ = l_Bool_repr___redArg(v_eta_5876_);
v___x_5979_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5977_);
lean_ctor_set(v___x_5979_, 1, v___x_5978_);
v___x_5980_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5980_, 0, v___x_5979_);
lean_ctor_set_uint8(v___x_5980_, sizeof(void*)*1, v___x_5907_);
v___x_5981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5981_, 0, v___x_5976_);
lean_ctor_set(v___x_5981_, 1, v___x_5980_);
v___x_5982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5982_, 0, v___x_5981_);
lean_ctor_set(v___x_5982_, 1, v___x_5910_);
v___x_5983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5983_, 0, v___x_5982_);
lean_ctor_set(v___x_5983_, 1, v___x_5912_);
v___x_5984_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5985_, 0, v___x_5983_);
lean_ctor_set(v___x_5985_, 1, v___x_5984_);
v___x_5986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5986_, 0, v___x_5985_);
lean_ctor_set(v___x_5986_, 1, v___x_5901_);
v___x_5987_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5988_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5877_, v___x_5929_);
v___x_5989_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5989_, 0, v___x_5987_);
lean_ctor_set(v___x_5989_, 1, v___x_5988_);
v___x_5990_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5990_, 0, v___x_5989_);
lean_ctor_set_uint8(v___x_5990_, sizeof(void*)*1, v___x_5907_);
v___x_5991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5986_);
lean_ctor_set(v___x_5991_, 1, v___x_5990_);
v___x_5992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5992_, 0, v___x_5991_);
lean_ctor_set(v___x_5992_, 1, v___x_5910_);
v___x_5993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5992_);
lean_ctor_set(v___x_5993_, 1, v___x_5912_);
v___x_5994_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5995_, 0, v___x_5993_);
lean_ctor_set(v___x_5995_, 1, v___x_5994_);
v___x_5996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5995_);
lean_ctor_set(v___x_5996_, 1, v___x_5901_);
v___x_5997_ = l_Bool_repr___redArg(v_iota_5878_);
v___x_5998_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5998_, 0, v___x_5958_);
lean_ctor_set(v___x_5998_, 1, v___x_5997_);
v___x_5999_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5999_, 0, v___x_5998_);
lean_ctor_set_uint8(v___x_5999_, sizeof(void*)*1, v___x_5907_);
v___x_6000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6000_, 0, v___x_5996_);
lean_ctor_set(v___x_6000_, 1, v___x_5999_);
v___x_6001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6001_, 0, v___x_6000_);
lean_ctor_set(v___x_6001_, 1, v___x_5910_);
v___x_6002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6002_, 0, v___x_6001_);
lean_ctor_set(v___x_6002_, 1, v___x_5912_);
v___x_6003_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_6004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6004_, 0, v___x_6002_);
lean_ctor_set(v___x_6004_, 1, v___x_6003_);
v___x_6005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6005_, 0, v___x_6004_);
lean_ctor_set(v___x_6005_, 1, v___x_5901_);
v___x_6006_ = l_Bool_repr___redArg(v_proj_5879_);
v___x_6007_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6007_, 0, v___x_5958_);
lean_ctor_set(v___x_6007_, 1, v___x_6006_);
v___x_6008_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6008_, 0, v___x_6007_);
lean_ctor_set_uint8(v___x_6008_, sizeof(void*)*1, v___x_5907_);
v___x_6009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6009_, 0, v___x_6005_);
lean_ctor_set(v___x_6009_, 1, v___x_6008_);
v___x_6010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6010_, 0, v___x_6009_);
lean_ctor_set(v___x_6010_, 1, v___x_5910_);
v___x_6011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6011_, 0, v___x_6010_);
lean_ctor_set(v___x_6011_, 1, v___x_5912_);
v___x_6012_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_6013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6011_);
lean_ctor_set(v___x_6013_, 1, v___x_6012_);
v___x_6014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6013_);
lean_ctor_set(v___x_6014_, 1, v___x_5901_);
v___x_6015_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_6016_ = l_Bool_repr___redArg(v_decide_5880_);
v___x_6017_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6017_, 0, v___x_6015_);
lean_ctor_set(v___x_6017_, 1, v___x_6016_);
v___x_6018_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6018_, 0, v___x_6017_);
lean_ctor_set_uint8(v___x_6018_, sizeof(void*)*1, v___x_5907_);
v___x_6019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6019_, 0, v___x_6014_);
lean_ctor_set(v___x_6019_, 1, v___x_6018_);
v___x_6020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6019_);
lean_ctor_set(v___x_6020_, 1, v___x_5910_);
v___x_6021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6021_, 0, v___x_6020_);
lean_ctor_set(v___x_6021_, 1, v___x_5912_);
v___x_6022_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_6023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6021_);
lean_ctor_set(v___x_6023_, 1, v___x_6022_);
v___x_6024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6024_, 0, v___x_6023_);
lean_ctor_set(v___x_6024_, 1, v___x_5901_);
v___x_6025_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_6026_ = l_Bool_repr___redArg(v_arith_5881_);
v___x_6027_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6025_);
lean_ctor_set(v___x_6027_, 1, v___x_6026_);
v___x_6028_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6028_, 0, v___x_6027_);
lean_ctor_set_uint8(v___x_6028_, sizeof(void*)*1, v___x_5907_);
v___x_6029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6029_, 0, v___x_6024_);
lean_ctor_set(v___x_6029_, 1, v___x_6028_);
v___x_6030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6030_, 0, v___x_6029_);
lean_ctor_set(v___x_6030_, 1, v___x_5910_);
v___x_6031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6030_);
lean_ctor_set(v___x_6031_, 1, v___x_5912_);
v___x_6032_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_6033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6033_, 0, v___x_6031_);
lean_ctor_set(v___x_6033_, 1, v___x_6032_);
v___x_6034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6033_);
lean_ctor_set(v___x_6034_, 1, v___x_5901_);
v___x_6035_ = l_Bool_repr___redArg(v_autoUnfold_5882_);
v___x_6036_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6036_, 0, v___x_5928_);
lean_ctor_set(v___x_6036_, 1, v___x_6035_);
v___x_6037_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6037_, 0, v___x_6036_);
lean_ctor_set_uint8(v___x_6037_, sizeof(void*)*1, v___x_5907_);
v___x_6038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6038_, 0, v___x_6034_);
lean_ctor_set(v___x_6038_, 1, v___x_6037_);
v___x_6039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6039_, 0, v___x_6038_);
lean_ctor_set(v___x_6039_, 1, v___x_5910_);
v___x_6040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6039_);
lean_ctor_set(v___x_6040_, 1, v___x_5912_);
v___x_6041_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_6042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6042_, 0, v___x_6040_);
lean_ctor_set(v___x_6042_, 1, v___x_6041_);
v___x_6043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6043_, 0, v___x_6042_);
lean_ctor_set(v___x_6043_, 1, v___x_5901_);
v___x_6044_ = l_Bool_repr___redArg(v_dsimp_5883_);
v___x_6045_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6045_, 0, v___x_6025_);
lean_ctor_set(v___x_6045_, 1, v___x_6044_);
v___x_6046_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6046_, 0, v___x_6045_);
lean_ctor_set_uint8(v___x_6046_, sizeof(void*)*1, v___x_5907_);
v___x_6047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6047_, 0, v___x_6043_);
lean_ctor_set(v___x_6047_, 1, v___x_6046_);
v___x_6048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6048_, 0, v___x_6047_);
lean_ctor_set(v___x_6048_, 1, v___x_5910_);
v___x_6049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6049_, 0, v___x_6048_);
lean_ctor_set(v___x_6049_, 1, v___x_5912_);
v___x_6050_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_6051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6051_, 0, v___x_6049_);
lean_ctor_set(v___x_6051_, 1, v___x_6050_);
v___x_6052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6052_, 0, v___x_6051_);
lean_ctor_set(v___x_6052_, 1, v___x_5901_);
v___x_6053_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_6054_ = l_Bool_repr___redArg(v_failIfUnchanged_5884_);
v___x_6055_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6055_, 0, v___x_6053_);
lean_ctor_set(v___x_6055_, 1, v___x_6054_);
v___x_6056_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6056_, 0, v___x_6055_);
lean_ctor_set_uint8(v___x_6056_, sizeof(void*)*1, v___x_5907_);
v___x_6057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6057_, 0, v___x_6052_);
lean_ctor_set(v___x_6057_, 1, v___x_6056_);
v___x_6058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6058_, 0, v___x_6057_);
lean_ctor_set(v___x_6058_, 1, v___x_5910_);
v___x_6059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6059_, 0, v___x_6058_);
lean_ctor_set(v___x_6059_, 1, v___x_5912_);
v___x_6060_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_6061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6059_);
lean_ctor_set(v___x_6061_, 1, v___x_6060_);
v___x_6062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6062_, 0, v___x_6061_);
lean_ctor_set(v___x_6062_, 1, v___x_5901_);
v___x_6063_ = l_Bool_repr___redArg(v_ground_5885_);
v___x_6064_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6064_, 0, v___x_6015_);
lean_ctor_set(v___x_6064_, 1, v___x_6063_);
v___x_6065_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6065_, 0, v___x_6064_);
lean_ctor_set_uint8(v___x_6065_, sizeof(void*)*1, v___x_5907_);
v___x_6066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6062_);
lean_ctor_set(v___x_6066_, 1, v___x_6065_);
v___x_6067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6067_, 0, v___x_6066_);
lean_ctor_set(v___x_6067_, 1, v___x_5910_);
v___x_6068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6068_, 0, v___x_6067_);
lean_ctor_set(v___x_6068_, 1, v___x_5912_);
v___x_6069_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_6070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6068_);
lean_ctor_set(v___x_6070_, 1, v___x_6069_);
v___x_6071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6070_);
lean_ctor_set(v___x_6071_, 1, v___x_5901_);
v___x_6072_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_6073_ = l_Bool_repr___redArg(v_unfoldPartialApp_5886_);
v___x_6074_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6074_, 0, v___x_6072_);
lean_ctor_set(v___x_6074_, 1, v___x_6073_);
v___x_6075_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6075_, 0, v___x_6074_);
lean_ctor_set_uint8(v___x_6075_, sizeof(void*)*1, v___x_5907_);
v___x_6076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6076_, 0, v___x_6071_);
lean_ctor_set(v___x_6076_, 1, v___x_6075_);
v___x_6077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6077_, 0, v___x_6076_);
lean_ctor_set(v___x_6077_, 1, v___x_5910_);
v___x_6078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6077_);
lean_ctor_set(v___x_6078_, 1, v___x_5912_);
v___x_6079_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6080_, 0, v___x_6078_);
lean_ctor_set(v___x_6080_, 1, v___x_6079_);
v___x_6081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6081_, 0, v___x_6080_);
lean_ctor_set(v___x_6081_, 1, v___x_5901_);
v___x_6082_ = l_Bool_repr___redArg(v_zetaDelta_5887_);
v___x_6083_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6083_, 0, v___x_5987_);
lean_ctor_set(v___x_6083_, 1, v___x_6082_);
v___x_6084_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6084_, 0, v___x_6083_);
lean_ctor_set_uint8(v___x_6084_, sizeof(void*)*1, v___x_5907_);
v___x_6085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6085_, 0, v___x_6081_);
lean_ctor_set(v___x_6085_, 1, v___x_6084_);
v___x_6086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6085_);
lean_ctor_set(v___x_6086_, 1, v___x_5910_);
v___x_6087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6087_, 0, v___x_6086_);
lean_ctor_set(v___x_6087_, 1, v___x_5912_);
v___x_6088_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6087_);
lean_ctor_set(v___x_6089_, 1, v___x_6088_);
v___x_6090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6090_, 0, v___x_6089_);
lean_ctor_set(v___x_6090_, 1, v___x_5901_);
v___x_6091_ = l_Bool_repr___redArg(v_index_5888_);
v___x_6092_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6092_, 0, v___x_6025_);
lean_ctor_set(v___x_6092_, 1, v___x_6091_);
v___x_6093_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6093_, 0, v___x_6092_);
lean_ctor_set_uint8(v___x_6093_, sizeof(void*)*1, v___x_5907_);
v___x_6094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___x_6090_);
lean_ctor_set(v___x_6094_, 1, v___x_6093_);
v___x_6095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6094_);
lean_ctor_set(v___x_6095_, 1, v___x_5910_);
v___x_6096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6095_);
lean_ctor_set(v___x_6096_, 1, v___x_5912_);
v___x_6097_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6096_);
lean_ctor_set(v___x_6098_, 1, v___x_6097_);
v___x_6099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6099_, 0, v___x_6098_);
lean_ctor_set(v___x_6099_, 1, v___x_5901_);
v___x_6100_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6101_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5889_);
v___x_6102_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6100_);
lean_ctor_set(v___x_6102_, 1, v___x_6101_);
v___x_6103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6103_, 0, v___x_6102_);
lean_ctor_set_uint8(v___x_6103_, sizeof(void*)*1, v___x_5907_);
v___x_6104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6099_);
lean_ctor_set(v___x_6104_, 1, v___x_6103_);
v___x_6105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6105_, 0, v___x_6104_);
lean_ctor_set(v___x_6105_, 1, v___x_5910_);
v___x_6106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6106_, 0, v___x_6105_);
lean_ctor_set(v___x_6106_, 1, v___x_5912_);
v___x_6107_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6108_, 0, v___x_6106_);
lean_ctor_set(v___x_6108_, 1, v___x_6107_);
v___x_6109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6109_, 0, v___x_6108_);
lean_ctor_set(v___x_6109_, 1, v___x_5901_);
v___x_6110_ = l_Bool_repr___redArg(v_zetaUnused_5890_);
v___x_6111_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6111_, 0, v___x_5928_);
lean_ctor_set(v___x_6111_, 1, v___x_6110_);
v___x_6112_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6112_, 0, v___x_6111_);
lean_ctor_set_uint8(v___x_6112_, sizeof(void*)*1, v___x_5907_);
v___x_6113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6109_);
lean_ctor_set(v___x_6113_, 1, v___x_6112_);
v___x_6114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6114_, 0, v___x_6113_);
lean_ctor_set(v___x_6114_, 1, v___x_5910_);
v___x_6115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6114_);
lean_ctor_set(v___x_6115_, 1, v___x_5912_);
v___x_6116_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6115_);
lean_ctor_set(v___x_6117_, 1, v___x_6116_);
v___x_6118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6117_);
lean_ctor_set(v___x_6118_, 1, v___x_5901_);
v___x_6119_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6120_ = l_Bool_repr___redArg(v_catchRuntime_5891_);
v___x_6121_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6121_, 0, v___x_6119_);
lean_ctor_set(v___x_6121_, 1, v___x_6120_);
v___x_6122_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6122_, 0, v___x_6121_);
lean_ctor_set_uint8(v___x_6122_, sizeof(void*)*1, v___x_5907_);
v___x_6123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6123_, 0, v___x_6118_);
lean_ctor_set(v___x_6123_, 1, v___x_6122_);
v___x_6124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6124_, 0, v___x_6123_);
lean_ctor_set(v___x_6124_, 1, v___x_5910_);
v___x_6125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6125_, 0, v___x_6124_);
lean_ctor_set(v___x_6125_, 1, v___x_5912_);
v___x_6126_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6127_, 0, v___x_6125_);
lean_ctor_set(v___x_6127_, 1, v___x_6126_);
v___x_6128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6128_, 0, v___x_6127_);
lean_ctor_set(v___x_6128_, 1, v___x_5901_);
v___x_6129_ = l_Bool_repr___redArg(v_zetaHave_5892_);
v___x_6130_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6130_, 0, v___x_5903_);
lean_ctor_set(v___x_6130_, 1, v___x_6129_);
v___x_6131_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6131_, 0, v___x_6130_);
lean_ctor_set_uint8(v___x_6131_, sizeof(void*)*1, v___x_5907_);
v___x_6132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6128_);
lean_ctor_set(v___x_6132_, 1, v___x_6131_);
v___x_6133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6132_);
lean_ctor_set(v___x_6133_, 1, v___x_5910_);
v___x_6134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6134_, 0, v___x_6133_);
lean_ctor_set(v___x_6134_, 1, v___x_5912_);
v___x_6135_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6136_, 0, v___x_6134_);
lean_ctor_set(v___x_6136_, 1, v___x_6135_);
v___x_6137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6137_, 0, v___x_6136_);
lean_ctor_set(v___x_6137_, 1, v___x_5901_);
v___x_6138_ = l_Bool_repr___redArg(v_letToHave_5893_);
v___x_6139_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6139_, 0, v___x_5987_);
lean_ctor_set(v___x_6139_, 1, v___x_6138_);
v___x_6140_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6140_, 0, v___x_6139_);
lean_ctor_set_uint8(v___x_6140_, sizeof(void*)*1, v___x_5907_);
v___x_6141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6141_, 0, v___x_6137_);
lean_ctor_set(v___x_6141_, 1, v___x_6140_);
v___x_6142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6142_, 0, v___x_6141_);
lean_ctor_set(v___x_6142_, 1, v___x_5910_);
v___x_6143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6143_, 0, v___x_6142_);
lean_ctor_set(v___x_6143_, 1, v___x_5912_);
v___x_6144_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6145_, 0, v___x_6143_);
lean_ctor_set(v___x_6145_, 1, v___x_6144_);
v___x_6146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6146_, 0, v___x_6145_);
lean_ctor_set(v___x_6146_, 1, v___x_5901_);
v___x_6147_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6148_ = l_Bool_repr___redArg(v_congrConsts_5894_);
v___x_6149_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6149_, 0, v___x_6147_);
lean_ctor_set(v___x_6149_, 1, v___x_6148_);
v___x_6150_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6150_, 0, v___x_6149_);
lean_ctor_set_uint8(v___x_6150_, sizeof(void*)*1, v___x_5907_);
v___x_6151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6151_, 0, v___x_6146_);
lean_ctor_set(v___x_6151_, 1, v___x_6150_);
v___x_6152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6152_, 0, v___x_6151_);
lean_ctor_set(v___x_6152_, 1, v___x_5910_);
v___x_6153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6153_, 0, v___x_6152_);
lean_ctor_set(v___x_6153_, 1, v___x_5912_);
v___x_6154_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6155_, 0, v___x_6153_);
lean_ctor_set(v___x_6155_, 1, v___x_6154_);
v___x_6156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6156_, 0, v___x_6155_);
lean_ctor_set(v___x_6156_, 1, v___x_5901_);
v___x_6157_ = l_Bool_repr___redArg(v_bitVecOfNat_5895_);
v___x_6158_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6158_, 0, v___x_6147_);
lean_ctor_set(v___x_6158_, 1, v___x_6157_);
v___x_6159_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6159_, 0, v___x_6158_);
lean_ctor_set_uint8(v___x_6159_, sizeof(void*)*1, v___x_5907_);
v___x_6160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6160_, 0, v___x_6156_);
lean_ctor_set(v___x_6160_, 1, v___x_6159_);
v___x_6161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6161_, 0, v___x_6160_);
lean_ctor_set(v___x_6161_, 1, v___x_5910_);
v___x_6162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6162_, 0, v___x_6161_);
lean_ctor_set(v___x_6162_, 1, v___x_5912_);
v___x_6163_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6164_, 0, v___x_6162_);
lean_ctor_set(v___x_6164_, 1, v___x_6163_);
v___x_6165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6165_, 0, v___x_6164_);
lean_ctor_set(v___x_6165_, 1, v___x_5901_);
v___x_6166_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6167_ = l_Bool_repr___redArg(v_warnExponents_5896_);
v___x_6168_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6168_, 0, v___x_6166_);
lean_ctor_set(v___x_6168_, 1, v___x_6167_);
v___x_6169_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6169_, 0, v___x_6168_);
lean_ctor_set_uint8(v___x_6169_, sizeof(void*)*1, v___x_5907_);
v___x_6170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6170_, 0, v___x_6165_);
lean_ctor_set(v___x_6170_, 1, v___x_6169_);
v___x_6171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6171_, 0, v___x_6170_);
lean_ctor_set(v___x_6171_, 1, v___x_5910_);
v___x_6172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6172_, 0, v___x_6171_);
lean_ctor_set(v___x_6172_, 1, v___x_5912_);
v___x_6173_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6174_, 0, v___x_6172_);
lean_ctor_set(v___x_6174_, 1, v___x_6173_);
v___x_6175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6175_, 0, v___x_6174_);
lean_ctor_set(v___x_6175_, 1, v___x_5901_);
v___x_6176_ = l_Bool_repr___redArg(v_suggestions_5897_);
v___x_6177_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6177_, 0, v___x_6147_);
lean_ctor_set(v___x_6177_, 1, v___x_6176_);
v___x_6178_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6178_, 0, v___x_6177_);
lean_ctor_set_uint8(v___x_6178_, sizeof(void*)*1, v___x_5907_);
v___x_6179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6175_);
lean_ctor_set(v___x_6179_, 1, v___x_6178_);
v___x_6180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6180_, 0, v___x_6179_);
lean_ctor_set(v___x_6180_, 1, v___x_5910_);
v___x_6181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6181_, 0, v___x_6180_);
lean_ctor_set(v___x_6181_, 1, v___x_5912_);
v___x_6182_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6183_, 0, v___x_6181_);
lean_ctor_set(v___x_6183_, 1, v___x_6182_);
v___x_6184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6184_, 0, v___x_6183_);
lean_ctor_set(v___x_6184_, 1, v___x_5901_);
v___x_6185_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6186_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5898_, v___x_5929_);
v___x_6187_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6187_, 0, v___x_6185_);
lean_ctor_set(v___x_6187_, 1, v___x_6186_);
v___x_6188_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6188_, 0, v___x_6187_);
lean_ctor_set_uint8(v___x_6188_, sizeof(void*)*1, v___x_5907_);
v___x_6189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6189_, 0, v___x_6184_);
lean_ctor_set(v___x_6189_, 1, v___x_6188_);
v___x_6190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6190_, 0, v___x_6189_);
lean_ctor_set(v___x_6190_, 1, v___x_5910_);
v___x_6191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6191_, 0, v___x_6190_);
lean_ctor_set(v___x_6191_, 1, v___x_5912_);
v___x_6192_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6193_, 0, v___x_6191_);
lean_ctor_set(v___x_6193_, 1, v___x_6192_);
v___x_6194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6194_, 0, v___x_6193_);
lean_ctor_set(v___x_6194_, 1, v___x_5901_);
v___x_6195_ = l_Bool_repr___redArg(v_locals_5899_);
v___x_6196_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6196_, 0, v___x_6015_);
lean_ctor_set(v___x_6196_, 1, v___x_6195_);
v___x_6197_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6197_, 0, v___x_6196_);
lean_ctor_set_uint8(v___x_6197_, sizeof(void*)*1, v___x_5907_);
v___x_6198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6198_, 0, v___x_6194_);
lean_ctor_set(v___x_6198_, 1, v___x_6197_);
v___x_6199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6199_, 0, v___x_6198_);
lean_ctor_set(v___x_6199_, 1, v___x_5910_);
v___x_6200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6200_, 0, v___x_6199_);
lean_ctor_set(v___x_6200_, 1, v___x_5912_);
v___x_6201_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6202_, 0, v___x_6200_);
lean_ctor_set(v___x_6202_, 1, v___x_6201_);
v___x_6203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6203_, 0, v___x_6202_);
lean_ctor_set(v___x_6203_, 1, v___x_5901_);
v___x_6204_ = l_Bool_repr___redArg(v_instances_5900_);
v___x_6205_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6205_, 0, v___x_5987_);
lean_ctor_set(v___x_6205_, 1, v___x_6204_);
v___x_6206_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6206_, 0, v___x_6205_);
lean_ctor_set_uint8(v___x_6206_, sizeof(void*)*1, v___x_5907_);
v___x_6207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6207_, 0, v___x_6203_);
lean_ctor_set(v___x_6207_, 1, v___x_6206_);
v___x_6208_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6209_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6210_, 0, v___x_6209_);
lean_ctor_set(v___x_6210_, 1, v___x_6207_);
v___x_6211_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6212_, 0, v___x_6210_);
lean_ctor_set(v___x_6212_, 1, v___x_6211_);
v___x_6213_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6213_, 0, v___x_6208_);
lean_ctor_set(v___x_6213_, 1, v___x_6212_);
v___x_6214_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6214_, 0, v___x_6213_);
lean_ctor_set_uint8(v___x_6214_, sizeof(void*)*1, v___x_5907_);
return v___x_6214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6215_, lean_object* v_prec_6216_){
_start:
{
lean_object* v___x_6217_; 
v___x_6217_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6215_);
return v___x_6217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6218_, lean_object* v_prec_6219_){
_start:
{
lean_object* v_res_6220_; 
v_res_6220_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6218_, v_prec_6219_);
lean_dec(v_prec_6219_);
return v_res_6220_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6223_, lean_object* v_x_6224_){
_start:
{
if (lean_obj_tag(v_x_6224_) == 0)
{
uint8_t v___x_6225_; 
v___x_6225_ = 0;
return v___x_6225_;
}
else
{
lean_object* v_head_6226_; lean_object* v_tail_6227_; uint8_t v___x_6228_; 
v_head_6226_ = lean_ctor_get(v_x_6224_, 0);
v_tail_6227_ = lean_ctor_get(v_x_6224_, 1);
v___x_6228_ = lean_nat_dec_eq(v_a_6223_, v_head_6226_);
if (v___x_6228_ == 0)
{
v_x_6224_ = v_tail_6227_;
goto _start;
}
else
{
return v___x_6228_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6230_, lean_object* v_x_6231_){
_start:
{
uint8_t v_res_6232_; lean_object* v_r_6233_; 
v_res_6232_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6230_, v_x_6231_);
lean_dec(v_x_6231_);
lean_dec(v_a_6230_);
v_r_6233_ = lean_box(v_res_6232_);
return v_r_6233_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6234_, lean_object* v_x_6235_){
_start:
{
switch(lean_obj_tag(v_x_6234_))
{
case 0:
{
uint8_t v___x_6236_; 
v___x_6236_ = 1;
return v___x_6236_;
}
case 1:
{
lean_object* v_idxs_6237_; uint8_t v___x_6238_; 
v_idxs_6237_ = lean_ctor_get(v_x_6234_, 0);
v___x_6238_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6235_, v_idxs_6237_);
return v___x_6238_;
}
default: 
{
lean_object* v_idxs_6239_; uint8_t v___x_6240_; 
v_idxs_6239_ = lean_ctor_get(v_x_6234_, 0);
v___x_6240_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6235_, v_idxs_6239_);
if (v___x_6240_ == 0)
{
uint8_t v___x_6241_; 
v___x_6241_ = 1;
return v___x_6241_;
}
else
{
uint8_t v___x_6242_; 
v___x_6242_ = 0;
return v___x_6242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6243_, lean_object* v_x_6244_){
_start:
{
uint8_t v_res_6245_; lean_object* v_r_6246_; 
v_res_6245_ = l_Lean_Meta_Occurrences_contains(v_x_6243_, v_x_6244_);
lean_dec(v_x_6244_);
lean_dec(v_x_6243_);
v_r_6246_ = lean_box(v_res_6245_);
return v_r_6246_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6247_){
_start:
{
if (lean_obj_tag(v_x_6247_) == 0)
{
uint8_t v___x_6248_; 
v___x_6248_ = 1;
return v___x_6248_;
}
else
{
uint8_t v___x_6249_; 
v___x_6249_ = 0;
return v___x_6249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6250_){
_start:
{
uint8_t v_res_6251_; lean_object* v_r_6252_; 
v_res_6251_ = l_Lean_Meta_Occurrences_isAll(v_x_6250_);
lean_dec(v_x_6250_);
v_r_6252_ = lean_box(v_res_6251_);
return v_r_6252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___impl(uint8_t v_x_6253_){
_start:
{
lean_object* v___x_6254_; lean_object* v___x_6255_; 
v___x_6254_ = lean_box(v_x_6253_);
v___x_6255_ = lean_obj_tag_nat(v___x_6254_);
lean_dec(v___x_6254_);
return v___x_6255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___impl___boxed(lean_object* v_x_6256_){
_start:
{
uint8_t v_x_4__boxed_6257_; lean_object* v_res_6258_; 
v_x_4__boxed_6257_ = lean_unbox(v_x_6256_);
v_res_6258_ = l_Lean_Meta_ApplyNewGoals_ctorIdx___impl(v_x_4__boxed_6257_);
return v_res_6258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6259_){
_start:
{
lean_inc(v_k_6259_);
return v_k_6259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6260_){
_start:
{
lean_object* v_res_6261_; 
v_res_6261_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6260_);
lean_dec(v_k_6260_);
return v_res_6261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6262_, lean_object* v_ctorIdx_6263_, uint8_t v_t_6264_, lean_object* v_h_6265_, lean_object* v_k_6266_){
_start:
{
lean_inc(v_k_6266_);
return v_k_6266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6267_, lean_object* v_ctorIdx_6268_, lean_object* v_t_6269_, lean_object* v_h_6270_, lean_object* v_k_6271_){
_start:
{
uint8_t v_t_boxed_6272_; lean_object* v_res_6273_; 
v_t_boxed_6272_ = lean_unbox(v_t_6269_);
v_res_6273_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6267_, v_ctorIdx_6268_, v_t_boxed_6272_, v_h_6270_, v_k_6271_);
lean_dec(v_k_6271_);
lean_dec(v_ctorIdx_6268_);
return v_res_6273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6274_){
_start:
{
lean_inc(v_nonDependentFirst_6274_);
return v_nonDependentFirst_6274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6275_){
_start:
{
lean_object* v_res_6276_; 
v_res_6276_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6275_);
lean_dec(v_nonDependentFirst_6275_);
return v_res_6276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6277_, uint8_t v_t_6278_, lean_object* v_h_6279_, lean_object* v_nonDependentFirst_6280_){
_start:
{
lean_inc(v_nonDependentFirst_6280_);
return v_nonDependentFirst_6280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6281_, lean_object* v_t_6282_, lean_object* v_h_6283_, lean_object* v_nonDependentFirst_6284_){
_start:
{
uint8_t v_t_boxed_6285_; lean_object* v_res_6286_; 
v_t_boxed_6285_ = lean_unbox(v_t_6282_);
v_res_6286_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6281_, v_t_boxed_6285_, v_h_6283_, v_nonDependentFirst_6284_);
lean_dec(v_nonDependentFirst_6284_);
return v_res_6286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6287_){
_start:
{
lean_inc(v_nonDependentOnly_6287_);
return v_nonDependentOnly_6287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6288_){
_start:
{
lean_object* v_res_6289_; 
v_res_6289_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6288_);
lean_dec(v_nonDependentOnly_6288_);
return v_res_6289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6290_, uint8_t v_t_6291_, lean_object* v_h_6292_, lean_object* v_nonDependentOnly_6293_){
_start:
{
lean_inc(v_nonDependentOnly_6293_);
return v_nonDependentOnly_6293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6294_, lean_object* v_t_6295_, lean_object* v_h_6296_, lean_object* v_nonDependentOnly_6297_){
_start:
{
uint8_t v_t_boxed_6298_; lean_object* v_res_6299_; 
v_t_boxed_6298_ = lean_unbox(v_t_6295_);
v_res_6299_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6294_, v_t_boxed_6298_, v_h_6296_, v_nonDependentOnly_6297_);
lean_dec(v_nonDependentOnly_6297_);
return v_res_6299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6300_){
_start:
{
lean_inc(v_all_6300_);
return v_all_6300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6301_){
_start:
{
lean_object* v_res_6302_; 
v_res_6302_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6301_);
lean_dec(v_all_6301_);
return v_res_6302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6303_, uint8_t v_t_6304_, lean_object* v_h_6305_, lean_object* v_all_6306_){
_start:
{
lean_inc(v_all_6306_);
return v_all_6306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6307_, lean_object* v_t_6308_, lean_object* v_h_6309_, lean_object* v_all_6310_){
_start:
{
uint8_t v_t_boxed_6311_; lean_object* v_res_6312_; 
v_t_boxed_6311_ = lean_unbox(v_t_6308_);
v_res_6312_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6307_, v_t_boxed_6311_, v_h_6309_, v_all_6310_);
lean_dec(v_all_6310_);
return v_res_6312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6326_){
_start:
{
lean_object* v___x_6327_; uint8_t v___x_6328_; 
v___x_6327_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6326_);
v___x_6328_ = l_Lean_Syntax_isOfKind(v_c_6326_, v___x_6327_);
if (v___x_6328_ == 0)
{
lean_object* v___x_6329_; uint8_t v___x_6330_; 
v___x_6329_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6326_);
v___x_6330_ = l_Lean_Syntax_isOfKind(v_c_6326_, v___x_6329_);
if (v___x_6330_ == 0)
{
lean_object* v___x_6331_; uint8_t v___x_6332_; 
v___x_6331_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6326_);
v___x_6332_ = l_Lean_Syntax_isOfKind(v_c_6326_, v___x_6331_);
if (v___x_6332_ == 0)
{
lean_object* v___x_6333_; 
lean_dec(v_c_6326_);
v___x_6333_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6333_;
}
else
{
lean_object* v___x_6334_; lean_object* v___x_6335_; lean_object* v___x_6336_; 
v___x_6334_ = lean_unsigned_to_nat(1u);
v___x_6335_ = lean_mk_empty_array_with_capacity(v___x_6334_);
v___x_6336_ = lean_array_push(v___x_6335_, v_c_6326_);
return v___x_6336_;
}
}
else
{
lean_object* v___x_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; 
v___x_6337_ = lean_unsigned_to_nat(0u);
v___x_6338_ = l_Lean_Syntax_getArg(v_c_6326_, v___x_6337_);
lean_dec(v_c_6326_);
v___x_6339_ = l_Lean_Syntax_getArgs(v___x_6338_);
lean_dec(v___x_6338_);
return v___x_6339_;
}
}
else
{
lean_object* v___x_6340_; lean_object* v___x_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; uint8_t v___x_6344_; 
v___x_6340_ = l_Lean_Syntax_getArgs(v_c_6326_);
lean_dec(v_c_6326_);
v___x_6341_ = lean_unsigned_to_nat(0u);
v___x_6342_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6343_ = lean_array_get_size(v___x_6340_);
v___x_6344_ = lean_nat_dec_lt(v___x_6341_, v___x_6343_);
if (v___x_6344_ == 0)
{
lean_dec_ref(v___x_6340_);
return v___x_6342_;
}
else
{
size_t v___x_6345_; size_t v___x_6346_; lean_object* v___x_6347_; 
v___x_6345_ = ((size_t)0ULL);
v___x_6346_ = lean_usize_of_nat(v___x_6343_);
v___x_6347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6340_, v___x_6345_, v___x_6346_, v___x_6342_);
lean_dec_ref(v___x_6340_);
return v___x_6347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6348_, size_t v_i_6349_, size_t v_stop_6350_, lean_object* v_b_6351_){
_start:
{
uint8_t v___x_6352_; 
v___x_6352_ = lean_usize_dec_eq(v_i_6349_, v_stop_6350_);
if (v___x_6352_ == 0)
{
lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; size_t v___x_6356_; size_t v___x_6357_; 
v___x_6353_ = lean_array_uget_borrowed(v_as_6348_, v_i_6349_);
lean_inc(v___x_6353_);
v___x_6354_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6353_);
v___x_6355_ = l_Array_append___redArg(v_b_6351_, v___x_6354_);
lean_dec_ref(v___x_6354_);
v___x_6356_ = ((size_t)1ULL);
v___x_6357_ = lean_usize_add(v_i_6349_, v___x_6356_);
v_i_6349_ = v___x_6357_;
v_b_6351_ = v___x_6355_;
goto _start;
}
else
{
return v_b_6351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6359_, lean_object* v_i_6360_, lean_object* v_stop_6361_, lean_object* v_b_6362_){
_start:
{
size_t v_i_boxed_6363_; size_t v_stop_boxed_6364_; lean_object* v_res_6365_; 
v_i_boxed_6363_ = lean_unbox_usize(v_i_6360_);
lean_dec(v_i_6360_);
v_stop_boxed_6364_ = lean_unbox_usize(v_stop_6361_);
lean_dec(v_stop_6361_);
v_res_6365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6359_, v_i_boxed_6363_, v_stop_boxed_6364_, v_b_6362_);
lean_dec_ref(v_as_6359_);
return v_res_6365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6366_){
_start:
{
lean_object* v___x_6367_; lean_object* v___x_6368_; lean_object* v___x_6369_; lean_object* v___x_6370_; lean_object* v___x_6371_; 
v___x_6367_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6368_ = lean_box(2);
v___x_6369_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6370_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6370_, 0, v___x_6368_);
lean_ctor_set(v___x_6370_, 1, v___x_6369_);
lean_ctor_set(v___x_6370_, 2, v_items_6366_);
v___x_6371_ = l_Lean_Syntax_node1(v___x_6368_, v___x_6367_, v___x_6370_);
return v___x_6371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6372_, lean_object* v_cfg_x27_6373_){
_start:
{
lean_object* v___x_6374_; lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v___x_6377_; 
v___x_6374_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6372_);
v___x_6375_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6373_);
v___x_6376_ = l_Array_append___redArg(v___x_6374_, v___x_6375_);
lean_dec_ref(v___x_6375_);
v___x_6377_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6376_);
return v___x_6377_;
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
